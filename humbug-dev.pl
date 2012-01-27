#!/usr/bin/perl -w
#
# boogie.pl -- track, view and change Bugzilla bugs in irssi [[[
#
# This plugin lets you view, change and comment on bugs in irssi
# using IRC-like commands.  You can have several bugs open possibly
# from different Bugzillas, and you can monitor multiple channels
# for bug references, which may come handy in bug-squash parties.
#
# To use boogie normally you want to define one ormore servers
# (see the SERVER command), associate windows with Bugzillas
# (see CONNECT) and OPEN bugs to see and change it, or SNIFF
# channels for bug references.
#
# Command keywords are case insensitive.  Not all commands are
# applicable in every kind of windows.  There are thee kind of
# windows:
# -- status:  usually the first window in irssi
# -- chatwin: a channel or an IRC query, which you can sniff for bugs
# -- bugwin:  a bug's window, where it's shown and can be changed
#
#Commands available everywhere:
# /BUG HELP [<topic>]
#	Gives you information about <topic>.
# /BUG RESTART [<script>]
#	Restart boogie but try to keep its state.
#	Useful during development.
#
# /BUG STATE	      <name>...
# /BUG STATE SAVE    [<name>]
# /BUG STATE RESTORE [<name>]
# /BUG STATE FORGET  [<name>]
#	Save and restore the currently open bugwins.
#
# /BUG SERVER [<alias>]
# /BUG SERVER  <alias> <url> [[<user>] <email>]
# /BUG SERVER  <alias> SET   <key> <value>...
# /BUG SERVER  <alias> UNSET <key>
# /BUG SERVER SAVE   <alias>
# /BUG SERVER DELETE <alias>
#	Create, see, change and delete known Bugzilla configurations.
#
# /BUG CONNECT
#	Show the open Bugzilla associations.
# /BUG LOGIN [<email>]
#	Login into the current window's Bugzilla.
#
# /BUG OPEN   [<bugzilla>] <bug>
#	Show a bug in a new window.
# /BUG SUMMARY [<bugzilla>] <bug>
#	Show the summary of a bug in the current window.
# /BUG BROWSE [<bugzilla>] <bug> [#<comment>]
#	Open a bug in a WWW browser.
#
#Valid commands in the status window and in chatwins:
# /BUG CONNECT <alias> | <url> [[<user>] <email>]
# /BUG LOGIN   <alias> | <url>  [<user>] <email>
# /BUG DISCONNECT
#	(Dis)Associates the current window with a Bugzilla.
#
#Commands for bugwin only:
# /BUG URL [#<comment>]
#	Show the current bug's show_bug.cgi URL.
# /BUG RELOAD
#	Refresh the current bug.
# /BUG SUMMARY
#	Refresh the summary of the current bug.
# /BUG BROWSE
#	Open the current bug in a WWW browser.
# /BUG ATTACHMENT [[{URL|CAT|GET}] <attachment>]
#	See bug attachments.
# /BUG NEWS [-all|-<n>|-<n>d]
#	View a bug's history.
# /BUG BLACKLIST
# /BUG UNBLACKLIST
#	Ignore or notice again this bug when sniffing.
#
# /BUG RENAME <summary>
# /BUG TUNE	[-tm <TM>] [-prio[rity] <prio>] [{-severity|-svr} <severity>]
# /BUG TAKE	[-assign]		[<comment>]
# /BUG RESOLVE	[-tm <TM>] <resolution>	[<comment>]
# /BUG REOPEN				[<comment>]
# /BUG WTF				[<comment>]
# /BUG FWT				[<comment>]
# /BUG COMMENT				[<comment>]
#	Change the current window's bug and/or add a comment.
#
#Valid commands in chatwins and bugwins:
# /BUG SNIFF
# /BUG UNSNIFF
#	Automatically open bugs mentioned on the current channel/query.
# ]]]
#
# Design features:
# -- do not require Perl 5.10
# -- support Bugzilla 3.0, 3.2 and 3.4
# -- don't block irssi with network I/O
# -- be lightweight on network traffic
# -- don't store passwords
# -- DWIM user interface
#
# TODO
# reads need not be parallel()
# /BUG SEARCH
# /BUG PING [<timeout>]
#	Check for news periodically.
#

# Modules
use strict;
use Irssi;
use Storable;
use POSIX qw(mktime);
use LWP::UserAgent;
use HTTP::Status;
use HTTP::Request;
use HTTP::Request::Common;
use XML::Parser;
use Text::ParseWords;
use Date::Parse;
use URI;

# Dump HTTP traffic?
BEGIN { $LWP::DebugFile::outname = '/tmp/lwp' }
use LWP::DebugFile;
use LWP::Debug qw(conns);

# Private constants [[[
my $COLUMNS = defined $ENV{'COLUMNS'} ? $ENV{'COLUMNS'}-3 : 77;

# Formats for print_bug()
my $FORMAT_C   = '@' . '|' x $COLUMNS;
my $FORMAT_L   = '@' . '<' x $COLUMNS;
my $FORMAT_LR  = '@' . '<' x (int($COLUMNS/2)-1) . ' ';
   $FORMAT_LR .= '@' . '>' x ($COLUMNS-2 - int($COLUMNS/2));

my $FORMAT_ACTIVITY =
	  '@' . ('<' x 24) . ' '
	. '@' . ('<' x ($COLUMNS-(25+1)));

# Fields for get_bug().  A $MINIMAL_BAG is fetched to refresh the specified
# fields after a modification.  $SMALL_BAG:s are shown in a /BUG SEARCH.
# $NORMAL_BAG:s contain all the information necessary for a /BUG SUMMARY.
# A $HEAVY_BAG includes all the comments.
my $MINIMAL_BAG	= [ qw(bug_id delta_ts token) ];
my $SMALL_BAG	= [ qw(bug_id bug_status resolution
	bug_severity priority target_milestone
	product component changeddate short_desc) ];
my $NORMAL_BAG	= [ @$MINIMAL_BAG, qw(
	creation_ts assigned_to
	short_desc attachment
	bug_status resolution
	priority bug_severity
	product	component
	version target_milestone
	keywords dependson blocked) ];
my $HEAVY_BAG	= [ @$NORMAL_BAG, qw(long_desc) ];
# ]]]

# Private variables [[[
# # Boogie::LWP object to access a Bugzilla through HTTP.
# # The additional fields tell how to authenticate with the HTTP server.
# # boogie_http_user is either read from the settings or asked at the
# # first contact.  boogie_http_pass is always prompted for.
# # boogie_http_auth is the last simple_request()s Authorization: header,
# # which is needed by xmlrep() to save it as a default header to send it
# # with all subsequent requests.
# lwp = { boogie_http_user, boogie_http_pass, boogie_http_auth }
#
# # Represents a Bugzilla, either connected or just a config.
# buz =
# {
#	url,		# The root URL of this Bugzilla.
#	alias,		# The name the user can refer to this Bugzilla.
#			# Configs stored in settings always have an alias,
#			# otherwise may or may not.
# 
#	user,		# Used to initialize $$lwp{'boogie_http_user'}.
#			# Can be undef, set by /BUG SERVER, stored in
#			# settings.
#	email,		# The e-mail address to log in with.  Will be
#			# prompted for if undef.  Not stored in settings,
#	emailcfg,	# but initializd with emailcfg, which is stored
#			# and changed with /BUG SERVER.
#
#	lwp,		# The $lwp to use for communication.  Every $buz
#			# has a different one.  undef if the $buz has not
#			# been connected to.  Not cleared when disconnected.
#
#	waiters,	# An array of callbacks to call when the currently
#			# running enqueue()d operation finished.  If not
#			# undef then further operations should be enqueue()d
#			# as well.
#	cancel,		# A callback which cancels the currently running
#			# enqueue()d operation.  # Undefined iff 'waiters'
#			# is undefined.
#	doers,		# The list of cancel callbacks of the currently
#			# executing parallel() operations.
# 
#	prefixes,	# An array of strings which may prefix bare bug
#			# numbers.  Stored in settings, otherwise may be
#			# undef.
#	rex, 		# A regular expression which can grep bug numbers
#			# belonging to this Bugzilla.  Used for sniffing.
#			# Compiled from prefixes.
# }
#
# # Identifies a bug within a bugzilla.
# bug =
# {
#	url,		# The bug's complete show_bug.cgi URL.
#	buz,		# Where the bug exists.  It may be that the buz is
#			# already deleted from %Configs and %Bugzillas.
#	ts		# The bug's delta_ts, the time it was last modified,
# 			# when we fetched it.  It's refreshed by change_bug(),
# 			# by change_bug_properties() if necessary, and by
# 			# cmd_reload() and cmd_comment().
#	token,		# A random hexadecimal string sent by newer Bugzillas
#			# and required when the bug is modified to prevent
#			# some malice.  Both the timestamp and the token are
#			# refreshed when the bug is reloaded.
#	attachments,	# bag::_ATTACHMENTS
# }
#
# # A raw bug as downloaded from a Bugzilla.  The keys are XML tag names.
# bag =
# {
#	token, delta_ts,
#	%fields		= ((key => value), ...),
#	_COMMENTS	= [ [ who, bug_when, thetext ], ... ],
#
#	# 'flags' is a comma-separated list of is... flags of the attachment
#	# like ispatch and isobsolete.
#	_ATTACHMENTS	= [ [ attachid, flags, date, desc, filename ], ... ],
# }
#
# # Loaded from settings when /RUN.  The list of $buz aliases is stored
# # in the 'aliases' setting.  The configs are stored serialized in
# # "srv_<alias>" settings.
# %Configs:	alias     => buz
#
# # Chat windows: each $buz is either in %Configs, %Bugzillas,
# # it can be the $Default_Bugzilla or any combination thereof.
# # If it is in %Bugzillas then it is currently connected.
# # It can be connected to multiple windows.  %Sniffs is a
# # set of those windows which are being /BUG SNIFF:ed.
# # %Blacklisted is a set of bugs which should not be opened
# # when sniff()ing.
# %Bugzillas:	window_id => buz
# %Sniffs:	window_id => 1
#
# # Bug windows:
# %Bugs:	window_id => bug
# %Bugwins:	bug_url   => window_id
# %Blacklisted:	bug_url   => 1
my $Default_Bugzilla;
my (%Configs, %Bugzillas);
my (%Bugs, %Bugwins);
my (%Sniffs, %Blacklisted);
# ]]]

# Program code
# Irssi accessories [[[
# In order to be testable some irssi APIs need to be worked around
# or emulated.

# Windows [[[
sub is_status_window
{
	my $win = shift;
	my $statwin;

	# This is the same algorithm as Irssi::print() uses
	# to print things.
	return 0 if !Irssi::in_irssi();
	$statwin = Irssi::window_find_closest(undef,
		tied(*Irssi::DEFAULT)->[0]);
	return $$win{'_irssi'} == $$statwin{'_irssi'};
}

# Open a new window.
sub new_window
{
	my ($win, $title, $name, $isauto) = @_;

	return Irssi::in_irssi()
		? Irssi::Irc::Server::query_create(
			$title, $name, $isauto)->window()
		: $win;
}
# ]]]

# User I/O [[[
if (!Irssi::in_irssi())
{
	*MSGLEVEL_NEVER			=
		*MSGLEVEL_CLIENTCRAP	=
		*MSGLEVEL_CLIENTNOTICE 	=
		*MSGLEVEL_CLIENTERROR 	= sub { 0 };
	*Irssi::print = sub { print shift, "\n" };
} else
{	# Add a method that escapes the escape characters.
	no warnings 'once';
	*Irssi::UI::Window::printq = sub
	{
		my ($self, $str) = (shift, shift);

		$str =~ s/%/%%/g;
		$self->print($str, @_);
	};
}

# Print an error message in the status window and return undef.
# This makes it usable in return statements.
sub error
{
	my $msg = shift;

	# We can't modify $_[0] in place because it can be
	# a string literal.
	chomp($msg);

	Irssi::print($msg, MSGLEVEL_CLIENTERROR);
	return wantarray ? undef : ();
}

sub not_enough_arguments
{
	Irssi::signal_emit("error command", 3, shift);
	return undef;
}

# Ask $prompt and call $next() with the answer and all the other parameters.
# If $issecret the answer won't be echoed nor put in the history.
sub ask_something
{
	my ($issecret, $prompt, $next) = (shift, shift, shift);

	if (Irssi::in_irssi())
	{
		my ($me1, $paste_detect_time, @nextargs);

		# There is no synchronous Irssi::read(),
		# we need to hack around by redirecting
		# user entry and capturing it.
		@nextargs = @_;
		$me1 = sub
		{
			my ($ans, $me2);

			# We're the first handler of key send_line.
			# irssi will clear the answer and unredirect
			# the entry after we've finished.  So we need
			# to get the answer now, but if $next wants
			# to ask() again we need to do this after irssi
			# is done.
			Irssi::signal_remove("key send_line", $me1);
			$ans = Irssi::parse_special('$L');
			$me2 = sub
			{
				Irssi::signal_remove("key send_line", $me2);
				$next->($ans, @nextargs)
			};
			Irssi::signal_add_last("key send_line", $me2);

			# Restore paste detection.  By omitting "msecs"
			# you can hang irssi.
			Irssi::settings_set_time("paste_detect_time",
				"${paste_detect_time}msecs");
			Irssi::signal_emit("setup changed");
		};
		Irssi::signal_add_first("key send_line", $me1);
		Irssi::signal_emit("gui entry redirect", undef,
			"$prompt: ", $issecret ? 0x02 : 0x00, undef);

		# Disable paste detection, so you can paste code.
		$paste_detect_time = Irssi::settings_get_time(
			"paste_detect_time");
		Irssi::settings_set_time("paste_detect_time", 0);
		Irssi::signal_emit("setup changed");
	} else
	{
		my ($noecho, $ans);

		$noecho = $issecret && -t STDIN;
		print STDERR "$prompt: ";
		system(qw(stty -echo)) if $noecho;
		$ans = <STDIN>;
		chop($ans);
		print STDERR "\n" if $issecret;
		system(qw(stty  echo)) if $noecho;
		$next->($ans, @_);
	}
}

sub ask_secret	{ unshift(@_, 1), &ask_something }
sub ask		{ unshift(@_, 0), &ask_something }

# Make it possible for the user to make a little speech about $prompt.
# If it's not discarded $next is called as ask() would do.
# It probably conflicts with unrelated ask()s like password requests badly.
sub speech
{
	my ($win, $prompt, $next) = (shift, shift, shift);
	my @nextargs = @_;
	my ($me, @speech);

	# ask() until enough.
	$win->print('End your speech with a ".", cancel with a "---"');
	ask($prompt, $me = sub
	{
		my $ans = shift;

		if ($ans eq '---')
		{
			return;
		} elsif ($ans eq '.')
		{
			$next->(join("\n", @speech), @nextargs);
		} else
		{
			$win->printq($ans);
			push(@speech, $ans);
			ask($prompt, $me);
		}
	});
}
# ]]]

# Settings [[[
# Deletes $key from boogie's settings.
sub delete_setting
{
	my $key = shift;

	# Irssi can't seem to delete settings reliably,
	# so let's invalidate $key in any case.
	Irssi::settings_add_str('boogie', "boogie_$key", "UNSET");
	Irssi::settings_set_str("boogie_$key", "UNSET");
	Irssi::settings_remove("boogie_$key");
}

# Save a key-list os values in boogie's settings.
# Undefs are allowed in the values.
sub write_setting
{
	my $key = shift;
	my (@values, $value);

	# Delete the settings if there are no values.
	$key = "boogie_$key";
	if (!@_)
	{
		Irssi::settings_remove($key);
		return;
	}

	# Concatenate the values with a '|', escaping the separator.
	foreach (@_)
	{
		if (defined $_)
		{
			$value = $_;
			$value =~ s/\\/\\\\/g;
			$value =~ s/\|/\\|/g;
			push(@values, $value);
		} else
		{
			push(@values, '');
		}
	}

	Irssi::settings_add_str('boogie', $key, '');
	Irssi::settings_set_str($key, join('|', @values));
}

# Returns the list of values of $key or an empty list
# if $key is not in boogie's settings.
sub read_setting
{
	my $key = shift;
	my ($value, @values);

	$key = "boogie_$key";
	Irssi::settings_add_str('boogie', $key, 'UNSET');
	$value = Irssi::settings_get_str($key);
	if ($value eq 'UNSET')
	{
		Irssi::settings_remove($key);
		return ();
	}

	# Unescape the parameter separator.
	@values = split(/\|/, $value);
	s/\\(.)/$1/g foreach @values;
	$_ ne '' or undef $_ foreach @values;
	return @values;
}
# ]]]
# ]]]

# HTTP communication [[[
# In order not to block irssi send the request, and receive and process the
# reply in another process and get the results through a pipe asynchronously.
# We must arrage for HTTP state updates to find their way back to the parent
# process, and make sure the whole process can be cancelled any time.

sub callback
{
	my $callback = shift;
	goto $callback if $callback;
}

sub failback
{
	my ($callback, $msg) = @_;

	error($msg);
	&$callback() if $callback;
}

# Returns the domain part of a request URL.
sub get_domain
{
	my $req = shift;

	$req = $req->uri() if ref $req;
	$req =~ m!^.*?://([^/:]*)!;
	return $1;
}

# Forks a process for $pusher which must return a reference and feeds it
# into $sucker when it's complete.
sub outsource
{
	my ($pusher, $sucker, $cancel) = @_;
	my $pid;

	# Exchange data with Storable.
	local (*TO_READ, *TO_WRITE);
	pipe(TO_READ, TO_WRITE);
	if (!($pid = fork()))
	{
		close(TO_READ);

		# Need to duplicate $@.
		my $ret = eval { $pusher->() };
		Storable::store_fd($@ ? \"$@" : $ret, \*TO_WRITE);

		# Irssi does something nasty if we simply exit().
		close(TO_WRITE);
		kill('KILL', $$);
	} elsif (Irssi::in_irssi())
	{
		my ($fh, $cleanup, $ioid);

		# Need to save *TO_READ because it will be reset
		# the moment we leave the function.
		$fh = *TO_READ;

		$cleanup = sub
		{	# Don't leave zombies and open files behind.
			Irssi::input_remove($ioid);
			close($fh);
			waitpid($pid, 0);
		};

		$ioid = Irssi::input_add(fileno(TO_READ), INPUT_READ, sub
		{
			$sucker->(Storable::fd_retrieve(\$fh));
			&$cleanup();
		}, undef);

		return sub
		{
			kill('KILL', $pid);
			&$cleanup();
			&$cancel() if defined $cancel;
		};
	} else
	{
		$sucker->(Storable::fd_retrieve(\*TO_READ));
		waitpid($pid, 0);
		return $cancel || sub { };
	}
}

# Log the HTTP reply if LWP::Debug is use'd.
*tee = %LWP::Debug::
? sub
{
	my $processor = shift;
	return sub
	{
		LWP::Debug::conns($_[0]);
		goto $processor;
	};
} : sub
{
	return shift
};

# Return a function which executes $processor as long as it doesn't die.
# $kukacr is the location of the error string, if any.  This twist is
# necessary because because $lwp->request() is not transparent to death.
sub terror
{
	my ($kukacr, $processor) = @_;

	sub
	{
		defined $$kukacr
			or defined eval { &$processor; 1 }
			or $@ eq ''
			or $$kukacr = $@
	}
}

# Makes a request and expects an XML-like response (like HTML),
# which will be processed with $class and its results fed to $callback.
sub xmlrep
{
	my ($lwp, $req, $parser, $on_success, $on_failure) = @_;
	my $cancel;

	# Ask for password beforehand if we know we'll need it.
	if (defined $$lwp{'boogie_http_user'}
		&& !defined $$lwp{'boogie_http_pass'})
	{
		my $domain = get_domain($req);
		$cancel = sub { };
		ask_secret("HTTP password at $domain", sub
		{
			$$lwp{'boogie_http_pass'} = shift;
			$cancel = xmlrep($lwp, $req, $parser,
				$on_success, $on_failure);
		});

		return sub { &$cancel };
	}

	$cancel = outsource(sub
	{
		my ($rep, $ret);

		# Convert URL to request.
		$req = HTTP::Request->new(GET => $req)
			unless ref $req;

		if (!ref $parser)
		{	# $parser is an XML::Parser Style.
			my $kukac;

			# PMO Bugzilla (3.0) allows weird characters
			# in the XML output.
			$parser = XML::Parser->new(
				Style => $parser,
				ProtocolEncoding => 'ISO-8859-1');
			$parser = $parser->parse_start();
			$rep = $lwp->request($req, terror(\$kukac, tee(sub
				{ $parser->parse_more(shift) })));
			is_success($rep->code())
				or die $rep->status_line();
			die $kukac if defined $kukac;

			# XML::Parser::parse_done() won't return anything
			# in scalar context.  (?) If the status is not OK
			# the response body won't be parsed.
			($ret) = $parser->parse_done();
		} else
		{	# $parser is the parser.
			my $kukac;

			$rep = $lwp->request($req, terror(\$kukac, tee(sub
				{ $parser->parse(shift) })));
			is_success($rep->code())
				or die $rep->status_line();
			die $kukac if defined $kukac;
			$parser->eof();
			if ($parser->isa('HASH'))
			{
				$ret = $$parser{'result'};
			} elsif ($parser->isa('ARRAY'))
			{
				$ret = $parser;
			} elsif ($parser->isa('SCALAR'))
			{
				$ret = $$parser;
			}
		}

		# Communicate state updates to the sucker.
		return
		{
			result		=> $ret,
			cookies		=> $lwp->cookie_jar()->{'COOKIES'},
			authorization	=> $$lwp{'boogie_http_auth'},
		};
	}, sub
	{
		my $ret = shift;

		if (ref($ret) ne 'SCALAR')
		{	# Normal reply, $ret should be a hash.
			# Update our cookies and set the sent
			# Authorization header as default.
			$lwp->cookie_jar()->{'COOKIES'} =
				delete $$ret{'cookies'};
			$lwp->default_headers()->authorization(
					delete $$ret{'authorization'})
				if defined $$ret{'authorization'};
			callback($on_success, delete $$ret{'result'});
		} elsif ($$ret =~ /^401\b/
			&& !defined $$lwp{'boogie_http_user'})
		{
			my $domain = get_domain($req);
			ask("HTTP user at $domain", sub
			{	# xmlrep() will ask for password.
				$$lwp{'boogie_http_user'} = shift;
				$cancel = xmlrep($lwp, $req, $parser,
					$on_success, $on_failure);
			});
		} elsif ($$ret =~ /^401\b/
			&& defined $$lwp{'boogie_http_pass'})
		{	# Authentication failure, get password again.
			delete $$lwp{'boogie_http_pass'};
			$cancel = xmlrep($lwp, $req, $parser,
				$on_success, $on_failure);
		} else
		{	# Either some other HTTP error or the response
			# processor had problems.
			failback($on_failure, $$ret);
		}
	});

	return sub { &$cancel };
}

# Constructs an XML-RPC request.
sub mkxmlreq
{
	my $method = shift;
	my $req;

	$req  = '<?xml version="1.0" encoding="us-ascii"?>';
	$req .= '<methodCall>';
	$req .= "<methodName>$method</methodName>";

	if (@_)
	{
		$req .= '<params><param><value><struct>';
		do
		{
			my ($key, $val) = (shift, shift);
			$req .= '<member>';
			$req .= "<name>$key</name>";
			$req .= "<value><string>$val</string></value>";
			$req .= '</member>';
		} while (@_);
		$req .= '</struct></value></param></params>';
	}

	$req .= '</methodCall>';
	return $req;
}

# Submits an XML-RPC request with the supplied method and parameters,
# process the XML reply and call $callback with the result.
sub xmlreq
{
	my ($lwp, $url) = (shift, shift);
	my ($on_failure, $on_success) = (pop, pop);
	my $req;

	$req = HTTP::Request->new(POST => $url);
	$req->header('Content-Type' => 'text/xml');
	$req->content(mkxmlreq(@_));
	return xmlrep($lwp, $req, 'Boogie::XMLRPC', sub
	{
		my $ret = shift;

		# XML-RPC error response?
		defined $ret && ref($ret) eq 'HASH' && $$ret{'faultString'}
			? failback($on_failure, $$ret{'faultString'})
			: callback($on_success, $ret);
	}, $on_failure);
}
# ]]]

# Bugzilla [[[
# Returns the version number of the Bugzilla at $url.  This is used to ping
# $url that it indeed points to a Bugzilla installation.
sub get_bugzilla_version
{
	my ($lwp, $url, $on_success, $on_failure) = @_;
	my $cancel;

	$cancel = xmlreq($lwp, "$url/xmlrpc.cgi", 'Bugzilla.version', sub
	{
		my $ret = shift;

		defined $$ret{'version'}
			? callback($on_success, $$ret{'version'})
			: failback($on_failure, 'Nonsense Bugzilla reply');
	}, sub
	{	# Perhaps this Bugzilla installation doesn't have XML-RPC.
		# Try to find evidence in the <title> of the home page that
		# this is a indeed a Bugzilla.
		$cancel = xmlrep($lwp, $url, Boogie::GrepTag->new('title'), sub
		{
			my $title = shift;

			defined $title && $title =~ /\bBugzilla\b/
				? callback($on_success, '')
				: faillback($on_failure, 'Bugzilla not found');
		}, $on_failure);
	});

	return sub { $cancel };
}

# $buz, $bid, [show|activity]
sub get_bug_url
{
	join('', $_[0]->{'url'}, '/',
		"show_", defined $_[2] ? $_[2] : 'bug', '.cgi',
		"?id=", $_[1])
}

sub get_bug
{
	my ($lwp, $url, $fields, $on_success, $on_failure) = @_;
	my $query;

	# Limit the fields to what we can process.
	# Especially attachments can be huge.
	$query  = "$url&ctype=xml";
	$query .= "&field=$_" for @$fields;
	return xmlrep($lwp, $query, 'Boogie::BuzXML', sub
	{
		my $ret = shift;

		ref($ret) eq 'HASH' && defined $$ret{'_ERROR'}
			? failback($on_failure, $$ret{'_ERROR'})
			: callback($on_success, $ret);
	}, $on_failure);
}

sub get_bugs
{
	my ($lwp, $url, $fields, $on_success, $on_failure) = @_;
	my $query;

	# Limit the fields to what we can process.
	# Especially attachments can be huge.
	$query  = "$url&ctype=csv";
	$query .= "&columnlist=" . join(',', @$fields);
	return xmlrep($lwp, $query, Boogie::CSVParser->new(),
		$on_success, $on_failure);
}

sub get_attachment
{
	my ($lwp, $url, $out) = @_;

	return xmlrep($lwp, $url, $out,
		sub { Irssi::print("Download of $$$out completed") },
		sub { error("$$$out: " . shift) });
}

sub get_activity
{
	my ($lwp, $url, $on_success, $on_failure) = @_;

	# We cannot use XML-RPC::get_history because Bugzilla 3.0
	# didn't implement that.  So we end up parsing the human-readable
	# HTML.
	return xmlrep($lwp, $url, Boogie::ActivityParser->new(),
		$on_success, $on_failure);
}

sub change_bug
{
	my ($bug, $oktocollide, $fields) = (shift, shift, shift);
	my ($on_failure, $on_success) = (pop, pop);
	my (@packet, $cancel);

	# Bugzilla 3.2 and 3.4 are unhappy without the longdesclength field.
	# (which i don't know what is
	# by the way)
	@packet =
	(
		@$fields,
		delta_ts			=> $$bug{'ts'},
		longdesclength			=> 2
	);

	# Bugzilla 3.0 which doesn't have tokens is crap and would
	# require us to replay all fields unless we pretend mass
	# bug changing.  `target_milestone' is included for the
	# especially ancient PMO bugzilla.
	push(@packet, defined $$bug{'token'}
		? (
			id			=> $$bug{'bid'},
			token			=> $$bug{'token'})
		: (
			"id_$$bug{'bid'}"	=> 1,
			dontchange		=> 'dontchange',
			product			=> 'dontchange',
			component		=> 'dontchange',
			target_milestone	=> 'dontchange'));

	$cancel = xmlrep($$bug{'buz'}{'lwp'},
		POST("$$bug{'buz'}{'url'}/process_bug.cgi", \@packet),
		Boogie::ProcessHTMLResponse->new(), sub
	{
		my $ret = shift;

		# Update token and delta_ts then try understand
		# the outcome of the change.
		refresh_bug($bug, $ret);
		if (!defined $$ret{'summary'})
		{	# Some low-level internal error, like a database
			# failure.
			failback($on_failure, 'Change failed');
		} elsif (($oktocollide && $$ret{'summary'} =~ /collision/i)
			|| $$ret{'summary'} =~ /suspicious/i)
		{
			# Our change can be suspicious to Bugzilla 3.4 whose
			# XML output is broken and gives wrong tokens, so
			# let's try again with the one included in the reply.
			# This makes us twice as slow.  Otherwise if it's a
			# collision we can ignore that too because comments
			# are safe to collide.
			Irssi::print("resubmit ($$ret{'summary'})");
			$cancel = change_bug($bug, $oktocollide,
				$fields, $on_success, $on_failure);
		} elsif ($$ret{'summary'} =~ /processed/i)
		{	# Success.
			callback($on_success, $ret);
		} else
		{
			# Some other error, like an Internal error,
			# which is usually because of missing fields.
			$$ret{'summary'} =~ s/:$//;
			failback($on_failure, $$ret{'summary'});
		}
	}, undef);

	return sub { &$cancel };
}
# ]]]

# Scheduling [[[
# To preserve some ordering between requests (esp. wrt login and changed)
# and to make everything cancellable we need some task administration.

sub get_success_failure
{
	my ($on_success, $on_failure, $on_destroy) = @_;

	return (sub
	{
		Irssi::signal_remove('window destroyed', $on_destroy)
			if Irssi::in_irssi();
		goto $on_success if defined $on_success;
	}, sub
	{
		Irssi::signal_remove('window destroyed', $on_destroy)
			if Irssi::in_irssi();
		goto $on_failure if defined $on_failure;
	});
}

sub enqueue
{
	my ($win, $buz, $fun) = (shift, shift, shift);
	my ($on_failure, $on_success) = (pop, pop);
	my ($wid, $on_destroy, $waiter);

	$wid = $$win{'_irssi'};
	$on_destroy = sub
	{
		return if shift->{'_irssi'} != $wid;
		@{$$buz{'waiters'}} = grep($_ != $waiter,
			@{$$buz{'waiters'}});
		$$waiter[1]();
		@{$$buz{'waiters'}}
			or $$buz{'cancel'}->();
	};
	$waiter = [get_success_failure($on_success,$on_failure,$on_destroy)];
	Irssi::signal_add('window destroyed', $on_destroy)
		if Irssi::in_irssi();

	if (!$$buz{'waiters'})
	{
		my ($waiters, $done);

		$waiters = [ $waiter ];
		$done = sub
		{
			my $how = shift;

			delete $$buz{'waiters'};
			delete $$buz{'cancel'};
			$$_[$how](@_) foreach @$waiters;
		};

		$$buz{'waiters'} = $waiters;
		$$buz{'cancel'} = &$fun(@_,
			sub { unshift(@_, 0); goto $done },
			sub { unshift(@_, 1); goto $done });
	} else
	{
		push(@{$$buz{'waiters'}}, $waiter);
	}
}

sub single
{
	my ($win, $fun) = (shift, shift);
	my ($on_failure, $on_success) = (pop, pop);
	my ($wid, $on_destroy, $cancel);

	$wid = $$win{'_irssi'};
	$on_destroy = sub { &$cancel() if shift->{'_irssi'} == $wid };
	Irssi::signal_add('window destroyed', $on_destroy)
		if Irssi::in_irssi();

	$cancel = $fun->(@_,
		get_success_failure($on_success, $on_failure, $on_destroy));
}

sub parallel
{
	my @args = @_;
	my ($win, $buz, $fun) = (shift, shift, shift);
	my ($on_failure, $on_success) = (pop, pop);

	if ($$buz{'waiters'})
	{
		enqueue($win, $buz, $fun, @_,
			sub { parallel(@args) }, $on_failure);
	} elsif (Irssi::in_irssi())
	{
		my ($cancel, $doers);

		defined ($doers = $$buz{'doers'})
			or $doers = $$buz{'doers'} = [ ];
		$cancel = single($win, $fun, @_, sub
		{
			@$doers = grep($_ != $cancel, @$doers);
			goto $on_success if defined $on_success;
		}, sub
		{
			@$doers = grep($_ != $cancel, @$doers);
			goto $on_failure if defined $on_failure;
		});
		push(@$doers, $cancel);
	} else
	{	# $fun cannot be cancelled.
		single($win, $fun, @_, $on_success, $on_failure);
	}
}
# ]]]

# Configurations [[[
# We store known Bugzillas in irssi settings.

# Write the list of stored configurations to the settings.
# This is necessary to know what configs to load next time we /RUN.
sub update_config_list
{
	write_setting('aliases', map($$_{'alias'}, values(%Configs)));
}

# Saves or update $buz's configuration in the settings.
sub save_config
{
	my $buz = shift;

	# Prefix the setting key with "srv" to prevent collision
	# with other settings of ours.
	write_setting("srv_$$buz{'alias'}",
		@$buz{qw(url user emailcfg)}, @{$$buz{'prefixes'}});
}

# Remove $buz's config from settings and %Config.
sub delete_config
{
	my $buz = shift;

	delete_setting("srv_$$buz{'alias'}");
	delete $Configs{$$buz{'alias'}};
	update_config_list();
}

# Adds $buz's config to %Config and settings.
sub add_config
{
	my ($alias, $buz) = @_;

	$$buz{'alias'} = $alias;
	$Configs{$alias} = $buz;
	save_config($buz);
	update_config_list();
}

# Change $buz's alias.  If there's already a config with $newalias
# it's silently overridden.
sub rename_config
{
	my ($buz, $newalias) = @_;

	return if $$buz{'alias'} eq $newalias;

	# Not using delete_config() avoids an extra update_config_list().
	delete_setting("srv_$$buz{'alias'}");
	delete $Configs{$$buz{'alias'}};
	add_config($newalias, $buz);
}

# Populate %Configs with the Bugzilla configurations found in the settings.
sub load_configs
{
	# The list of stored configurations is kept in a separate setting.
	foreach my $alias (read_setting('aliases'))
	{
		my ($url, $user, $email, @prefixes);

		(($url, $user, $email, @prefixes) =
				read_setting("srv_$alias"))
			or next;
		$Configs{$alias} = 
		{
			alias		=> $alias,
			url		=> $url,
			user		=> $user,
			emailcfg	=> $email,
			email		=> $email,
			prefixes	=> \@prefixes,
		};
	}
}
# ]]]

# Boogie commands [[[
# Common code [[[
# Returns which $buz to be used for $win.
sub get_bugzilla_for_window
{
	my $win = shift;
	my ($wid, $buz, $bug);

	$wid = $$win{'_irssi'};
	if (!defined ($buz = $Bugzillas{$wid}))
	{
		if (defined ($bug = $Bugs{$wid}))
		{
			$buz = $$bug{'buz'};
		} elsif (!defined ($buz = $Default_Bugzilla))
		{
			return wantarray ? () : undef;
		}
	}
	return wantarray ? ($buz, $bug) : $buz;
}

# Returns if the argument is $Default_Bugzilla.
sub is_default_connection
{
	defined $Default_Bugzilla && $Default_Bugzilla == shift
}

# Returns whether $buz is used by a window.
sub is_connected
{
	my $buz = shift;

	return 1 if is_default_connection($buz);
	$_ == $buz and return 1 foreach values(%Bugzillas);
	return 0;
}

# Returns all Bugzillas in use.
sub all_connections
{
	my %cons;

	$cons{$Default_Bugzilla} = $Default_Bugzilla
		if defined $Default_Bugzilla;
	$cons{$_} = $_ foreach values(%Bugzillas);
	return \%cons;
}

# Cancel all enqueue()d and parallel() operations of $buz.
sub disconnect
{
	my $buz = shift;

	$$buz{'cancel'}() if $$buz{'cancel'};
	do { &$_ foreach @{$$buz{'doers'}} }
		if $$buz{'doers'};
}

# Makes $buz connected, adds it to $Bugzillas and/or makes it
# the $Default_Bugzilla.
sub new_connection
{
	my ($win, $buz) = @_;
	my $prev;

	if (!is_status_window($win))
	{
		!defined ($prev = $Bugzillas{$$win{'_irssi'}})
			or $prev != $buz
			or return;
		$Bugzillas{$$win{'_irssi'}} = $buz;
		if (!defined $Default_Bugzilla)
		{
			$Default_Bugzilla = $buz;
			Irssi::print(
				"Default Bugzilla changed to $$buz{'url'}");
		}
	} else
	{
		!defined ($prev = $Default_Bugzilla)
			or $prev != $buz
			or return;
		$Default_Bugzilla = $buz;
	}

	# If we replaced a previous connections which is
	# not used anymore cancel its ongoing operations.
	disconnect($prev) if defined $prev && !is_connected($prev);

	$win->printq("Connected to Bugzilla at $$buz{'url'}",
		MSGLEVEL_CLIENTNOTICE);
}

# Add an LWP to $buz if it doesn't have one yet.
sub revive_bugzilla
{
	my $buz = shift;

	$$buz{'lwp'} = Boogie::LWP->new($$buz{'user'})
		unless defined $$buz{'lwp'};
}

# Transfer important information from the raw representation of a bug
# to our internal nonvolatile representation.  $bag can either be the
# output of Boogie::BuzXML or Boogie::ProcessHTMLResponse.
sub refresh_bug
{
	my ($bug, $bag) = @_;

	$$bug{'token'}		= delete $$bag{'token'}
		if defined $$bag{'token'};
	$$bug{'ts'}		= delete $$bag{'delta_ts'}
		if defined $$bag{'delta_ts'};
	$$bug{'attachments'}	= delete $$bag{'_ATTACHMENTS'}
		if defined $$bag{'_ATTACHMENTS'}
			&& (@{$$bag{'_ATTACHMENTS'}}
				|| !$$bug{'attachments'});
}

# Launch an X11 WWW browser.
sub browse
{
	$ENV{'DISPLAY'} = ':0' unless defined $ENV{'DISPLAY'};
	Irssi::command("EXEC x-www-browser " . shift);
}
# ]]]

# HELP [[[
# Format our comments in $_ to be displayable in irssi.
sub procline
{
	my $col;

	chop;
	$col = length;
	s/^# *//;
	$col = $col - length;

	# Expand tabs.
	s/(.)/$1 ne "\t"
		? do { $col++; $1 }
		: do { my $spaces = 8 - ($col % 8);
			$col += $spaces;
			' ' x $spaces }/ge;

	return $_;
}

# /BUG [HELP]
#	Print overall help about boogie commands.
# /BUG HELP <subcommand>
#	Print the usage of <subcommand>.
sub cmd_help
{
	local *ME;
	my $dir;

	$dir = Irssi::get_irssi_dir();
	open(ME, '<', "$dir/scripts/boogie.pl")
		|| open(ME, '<', "$dir/scripts/autorun/boogie.pl")
		or return error("lofasz a seggedbe");

	if (!@_)
	{
		do { $_ = <ME> } until /This/;
		do
		{
			Irssi::print(procline($_), MSGLEVEL_CLIENTCRAP);
		} until ($_ = <ME>) =~ /\]{3}$/;
	} else
	{
		my ($re, $found);

		# Skip introduction.
		do { $_ = <ME> } while /^#/;

		# Find the help for the command.  Print help for all
		# commands that match.
		$re = qr{^# /BUG (?:\U\Q[$_[0]]\E|\U\Q$_[0]\E)};
		for (;;)
		{
			my $prelude;

			$prelude = '';
			for (;;)
			{
				defined ($_ = <ME>)
					or return $found
						|| error("No such topic");
				last if $_ =~ $re;
				/^#/ ? ($prelude .= $_) : ($prelude = '');
			}

			Irssi::print('', MSGLEVEL_CLIENTCRAP) if $found;
			$found = 1;

			# Print the text before the /BUG FOO.
			if (length($prelude))
			{	# Rip off the marker.
				$prelude =~ s/^#.*\[\[\[\n(?:#\s*\n)*//;
				Irssi::print(procline(), MSGLEVEL_CLIENTCRAP)
					foreach split(/\n/, $prelude)
			}

			# Print all the comments.
			do
			{
				Irssi::print(procline($_),
					MSGLEVEL_CLIENTCRAP);
			} while ($_ = <ME>) =~ /^#/;
		}
	}
	close(ME);
}
# HELP ]]]

# States [[[
# RESTART [[[
#
# /BUG RESTART [<me>]
#	Restarts the script preserving the state.  <me> designates the
#	script's current name.  Intended for development.
sub cmd_restart
{
	require Data::Dumper;
	my ($win, $me) = @_;
	my $dumper;

	# Cancel all scheduled tasks.
	disconnect($_) foreach values(%{all_connections()});

	# Save our state in a setting then ask Irssi to reload us.
	# When the new instance start executing it'll try to restore
	# the state from the setting, which will be deleted afterwards.
	$dumper = Data::Dumper->new(
	[
		$Default_Bugzilla,
		\(%Configs, %Bugzillas),
		\(%Bugs, %Bugwins),
		\(%Sniffs, %Blacklisted),
	], [
		'Default_Bugzilla',
		'*Configs', '*Bugzillas',
		'*Bugs', '*Bugwins',
		'*Sniffs', '*Blacklisted',
	]);
	$dumper->Freezer('freeze');
	$dumper->Toaster('toast');

	# Neither Data::Dumper nor Storable is able to restore our
	# sniffer regular expression, prune it, we'll recreate it.
	delete $$_{'rex'} foreach values(%Bugzillas);
	delete $$Default_Bugzilla{'rex'} if defined $Default_Bugzilla;

	Irssi::settings_add_str('boogie', "boogie_state", '');
	Irssi::settings_set_str("boogie_state", $dumper->Dump());

	$win->command(defined $me ? "RUN $me" : "RUN boogie");
}
# ]]] 

# STATE [[[
#
# /BUG STATE <name>...
#	Show what bugs are saved in the <name>d sets.
# /BUG STATE SAVE [<name>]
#	Save what bugwins are currently open.
#	If you don't <name> the set 'default' will be assumed.
# /BUG STATE RESTORE [<name>]
#	Open the bugs in the <name>d sets.
# /BUG STATE FORGET [<name>]
#	Forget a saved bugwin set.
sub cmd_state
{
	my $win = shift;
	my ($cmd, $name) = @_;
	my $alias;

	$name = 'default' if !defined $name;
	if (!@_)
	{
		return not_enough_arguments('state');
	} elsif ($cmd =~ /^SAVE$/i)
	{
		write_setting("set_$name", map(
			defined ($alias = $$_{'buz'}{'alias'})
				? ($alias, $$_{'bid'})
				: error("Cannot include bug $$_{'bid'} "
					. "in the set"),
			values(%Bugs)));
		print "Bugwin set saved";
	} elsif ($cmd =~ /^RESTORE$/i)
	{
		foreach (read_setting("set_$name"))
		{
			if (!defined $alias)
			{
				$alias = $_;
			} elsif (!defined $Configs{$alias})
			{
				error("$alias: unknown configuration");
				undef $alias;
			} else
			{
				cmd_open($win, $Configs{$alias}, $_, 1);
				undef $alias;
			}
		}
	} elsif ($cmd =~ /^FORGET$/i)
	{
		delete_setting("set_$name");
		print "Bugwin set forgotten";
	} else
	{
		foreach (@_)
		{
			print "$_:";
			foreach (read_setting("set_$_"))
			{
				if (!defined $alias)
				{
					$alias = $_;
				} else
				{
					print "  $alias: $_";
					undef $alias;
				}
			}
		}
	}
}
# ]]]
# ]]]

# Connections [[[
# Print the configuration of $buz and $mark it. [[[
sub show_config
{
	my ($win, $buz, $mark) = @_;
	my $info;

	$info  = " $mark ";
	$info .=    "Alias:           $$buz{'alias'}\n     "
		if defined $$buz{'alias'};
	$info .=      "Bugzilla URL:  $$buz{'url'}\n";
	$info .= "     HTTP user:     $$buz{'user'}\n"
		if defined $$buz{'user'};
	$info .= "     Bugzilla user: $$buz{'email'}\n"
		if defined $$buz{'email'};
	$info .= "     Bug prefixes:  "
			. join(', ', @{$$buz{'prefixes'}})
		if $$buz{'prefixes'} && @{$$buz{'prefixes'}};
	chomp($info);
	$win->printq($info);
}
# ]]]

# SERVER [[[
#
# Creates, shows and modifies Bugzilla configurations.
#
# /BUG SERVER
#	Print all stored configurations.
# /BUG SERVER <alias>
#	Print the configuration of <alias>.
# /BUG SERVER <alias> <url> [[<user>] <email>]
#	Create a new configuration or change an existing one.
#	<url> is the root URL of the Bugzilla installation.
#	<user> is the HTTP user for Basic authentication.
#	<email> is the Bugzilla user you login with.
#	Does not affect the current connections.
# /BUG SERVER <alias> SET <key> <value>...
#	Change or rename an existing configuration.
#	<key> can be alias, url, user, email or prefixes (or prefix).
#	Prefixes are used by /BUG SNIFF to recognize bug IDs.
# /BUG SERVER <alias> UNSET <key>
#	Remove user, email or prefixes from the stored settings.
#	The effect on prefixes is immediate.
# /BUG SERVER SAVE <alias>
#	Save or duplicate the configuration of the current window's
#	Bugzilla connection.
# /BUG SERVER DELETE <alias>
#	Delete the named configuration from the stored settings.
sub cmd_server
{
	my ($win, $alias) = (shift, shift);
	my $buz;

	if (!defined $alias)
	{	# Print all configs.
		my $cons;

		# Mark active connections with '*'.
		return error("No Bugzilla configurations defined")
			if !%Configs;
		$cons = all_connections();
		show_config($win, $_, $$cons{$_} ? '*' : ' ')
			foreach values(%Configs);
	} elsif (!@_)
	{	# Print $alias.
		return error("No such Bugzilla configuration")
			if !defined ($buz = $Configs{$alias});
		show_config($win, $buz, is_connected($buz) ? '*' : ' ');
	} elsif ($alias =~ /^SAVE$/i)
	{	# Save the current connection settings.
		$alias = shift;
		defined ($buz = get_bugzilla_for_window($win))
			or return error("Not connected to Bugzilla");
		return error("Bugzilla configuration already exists")
			if $Configs{$alias};

		# Duplicate $buz if it's already in $Configs.
		$buz = { map(($_ => $$buz{$_}),
				qw(url user email emailcfg prefixes)) }
			if $Configs{$$buz{'alias'}};
		add_config($alias, $buz);
		print "Configuration $alias saved.";
	} elsif ($alias =~ /^DELETE$/i)
	{	# Delete $alias as config.
		$alias = shift;
		return error("No such Bugzilla configuration")
			if !defined ($buz = $Configs{$alias});
		delete_config($buz);
		print "Configuration $alias deleted.";
	} elsif ($_[0] =~ /^SET$/i)
	{	# Rename $buz or change url, user, email, prefixes.
		shift;

		my $key = shift;
		return not_enough_arguments('server')
			if !@_;
		return error("No such Bugzilla configuration")
			if !defined ($buz = $Configs{$alias});

		if ($key eq 'alias')
		{
			$alias = shift;
			return error("Bugzilla configuration already exists")
				if $Configs{$alias};
			rename_config($buz, $alias);
		} elsif ($key eq 'url' || $key eq 'user')
		{
			$$buz{$key} = shift;
			save_config($buz);
			$$buz{'lwp'}->auth_flush($$buz{'user'})
				if defined $$buz{'lwp'};
		} elsif ($key eq 'email')
		{	# Update both run-time and stored email.
			$$buz{'email'} = $$buz{'emailcfg'} = shift;
			save_config($buz);
		} elsif ($key eq 'prefixes' || $key eq 'prefix')
		{	# sniff() will recompile 'rex'.
			$$buz{'prefixes'} = [ @_ ];
			delete $$buz{'rex'};
			save_config($buz);
		} else
		{
			return error("parameter cannot be changed");
		}

		print $key eq 'alias'
			? "Configuration $alias renamed."
			: "Configuration $alias updated.";
	} elsif ($_[0] =~ /^UNSET$/i)
	{	# Delete user, email, prefixes from settings.
		my $key;

		shift;
		return not_enough_arguments('server')
			if !defined ($key = shift);
		return error("No such Bugzilla configuration")
			if !defined ($buz = $Configs{$alias});

		if ($key eq 'user')
		{
			delete $$buz{$key};
		} elsif ($key eq 'email')
		{	# Only delete from the settings.
			delete $$buz{'emailcfg'};
		} elsif ($key eq 'prefixes')
		{
			delete $$buz{'prefixes'};
			delete $$buz{'rex'};
		} else
		{
			return error("parameter cannot be changed");
		}

		save_config($buz);
		print "Configuration $alias updated.";
	} else	# $alias and bugzilla config given, save it.
	{
		my ($url, $user, $email);

		$url = shift;
		@_ == 1 ? ($email) : ($user, $email) = @_;

		# Don't overwrite already existing configs.
		return error("Bugzilla configuration already exist")
			if defined $Configs{$alias};
		add_config($alias, 
		{
			url		=> $url,
			user		=> $user,
			email		=> $email,
			emailcfg	=> $email,
		});
		print "Configuration $alias saved.";
	}
}
# SERVER ]]]

# CONNECT [[[
#
# Associate or reassociate the current chatwin with a Bugzilla
# or change the default Bugzilla.  Not available in bugwins.
#
# /BUG CON
# /BUG CONN
# /BUG CONNECT
#	List the active connections.
# /BUG CONNECT <bugzilla>
# /BUG CONNECT <url> [[<user>] <email>]
#	See /BUG SERVER for the meaning of the parameters.
#	The first Bugzilla association will become the default one,
#	which will be used if a window is not explicitly associated
#	with another Bugzilla.  After that the default Bugzilla
#	can only be changed in the status window.
sub cmd_conn
{
	my $win = shift;
	my ($url, $user, $email, $buz, $lwp);

	# Parse the parameters.
	if (@_ == 0)
	{	# List connections, mark the current window's.
		my $cons = all_connections();
		return $win->print("Not connected to any Bugzillas.")
			if !%$cons;
		$buz = get_bugzilla_for_window($win);
		show_config($win, $_, is_default_connection($buz) ? '@'
				: defined $buz && $_ == $buz ? '*' : ' ')
			foreach values(%$cons);
		return;
	} elsif (@_ == 1)
	{	# alias or url, try looking up the config
		my $alias = shift;
		if (!defined ($buz = $Configs{$alias}))
		{
			$buz = { url => $alias };
		} elsif (is_connected($buz))
		{	# $buz is already connected on another window
			new_connection($win, $buz);
			return;
		}
	} elsif (@_ == 2)
	{	# url, email
		$buz = { url => shift, email => shift };
		$$buz{'emailcfg'} = $$buz{'email'};
	} else
	{	# url, user, email
		$buz = { url => shift, user => shift, email => shift };
		$$buz{'emailcfg'} = $$buz{'email'};
	}

	# Verify $url and admit $buz into $Bugzillas if it's alright.
	# Cancel the operation if $win is closed.
	revive_bugzilla($buz);
	single($win, \&get_bugzilla_version, $$buz{'lwp'}, $$buz{'url'},
	sub
	{
		my $version = shift;
		$win->printq("Found Bugzilla $version",
			MSGLEVEL_CLIENTNOTICE);
		new_connection($win, $buz);
	}, undef);
}
# ]]]

# LOGIN [[[
#
# /BUG LOGIN [<email>]
#	Log into the current window's connection with <email> if provided.
# /BUG LOGIN <bugzilla>
# /BUG LOGIN <url> [<user>] <email>
#	Like /BUG CONNECT but also log in.
#	Ask for e-mail/password if not provided.
sub cmd_login
{
	my $win = shift;
	my ($buz, $newbuz);

	if (@_ == 0)
	{	# Use current window's connection, ask for email if needed.
		defined ($buz = get_bugzilla_for_window($win))
			or return error('First connect to a Bugzilla');
		defined $$buz{'email'}
			or return ask(
				"Your e-mail address to login with",
				sub { cmd_login($win, $buz, shift) });
	} elsif (ref $_[0])
	{	# We called ourselves after ask()ing email.
		$buz = shift;
		$$buz{'email'} = shift;
	} elsif (@_ >= 3)
	{	# url, user,email
		$buz = { url => shift, user => shift, email => shift };
		$$buz{'emailcfg'} = $$buz{'email'};
	} elsif (@_ == 2)
	{	# url, email
		$buz = { url => shift, email => shift };
		$$buz{'emailcfg'} = $$buz{'email'};
	} elsif (!defined ($buz = $Configs{$_[0]}))
	{	# email
		defined ($buz = get_bugzilla_for_window($win))
			or return error('First connect to a Bugzilla');
		$$buz{'email'} = shift;
	} elsif (!defined $$buz{'email'})
	{	# alias, config missing email
		return ask("Your e-mail address to login with",
			sub { cmd_login($win, $buz, shift) });
	}

	$newbuz = get_bugzilla_for_window($win);
	$newbuz = !defined $newbuz || $newbuz != $buz;

	revive_bugzilla($buz);
	ask_secret('Bugzilla password', sub
	{
		my ($done, @args);

		$done = $newbuz
			? sub { new_connection($win, $buz) }
			: sub { $win->printq("Logged in at $$buz{'url'}",
				MSGLEVEL_CLIENTNOTICE) };
		@args = (\&xmlreq, $$buz{'lwp'},
			"$$buz{'url'}/xmlrpc.cgi", 'User.login',
			login    => $$buz{'email'},
			password => shift,
			$done, undef);
		$newbuz ? single($win, @args)
			: enqueue($win, $buz, @args);
	});
}
# ]]]

# DISCONNECT [[[
#
# /BUG DISCO
# /BUG DISCONNECT
#	Ordered in a chat window disassociates it from its Bugzilla
#	connection.  In the status window it clears the default Bugzilla
#	association.  Otherwise if the current window is a bug window
#	it will be shut.
sub cmd_disco
{
	my ($win, $bug) = @_;

	if (delete $Bugzillas{$$win{'_irssi'}})
	{	# Chat window with its own association.
		cmd_unsniff($win);
		$win->print('Bugzilla disassociated', MSGLEVEL_CLIENTNOTICE);
	} elsif (defined $bug)
	{	# Bug window, window_destroyed() will clean up.
		$win->command('WINDOW CLOSE');
	} elsif (is_status_window($win))
	{
		undef $Default_Bugzilla;
		Irssi::print('Default Bugzilla forgotten');
	}
}
# ]]]
# ]]]

# View bugs [[[
# Print a bug [[[
# Print something without any prefix.
sub whisper
{
	@_ > 2 && pop()
		? shift->printformat(MSGLEVEL_NEVER, 'hi', @_)
		: shift->printq(@_, MSGLEVEL_NEVER);
}

# Format @_ with $fmt and print on $win.
sub forme
{
	my ($win, $fmt) = (shift, shift);
	local $^A = '';

	if (@_ != 1 || length($_[0]) <= $COLUMNS)
	{
		formline($fmt, @_);
	} else
	{	# Format multiple lines.  This is for long summaries.
		formline($fmt, $1) while $_[0] =~ /(.{0,$COLUMNS})/go;
	}

	whisper($win, $^A);
}

# Print '===' or '=== title ==='.  Highlight it if $hl.
sub print_divider
{
	my ($win, $title, $hl) = @_;

	if (defined $title)
	{
		my ($l, $c, $r);

		$c = 1+length($title)+1;
		$l = int(($COLUMNS  - $c) / 2);
		$r = $COLUMNS - ($l+$c);
		whisper($win, '=' x $l . " $title " . '=' x $r, $hl);
	} else
	{
		whisper($win, '=' x $COLUMNS, $hl);
	}
}

# Also used on attachments.
sub print_comment
{
	my ($win, $isfirst, $title, $who, $when, $comment) = @_;

	print_divider($win, $title, $isfirst);
	forme($win, $FORMAT_LR, $who, $when);
	whisper($win, '');
	whisper($win, $comment);
	whisper($win, '');
}

# Can print either an attachment or an array of attachments.
sub print_attachments
{
	my ($win, $files) = @_;
	my $n;

	print_comment($win, !defined $n, 'attachment ' . $n++,
			$$_{'flags'}
				? "$$_{'filename'} ($$_{'flags'})"
				:  $$_{'filename'},
			@$_{qw(date desc)})
		foreach ref($files) eq 'ARRAY' ? @$files : $files;
}

# "alpha" => "Mercury",
# "beta"  => "Venus"
#         ||
#         vv
# |alpha: Mercury|
# |beta:  Venus  |
sub txtblock
{
	my (@ary, $maxfield, $maxvalue);

	while (@_)
	{
		my ($field, $value) = (shift, shift);
		my $len;

		$field .= ": ";
		$len = length($field);
		defined $maxfield && $maxfield >= $len
			or $maxfield = $len;

		defined $value
			or $value = '';
		$len = length($value);
		defined $maxvalue && $maxvalue >= $len
			or $maxvalue = $len;

		push(@ary, [ $field, $value ]);
	}

	return map($$_[0] . ' ' x ($maxfield - length($$_[0]))
		.  $$_[1] . ' ' x ($maxvalue - length($$_[1])), @ary);
}

# [ a1, a2, a3, ... ], [ b1, b2, b3, ... ] => a1, b1, a2, b2, a3, b3, ...
# (maybe unzip() is not the correct name)
sub unzip
{
	my @bary;

	for (;;)
	{
		my ($n, @ary);

		foreach (@_)
		{
			if (@$_)
			{
				$n |= 1;
				push(@ary, shift(@$_));
			} else
			{
				push(@ary, '');
			}
		}

		last if !$n;
		push(@bary, \@ary);
	}

	return @bary;
}

# Actually it should be called print_bag() because it prints bags not bugs.
sub print_bug
{
	my ($win, $bag) = @_;
	my (@kdb, @heading, $comment, $n);

	# The rest of the fields are printed in two columns but these
	# must come on their own lines because they can be long and
	# truncating them they would lose significant information.
	push(@kdb, "Keywords"	=> $$bag{'keywords'})
		if defined $$bag{'keywords'};
	push(@kdb, "Depends on"	=> $$bag{'dependson'})
		if defined $$bag{'dependson'};
	push(@kdb, "Blocks"	=> $$bag{'blocked'})
		if defined $$bag{'blocked'};

	# Apply some maemo terminology.
	@heading = unzip(
		[ txtblock(
			"ID"		=> $$bag{'bug_id'},
			"Created"	=> $$bag{'creation_ts'},
			"Status"	=> $$bag{'bug_status'},
			"Severity"	=> $$bag{'bug_severity'},
			"Component"	=> $$bag{'product'},
			"Version"	=> $$bag{'version'},
			@kdb) ],
		[ txtblock(
			"Assigned to"	=> $$bag{'assigned_to'},
			"Modified"	=> $$bag{'delta_ts'},
			"Resolution"	=> $$bag{'resolution'},
			"Priority"	=> $$bag{'priority'},
			"Subcomponent"	=> $$bag{'component'},
			"TM"		=> $$bag{'target_milestone'}) ]);
	forme($win, $FORMAT_LR, @$_) foreach @heading[0..$#heading-@kdb/2];
	forme($win, $FORMAT_L,  @$_) foreach @heading[-@kdb/2..-1];

	whisper($win, '');
	forme($win, $FORMAT_C,	$$bag{'short_desc'});
	whisper($win, '');

	print_attachments($win, $$bag{'_ATTACHMENTS'})
		if defined $$bag{'_ATTACHMENTS'};

	return if !@{$$bag{'_COMMENTS'}};
	print_comment($win, !defined $n, 'comment ' . $n++,
			@$comment{qw(who bug_when thetext)})
		while defined ($comment = shift(@{$$bag{'_COMMENTS'}}));

	# Repeat the most important information at the bottom
	# so the user needn't scroll up.
	print_divider($win, undef, 1);
	forme($win, $FORMAT_LR, @$_) for @heading[0,2];
}
# ]]]

# OPEN [[[
# /BUG OPEN [<bugzilla>] <bug>
#	Opens <bug> (possibly of the <bugzilla>) in a new irssi window.
sub cmd_open
{
	my ($win, $buz, $bid, $auto) = @_;
	my ($url, $bug, $bugwin);

	return not_enough_arguments('open')
		if !defined $bid;

	$url = get_bug_url($buz, $bid);
	if (exists $Bugwins{$url} && Irssi::in_irssi())
	{	# $bid is open somewhere, find the window and activate it.
		# If the bug is opened explicitly (not by sniff()) switch
		# to the window.
		foreach $bugwin (Irssi::windows())
		{
			next if $$bugwin{'_irssi'} != $Bugwins{$url};
			$auto	? $bugwin->activity(2)
				: $win->command("WINDOW $$bugwin{'refnum'}");
			return;
		}

		# Bug is not open after all?
		delete $Bugwins{$url};
	}

	# Fetch the bug from $buz and show it in a new window.
	revive_bugzilla($buz);
	parallel($win, $buz, \&get_bug, $$buz{'lwp'}, $url, $HEAVY_BAG, sub
	{
		my $bag = shift;

		# Open a new bugwin and add the bug to $Bugs.
		$bugwin = new_window($win, $$bag{'short_desc'}, $bid, $auto);
		$bugwin->set_name('bugzilla');
		$Bugs{$$bugwin{'_irssi'}} =
		{
			buz	=> $buz,
			url	=> $url,
			bid	=> $$bag{'bug_id'},
			ts	=> $$bag{'delta_ts'},
			token	=> $$bag{'token'},
			files	=> $$bag{'_ATTACHMENTS'},
		};
		$Bugwins{$url} = $$bugwin{'_irssi'};

		print_bug($bugwin, $bag);
	}, undef);
}
# ]]]

# RELOAD [[[
#
# /BUG RELOAD
#	Clear the current window and reload its bug.
sub cmd_reload
{
	my ($win, $buz, $bug) = @_;

	parallel($win, $buz, \&get_bug, $$buz{'lwp'}, $$bug{'url'},
		$HEAVY_BAG,
	sub
	{
		my $bag = shift;

		$win->command("SCROLLBACK CLEAR");
		print_bug($win, $bag);
		$win->activity(1);
		# TODO Should refresh the status bar text too.
		refresh_bug($bug, $bag);
	}, undef);
}
# ]]]

# SUMMARY [[[
#
# /BUG SUM
# /BUG SUMMARY
#	Refresh and show the summary of the bug of the active bugwin.
# /BUG SUMMARY [<bugzilla>] <bug>
#	Show the summary of <bug> (of <bugzilla>) in the active window.
sub cmd_summary
{
	my ($win, $buz, $bug) = @_;

	if (!defined $bug)
	{
		return not_enough_arguments('summary');
	} elsif (!ref $bug)
	{
		$bug =~ /^\d+$/
			or error("Not a bug number");
		$bug = { url => get_bug_url($buz, $bug) };
	}

	revive_bugzilla($buz);
	single($win, \&get_bug, $$buz{'lwp'}, $$bug{'url'}, $NORMAL_BAG,
	sub
	{
		my $bag = shift;
		refresh_bug($bug, $bag);
		print_divider($win, undef, 1);
		print_bug($win, $bag);
	}, undef);
}
# ]]]

# BROWSE [[[
#
# /BUG BROWSE [[<bugzilla>] <bug>] [#<comment>]
#	Show <bug> or the bug in the current window in a WWW browser
#	and jump to <comment> if specified.  If <bugzilla> is also
#	given look up the bug there.
sub cmd_browse
{
	my ($win, $buz, $bug, $comment) = @_;
	my $url;

	die 'marha' if !defined $bug;
	$url = ref $bug ? $$bug{'url'} : get_bug_url($buz, $bug);
	if (defined $comment)
	{
		$comment =~ /^#[0-9]+$/
			or return error("Not a comment number");
		$comment =~ s/^#/#c/;
		$url .= $comment;
	}

	browse($url);
}
# ]]]
# ]]]

# Getting bug attachments [[[
# Return "$dir/$fname" sanitized.
sub mkpath
{
	my ($dir, $fname) = @_;
	my $path;

	# Remove "//"s and "./"s.
	return $fname if !length($dir);
	$path = "$dir/$fname";
	$path =~ s!/{2,}!/!;
	$path =~ s!^(?:\./)+!!;
	$path =~ s!/\./!/!g;
	return $path;
}

# /BUG ATTACHMENT
#	Show all attachments of the current bug.
# /BUG ATTACHMENT [<attachment>]
#	Only show information about <attachment>.
# /BUG ATTACHMENT URL <attachment>
#	Print the direct download URL of <attachment>.
# /BUG ATTACHMENT CAT <attachment>
#	Open a new window and show <attachment> there.
# /BUG ATTACHMENT GET <attachment>
#	Download <attachment>.
sub cmd_attachment
{
	my ($win, $buz, $bug, $cmd) = (shift, shift, shift, shift);
	my ($atch, $url);

	# Show attachment information?
	if (!defined $cmd)
	{
		print_attachments($win, $$bug{'files'});
		return;
	} elsif ($cmd =~ /^\d+$/)
	{
		return error("No such attachment")
			if $cmd >= @{$$bug{'files'}};
		print_attachments($win, $$bug{'files'}[$cmd]);
		return;
	}

	# URL/GET/CAT
	if (!defined ($atch = shift))
	{
		return not_enough_arguments('files');
	} elsif ($atch !~ /^\d+$/)
	{
		return error('Not an attachment number');
	} elsif ($atch >= @{$$bug{'files'}})
	{
		return error('No such attachment');
	}
	$atch = $$bug{'files'}[$atch];
	$url  = "$$buz{'url'}/attachment.cgi?id=$$atch{'attachid'}";

	if ($cmd =~ /^URL$/i)
	{	# Tell the attachment's URL.
		$win->printq($url);
	} elsif ($cmd =~ /^CAT$/i)
	{
		single($win, \&xmlrep,
			$$buz{'lwp'}, $url, Boogie::FileSaver->new(),
			sub { whisper(new_window($win, $$atch{'desc'},
				$$atch{'attachid'}, 0), shift) },
			sub { error(shift) });
	} elsif ($cmd =~ /^GET$/i) # [[[
	{	# Download attachment.
		my ($dir, $path);

		# Ask the user where to save the attachment.
		# The default is $path, which would save to
		# the directory where the previous attachment
		# was saved.
		(($dir) = read_setting("savedir"))
			or $dir = '.';
		$path = mkpath($dir, $$atch{'filename'});

		ask("Save to $path?", sub
		{
			my $ans = shift;
			my $out;

			# DWIM with the user's $ans:
			# "---"			=> cancel
			# <empty>		=> $path
			# <file name>		=> $dir/$$atch{'filename'}
			# <existing directory>	=> <*>/$$atch{'filename'}
			# <*/>			=> mkdir(<*>); -"-
			# <*/*>			=> accept as it is

			$ans =~ s/^\s+//;
			$ans =~ s/\s+$//;
			if ($ans eq '---')
			{	# Cancelled.
				return;
			} elsif (-d $ans)
			{	# Existing directory
				$dir = $ans;
				$path = mkpath($dir, $$atch{'filename'});
			} elsif ($ans =~ m{/$})
			{	# Create directory.
				$dir = $ans;
				mkdir($dir) or return error("$dir: $!");
				$path = mkpath($dir, $$atch{'filename'});
			} elsif ($ans =~ m{^(.*)/})
			{	# Complete path
				$dir = $1;
				$path = $ans;
			} elsif (length($ans))
			{	# File name
				$path = mkpath($dir, $ans);
			} else	# Empty
			{	# Accept default.
				undef $dir;
			}

			# Err out right now if we can't create the file.
			ref ($out = Boogie::FileDumper->new($path))
				or return error("$path: $out");

			# Update "savedir" for future downloads.
			write_setting("savedir", $dir)
				if defined $dir;

			# Download $url.
			single($win, \&xmlrep,
				$$buz{'lwp'}, $url, $out,
				sub { Irssi::print("Download of $path completed") },
				sub { error("$path: " . shift) });
		});
		# ]]]
	} else
	{
		error("Unknown subcommand");
	}
}
# ]]]

# Checking a bug's history [[[
#
# Print the history of a bug, who changed what field and when.
# Making comments and adding attachments are not listed.
#
# /BUG NEWS -all  [<who>]
#	Print all the bug's history.  You can restrict the listing
#	to changes made by a specific person (substring).
# /BUG NEWS -<n>  [<who>]
#	List the last <n> changes.
# /BUG NEWS -<n>d [<who>]
#	List changes made the last <n> days.  `-0' means `today',
#	`-1' is for `yesterday and today' and so on.
# /BUG NEWS       [<who>]
#	List unseen changes, ie. those made after you last RELOADed
#	the bug or changed it in any way.
sub cmd_news
{
	my ($win, $buz, $bug, $since) = (shift, shift, shift, @_);
	my ($only, $who);

	# Print activities $since...?
	if (!defined $since)
	{
		$since = str2time($$bug{'delta_ts'});
	} elsif ($since eq '-all')
	{
		$since = 0;
		shift;
	} elsif ($since =~ /^-(\d+)d$/)
	{	# Today counts as a whole day.
		$since  = mktime(0, 0, 0, (localtime(time))[3..8]);
		$since -= ($1-1)*24*60*60 if $1 > 0;
		shift;
	} elsif ($since =~ /^-(\d+)$/)
	{
		$only = $1;
		undef $since;
		shift;
	} elsif ($since =~ /^-/)
	{
		error("Invalid time specification");
		return;
	}

	# Print activities by ...?
	$who = shift;
	$who = qr/\Q$who\E/i if defined $who;

	get_activity($$buz{'lwp'},
		get_bug_url($buz, $$bug{'bid'}, 'activity'), sub
	{
		my $activities = shift;

		# Filter out the important @$activities.
		@$activities = grep($$_[1] =~ $who, @$activities)
			if defined $who;

		if (defined $since)
		{
			@$activities = grep(str2time($$_[0]) > $since,
				@$activities);
		} elsif ($only < @$activities)
		{
			@$activities = @$activities[-$only..-1]
		}

		if (!@$activities)
		{
			$win->print('No news');
			return;
		}

		foreach (@$activities)
		{
			print_divider($win,
				$_ == $$activities[0] ? ('History', 1) : ());
			forme($win, $FORMAT_LR,
				shift(@$_), shift(@$_));
			whisper($win, '');
			whisper($win, shift(@$_));
			whisper($win, '');
		}
	});
}
# ]]]

# Finding bugs [[[
# Constants [[[
# Inverse of @SMALL_BAG, mapping names to indices.
my %SMALL_BAG_MAP = map(($$SMALL_BAG[$_] => $_), 0..$#$SMALL_BAG);

# Lists valid /BUG SEARCH parameters and their canonical forms.
my %VALID_CRITERIA =
(
	'-kw'		=> '-keywords',
	'-wb'		=> '-whiteboard',
	'-prio'		=> '-priority',
	'-svr'		=> '-severity',
	'-prog'		=> '-program',
	'-comp'		=> '-component',
	'-subcomp'	=> '-subcomponent',
	'-mine'		=> '-assigned-to',
	'-assignee'	=> '-assigned-to',
	'-reporter'	=> '-reporter-by',
	'-sort'		=> '-order',
);

$VALID_CRITERIA{$_} = $_
	for (values(%VALID_CRITERIA),
		qw(-bugs -lastmod -summary),
		qw(-all -open -fixed),
		qw(-qa -cc -commenter -who));

# The same for -sort keys.
my %VALID_SORTING =
(
	'stat'		=> 'status',
	'imp'		=> 'importance',
	'prio'		=> 'priority',
	'svr'		=> 'severity',
	'comp'		=> 'component',
	'tm'		=> 'TM',
);

$VALID_SORTING{$_} = $_
	for ('lastmod', values(%VALID_SORTING));

# Maps /BUG SEARCH parameters to Bugzilla search fields.
my %CRITERIUM2BUGZILLA =
(
	'-bugs'		=>
	[
		bugidtype	=> 'include',
		bug_id		=> # actual value
	],
	'-not-bugs'	=>
	[
		bugidtype	=> 'exclude',
		bug_id		=> # actual value
	],
	'-lastmod'	=>
	[
		'field0-0-0'	=> 'days_elapsed',
		'type0-0-0'	=> 'lessthan',
		'value0-0-0'	=> # actual value
	],
	'-summary'	=>
	[
		short_desc_type	=> 'anywordssubstr',
		short_desc	=> # actual value
	],
	'-keywords'	=>
	[
		keywords_type	=> 'anywords',
		keywords	=> # actual value
	],
	'-open'		=> 'bug_status',
	'-fixed'	=> 'bug_status',
	'-priority'	=> 'priority',
	'-severity'	=> 'bug_severity',
	'-program'	=> 'classification',
	'-component'	=> 'product',
	'-subcomponent'	=> 'component',
	'-assigned-to'	=> 'emailassigned_to1',
	'-reported-by'	=> 'emailreporter1',
	'-qa'		=> 'emailqa_contact1',
	'-cc'		=> 'emailcc1',
	'-commenter'	=> 'emaillongdesc1',
	'-sort'		=> 'order',
);

my %SORTING2BUGZILLA =
(
	lastmod		=> 'bugs.delta_ts',
	status		=> 'bugs.bug_status,bugs.resolution',
	importance	=> 'bugs.priority,bugs.bug_severity',
	priority	=> 'bugs.priority',
	severity	=> 'bugs.bug_severity',
	component	=> 'map_classifications.name,map_products.name,map_components.name',
	tm		=> 'bugs.target_milestone',
);
# ]]]

# Returns whether $ary1 contains all strings in $ary2.
sub issubset
{
	my ($ary1, $ary2) = @_;
	my %hash2;

	%hash2 = map(($_ => undef), @$ary2);
	exists $hash2{$_} or return 0
		foreach @$ary1;
	return 1;
}

sub cmd_search
{
	my ($win, $buz) = (shift, shift);
	my ($show_url, $browse, $newin, $not);
	my (%criteria, $old_crit, @fields, $query, $and);

	# Some constants first. [[[
	my @states	= qw(-all -open -fixed);
	my @users	= qw(-assigned-to -reported-by -qa -cc -commenter);
	my %whos	= map($_ => $VALID_CRITERIA{"-$_"},
				qw(assignee reporter qa cc commenter));
	my @nullary	= (@states, '-mine');
	my @unary	= qw(-lastmod);
	my @negatable	= qw(-bugs -whiteboard);
	# ]]]

	# Parse the command arguments and fill in %criteria. [[[
	$old_crit = { };
	while (@_)
	{
		my ($arg, $crit, $val);
		my (@cgrp, $old_val);

		$arg = shift;
		if ($arg eq '-url')
		{	# Print the buglist URL.
			$show_url = 1;
			next;
		} elsif ($arg eq '-browse')
		{	# Open the buglist in a browser.
			$browse = 1;
			next;
		} elsif ($arg eq '-new')
		{	# Open results in a new window.
			$newin = 1;
			next;
		} elsif ($arg eq '-not')
		{	# Negate the next criterium.
			$not = 2*!$not;
			next;
		}

		# Get $val, $crit.  Check $arg being @nullary because
		# $VALID_CRITERIA translates -mine to -assigned-to,
		# which is not.
		($val) = $arg =~ s/=(.*)$//;
		defined ($crit = $VALID_CRITERIA{$arg})
			or return error("$arg: unknown criterium");
		not $not or grep($crit eq $_, @negatable)
			or return error("$crit cannot be negated");
		not (defined $val && grep($arg eq $_, @nullary))
			or return error("$arg doesn't take parameters");

		# These criteria don't take parameters.
		if ($crit eq '-all')
		{	# Bugs with status.
			delete @$old_crit{@states};
			delete @criteria{@states};
			$criteria{$crit} = 1;
			next;
		} elsif ($crit eq '-open' || $crit eq '-fixed')
		{	# Unfixed bugs; Resolved but unreleased bugs.
			delete @$old_crit{@states};
			delete $criteria{'-all'};
			$criteria{$crit} = 1;
			next;
		}

		# These criteria (assignee, reporter, ...) may take an email
		# parameter to designate the subject.  If this parameter is
		# given it must be specified together with the criterium,
		# like -crit=email.
		if (grep($crit eq $_, @users))
		{
			if (defined $val && $val eq 'ANY')
			{	# Remove just this $crit.
				delete $$old_crit{$crit};
				next;
			} elsif (!defined $criteria{'EMAIL'})
			{
				# Store it in $criteria even if $val is
				# not defined.  We will know then to use
				# the current user's email.
				$criteria{'EMAIL'} = $val;
			} elsif (defined $val && $criteria{'EMAIL'} eq $val)
			{
				error('At most one email can be specified');
				return;
			}

			delete @$old_crit{@users, 'EMAIL'};
			$criteria{$crit} = 1;
			next;
		}

		# The rest of the criteria take a mandatory parameter.
		# Take the next argument if $val wasn't specified with $arg.
		defined $val
			or defined ($val = shift)
			or return not_enough_arguments('search');

		# Handle -who on its own because it sets all of @users.
		if ($crit eq '-who')
		{
			if ($val eq 'ANY')
			{	# But don't remove {'EMAIL'}.
				delete @$old_crit{@users};
				delete @criteria{ @users};
			} elsif ($val !~ s/^\+//)
			{	# Override $old_crit{@users}.
				delete @$old_crit{@users};
			}

			foreach (split(/,\s*/, $val))
			{
				return error("-who $_: invalid parameter")
					if !$whos{$_};
				$criteria{$VALID_CRITERIA{$_}} = 1;
			}

			next;
		}

		# Remove criterium?
		if ($val eq 'ANY')
		{	# Invalidate -not-... as well.
			error('-not ANY does not make sense') if $not;
			delete @$old_crit{$crit, "-not$crit"};
			next;
		}

		# Find criterium groups, the set of criteria which
		# should be replaced by $val.
		@cgrp = ($crit);
		grep($crit eq $_, @$_) and @cgrp = @$_ and last
			foreach ([qw(-bugs -not-bugs)],
				 [qw(-whiteboard -not-whiteboard)],
				 [qw(-program -component -subcomponent)]);

		# Invalidate $old_crit, but preserve it if the new value
		# is an addition, unless the criterium can only take a
		# single parameter.
		if (!grep($crit eq $_, @unary) && $val =~ s/^\+//
			&& defined ($old_val = delete $$old_crit{$crit}))
		{	# Copy $old_val from $old_crit, but don't touch
			# the rest of @cgrp.
			push(@{$criteria{$crit}}, @$old_val);
		} else
		{
			delete @$old_crit{@cgrp};
		}

		# Add new $val.
		if ($crit eq '-sort')
		{	# Validate $val first.
			foreach (split(/,\s*/, $val))
			{
				return error("$_: invalid -sort key")
					if !exists $VALID_SORTING{$_};
				push(@{$criteria{$crit}},
					$VALID_SORTING{$_});
			}
		} elsif (!grep($crit eq $_, @unary))
		{	# Split $val.
			push(@{$criteria{$crit}}, split(/,\s*/, $val));
		} else
		{	# Accept $val as is.
			push(@{$criteria{$crit}}, $val);
		}

		push(@{$criteria{$crit}}, grep($crit eq $_, @unary)
			? $val : split(/,\s*/, $val));
	} continue
	{	# Forget $not.
		$not-- if $not;
	}
	# ]]]

	# Finished parsing the command line, finalize %criteria. [[[
	# Check that a single operation is requested.
	! ! $show_url + ! ! $browse + ! ! $newin <= 1
		or return error('-url, -browse and -new are mutex');

	# Merge the window's previous criteria.
	$criteria{$_} = $$old_crit{$_}
		foreach keys(%$old_crit);

	# Remove EMAIL if no @users criteria given.
	delete $criteria{'EMAIL'}
		if exists $criteria{'EMAIL'}
		&& !grep($_, map(exists $criteria{$_}, @users));

	# Make EMAIL=ME mean the current user.
	defined $criteria{'EMAIL'} && $criteria{'EMAIL'} eq 'ME'
		and undef $criteria{'EMAIL'};

	# Maybe it would make a little sense, but Bugzilla cannot
	# handle it anyway.
	$criteria{'-bugs'} && $criteria{'-not-bugs'}
		and return error('-bugs and -not -bugs are mutex');

	# Refuse to bombard a Bugzilla with a request for all bugs.
	return error('Empty query')
		if !%criteria || !grep(!/^-not-/, keys(%criteria));

	# Set defaults.
	$criteria{'-all'} || $criteria{'-open'} || $criteria{'-fixed'}
		or $criteria{'-open'} = 1;
	$criteria{'-sort'}
		or $criteria{'-sort'} =
			[ qw(status importance component lastmod) ];
	# ]]]

	# Turn the final search %criteria into Bugzilla query @fields. [[[
	$and = 0;
	foreach my $crit (keys(%criteria))
	{
		my $field = $CRITERIUM2BUGZILLA{$crit};
		ref $field or $field = [ $field ];
		if ($crit eq '-bugs' || $crit eq '-not-bugs')
		{	# These expect a comma-separated list.
			push(@fields, @$field =>
				join(',', @{$criteria{$crit}}));
		} elsif ($crit eq '-summary')
		{	# And this a while-space separated one.
			push(@fields, @$field =>
				join(' ', @{$criteria{$crit}}));
		} elsif ($crit eq '-whiteboard')
		{
			my (@substr, @words, $or, $chart);

			# Whiteboard search is special because the terms
			# may include spaces, in which case we need to
			# search for a substring.  Separate these two
			# types of terms from each other.
			push(@{/ / ? \@substr : \@words}, $_)
				foreach @{$criteria{$crit}};
			$or = 0;

			# ... AND (substring OR substring OR ...)
			foreach (@substr)
			{
				$chart = join('-', 0, $and, $or++);
				push(@fields,
					"field$chart" => 'status_whiteboard',
					"type$chart"  => 'substring',
					"value$chart" => $_);
			}

			# ... AND (anywords) ...
			if (@words)
			{
				$chart = join('-', 0, $and, $or++);
				push(@fields,
					"field$chart" => 'status_whiteboard',
					"type$chart"  => 'anywords',
					"value$chart" => join(' ', @words));
			}

			$and++;
		} elsif ($crit eq '-not-whiteboard')
		{
			my (@substr, @words, $chart);

			push(@{/ / ? \@substr : \@words}, $_)
				foreach @{$criteria{$crit}};

			# ... AND (notsubstring) AND (notsubstring) ...
			foreach (@substr)
			{
				$chart = join('-', 0, $and++, 0);
				push(@fields,
					"field$chart" => 'status_whiteboard',
					"type$chart"  => 'notsubstring',
					"value$chart" => $_);
			}

			# ... AND (nowords) ...
			if (@words)
			{
				$chart = join('-', 0, $and++, 0);
				push(@fields,
					"field$chart" => 'status_whiteboard',
					"type$chart"  => 'nowords',
					"value$chart" => join(' ', @words));
			}
		} elsif ($crit eq '-all')
		{	# NOP
		} elsif ($crit eq '-open')
		{
			push(@fields, @$field => $_)
				for qw(UNCONFIRMED NEW ASSIGNED REOPENED);
		} elsif ($crit eq '-fixed')
		{
			push(@fields, @$field => 'RESOLVED');
		} elsif ($crit eq 'EMAIL' && defined $criteria{'EMAIL'})
		{	# Allow for abbreviations in case of
			# user-specified emails.
			push(@fields,
				emailtype1	=> 'substring',
				email1		=> $criteria{'EMAIL'});
		} elsif ($crit eq 'EMAIL' && exists $criteria{'EMAIL'})
		{
			my $email;

			# Match it exactly, since we know the exact value.
			defined ($email = $$buz{'email'})
				or defined ($email = $$buz{'emailcfg'})
				or return error('Set your Bugzilla user');
			push(@fields,
				emailtype1	=> 'exact',
				email1		=> $email);
		} elsif ($crit eq '-sort')
		{
			push(@fields, $criteria{$crit}, join(',',
				@SORTING2BUGZILLA{@{$criteria{$crit}}}));
		} elsif (ref $criteria{$crit})
		{	# Multivalue-field.
			push(@fields, @$field => $_)
				foreach @{$criteria{$crit}};
		} else
		{	# Unary field.
			push(@fields, @$field => $criteria{$crit});
		}
	}
	# ]]]

	# Take action. [[[
	# Create the $query and $show_url or $browse it...
	$query = URI->new("$$buz{'url'}/buglist.cgi");
	$query->query_form(@fields);
	return $win->printq($query) if $show_url;
	return browse($query) if $browse;

	# ...or do the search.
	parallel($win, $buz, \&get_bugs, $$buz{'lwp'}, $query, $SMALL_BAG,
	sub
	{
		my $bags = shift;
		my ($now, @lengths, $fmt1, $fmt2);

		# The first row of the reply should be the field list
		# which should contain all the fields we asked for and
		# tells us the order of the columns in the rest of the
		# rows.
		$now = time();
		return error('Nonsense Bugzilla reply') if !@$bags;
		return error('Nonsense Bugzilla reply')
			if !issubset($SMALL_BAG, shift(@$bags));
		foreach (@$bags)
		{
			# Create the display columns of the list:
			# bug_id svr/prio/tm status comp/subcomp lastmod
			my $secs = ($now-str2time(
				$$_[$SMALL_BAG_MAP{'changeddate'}]));
			$_ = [ $$_[$SMALL_BAG_MAP{'bug_id'}],
				join('/', @$_[@SMALL_BAG_MAP{
					qw(bug_severity priority
						target_milestone)}]),
				$$_[$SMALL_BAG_MAP{'resolution'}]
					|| $$_[$SMALL_BAG_MAP{'bug_status'}],
				join('/', @$_[@SMALL_BAG_MAP{
					qw(product component)}]),
				int($secs / (24*60*60))."d",
				$$_[$SMALL_BAG_MAP{'short_desc'}] ];
			for my $i (0..$#$_)
			{	# Find the widest of the fields.
				my $len = length($$_[$i]);
				defined $lengths[$i] && $lengths[$i] >= $len
					or $lengths[$i] = $len;
			}
		}

		# Create the output formats so that the fields will be
		# aligned nicely.
		$lengths[3]  = $COLUMNS;
		$lengths[3] -= $lengths[$_]+1 for (0, 1, 2, 4);
		$lengths[5]  = $COLUMNS - ($lengths[0]+1);
		$fmt1 = join(' ', map('@'.'<'x($_-1), @lengths[0..3]),
			'@'.'>'x($lengths[4]-1));
		$fmt2 = ' 'x($lengths[0]+1) . '@' . '<'x($lengths[5]-1);

		# Print the list.
		foreach (@$bags)
		{
			forme($win, $fmt1, @$_);
			forme($win, $fmt2, $$_[5]);
		}
	}, undef);
	# ]]]
}
# ]]]

# Sniffing [[[
# SNIFF [[[
#
# Public and private message handler to catch Bugzilla references
# in the conversation and open bugwins.
sub sniff
{
	my ($srv, $msg, $nick, $addr, $target) = @_;
	my ($win, $buz);

	$win = defined $target
		? $srv->channel_find($target)->window()
		: $srv->query_find($nick)->window();
	return if !$Sniffs{$$win{'_irssi'}};

	if (!defined ($buz = get_bugzilla_for_window($win)))
	{	# $win must have been disassociated.
		cmd_unsniff($win);
		return;
	}

	if (!defined $$buz{'rex'})
	{
		# Catch show_bug URLs, prefixed bug numbers and long numbers,
		# which are possibly bug numbers, but only if they are not
		# tails of other URLs.
		local $" = "|";
		my @rexes =
		(
			qr{\Q$$buz{'url'}/show_bug.cgi?id=\E(\d+)},
			map(qr{\b\Q$_\E(\d+)}, @{$$buz{'prefixes'}}),
			qr{\b\w+://\S+}, qr{\b(\d{5,})\b},
		);
		$$buz{'rex'} = qr/(?:@rexes)/;
	}

	# Open all bids we find in $msg.
	defined $+ and !$Blacklisted{get_bug_url($buz, $+)}
			and cmd_open($win, $buz, $+, 1)
		while $msg =~ /$$buz{'rex'}/g;
}

# Let sniff() see all messages in all windows.
sub install_sniffer
{
	Irssi::signal_add('message public',  "sniff");
	Irssi::signal_add('message private', "sniff");
}

# /BUG SNIFF
#	Start watching the conversation for Bugzilla references.
#	When a reference is caught open the bug in a new window,
#	or highlight the window if it's already open.  Recognized
#	references are bug URLs, prefixed numbers or numbers with
#	5 or more digits.
# /BUG BLACKLIST
#	Close this bugwin and don't open it again when sniffing.
#	You can still OPEN it manually, though.  The blacklist is
#	not stored permanently.
# /BUG UNBLACKLIST
#	Notice this bug again when sniffing.
sub cmd_sniff
{
	my $win = shift;

	install_sniffer() if !%Sniffs;
	$Sniffs{$$win{'_irssi'}} = 1;
	$win->print("Sniffing for bug numbers");
}
# ]]]

# UNSNIFF [[[
#
# /BUG UNSNIFF
#	Stop watching for Bugzilla references.
sub cmd_unsniff
{
	my $win = shift;

	delete $Sniffs{$$win{'_irssi'}}
		or return;
	$win->print("Not sniffing anymore");
	if (!%Sniffs)
	{
		Irssi::signal_remove('message public',  \&sniff);
		Irssi::signal_remove('message private', \&sniff);
	}
}
# ]]]
# ]]]

# Change bugs [[[
# common code [[[
# Collect comments required for a bug change either from the command line
# or prompt for them then run $next.
sub get_comments
{
	my ($win, $prompt) = (shift, shift);
	my $next = pop;

	if (@_)
	{
		&$next(join(' ', @_));
	} else
	{	# Collect the speech then rerun.
		speech($win, $prompt, $next);
	}
}

# Change the @$fields properties of a bug, such as summary (short_desc),
# priority and so on.  When finished successfullly prints the current
# properties to $win.
sub change_bug_properties
{
	my ($win, $buz, $bug, $fields) = @_;

	parallel($win, $buz, \&change_bug, $bug, 0, $fields,
		sub { cmd_summary($win, $buz, $bug) }, undef);
}
# ]]]

# RENAME [[[
#
# /BUG RENAME <summary>
#	Changes the current bug's summary.
sub cmd_rename
{
	my ($win, $buz, $bug) = (shift, shift, shift);

	return not_enough_arguments('rename') if !@_;
	change_bug_properties($win, $buz, $bug,
		[ short_desc => join(' ', @_) ]);
}
# ]]]

# TUNE [[[
#
# /BUG TUNE [-tm <TM>] [-prio[rity] <prio>] [{-severity|-svr} <severity>]
#	Changes the current bug's severity/priority/target milestone.
#	Make sure the TM is valid, otherwise it may be reset to none
#	on Bugzilla 3.0.
sub cmd_tune
{
	my ($win, $buz, $bug) = (shift, shift, shift);
	my (@fields, $param, $value);

	while (defined ($param = shift))
	{
		if (!defined ($value = shift))
		{
			return error("$param left without value");
		} elsif ($param eq '-tm')
		{
			push(@fields, target_milestone => $value);
		} elsif ($param eq '-priority' || $param eq '-prio')
		{
			push(@fields, priority => $value);
		} elsif ($param eq '-severity' || $param eq '-svr')
		{
			push(@fields, bug_severity => $value);
		} else
		{
			return error("Unrecognized bug parameter");
		}
	}

	return error("Nothing to change") if !@fields;
	change_bug_properties($win, $buz, $bug, \@fields);
}
# ]]]

# TAKE [[[
#
# /BUG TAKE [-assign] [<comment>]
#	Reassign the bug to you and optionally set its status to ASSIGNED.
#	If you don't provide a comment boogie will add one for you.
#	Bugzilla 3.0 cannot change the assignee and the bug status at the
#	same time and -assign takes precedence then.
sub cmd_take
{
	my ($win, $buz, $bug) = (shift, shift, shift);
	my @fields;

	return error("No user id defined for this Bugzilla")
		if !defined $$buz{'email'};
	@fields = (assigned_to => $$buz{'email'});

	if (@_ && $_[0] eq '-assign')
	{
		shift;
		push(@fields, knob => 'accept', bug_status => 'ASSIGNED');
	} else
	{	# Make ourselves Bugzilla 3.0 friendly.
		push(@fields, knob => 'reassign');
	}

	push(@fields, comment => @_ ? join(' ', @_) : 'taken');

	change_bug_properties($win, $buz, $bug, \@fields);
}
# ]]]

# RESOLVE [[[
#
# /BUG RESOLVE [-tm <TM>] <resolution> [<comment>]
#	Mark the current bug resolved.  You may have to provide a TM.
#	Commentary is required.
sub cmd_resolve
{
	my ($win, $buz, $bug) = (shift, shift, shift);
	my @fields;

	return not_enough_arguments('resolve') if !@_;
	if ($_[0] eq '-tm')
	{
		shift;
		return not_enough_arguments('resolve') if !@_;
		push(@fields, target_milestone => shift);
		return not_enough_arguments('resolve') if !@_;
	}

	push(@fields,
		knob		=> 'resolve',
		bug_status	=> 'RESOLVED',
		resolution	=> shift);

	get_comments($win, 'comment', @_, sub
	{
		change_bug_properties($win, $buz, $bug,
			[ @fields, comment => shift ]);
	});
}
# ]]]

# REOPEN [[[
#
# /BUG REOPEN [<comment>]
#	Reopen the current bug.  You have to provide an explanation.
sub cmd_reopen
{
	my ($win, $buz, $bug) = (shift, shift, shift);

	get_comments($win, 'comment', @_, sub
	{
		change_bug_properties($win, $buz, $bug,
		[
			knob		=> 'reopen',
			bug_status	=> 'REOPENED',
			comment		=> shift,
		]);
	});
}
# ]]]

# WTF [[[
#
# /BUG WTF [<comment>]
#	Ask a NEED_INFO question from the reporter.
#	May not be supported by the Bugzilla installation.
sub cmd_wtf
{
	my ($win, $buz, $bug) = (shift, shift, shift);

	get_comments($win, 'comment', @_, sub
	{
		change_bug_properties($win, $buz, $bug,
			[ knob => 'need_info', comment => shift ]);
	});
}
# ]]]

# FTW [[[
#
# /BUG FWT [<comment>]
#	Answer the NEED_INFO question.
sub cmd_ftw
{
	my ($win, $buz, $bug) = (shift, shift, shift);

	get_comments($win, 'comment', @_, sub
	{
		change_bug_properties($win, $buz, $bug,
			[ knob => 'confirm_and_reassign', comment => shift ]);
	});
}
# ]]]

# COMMENT [[[
#
# /BUG COMMENT [<comment>]
#	Makes <comment> on the current bug.  You can make a multiline
#	comment by omitting it from the command.
sub cmd_comment
{
	my ($win, $buz, $bug) = (shift, shift, shift);

	get_comments($win, 'comment', @_, sub
	{
		my $comment = shift;
		parallel($win, $buz, \&change_bug, $bug, 1,
			[ comment => $comment, ], sub
		{	# Assume we have an email if we were able to comment.
			print_comment($win, 0, undef, $$buz{'email'}, $$bug{'ts'},
				$comment);

			# Refresh the token and the timestamp if they
			# didn't come with the bug-processed reply.
			parallel($win, $buz, \&get_bug,
				$$buz{'lwp'}, $$bug{'url'}, $MINIMAL_BAG,
				sub { refresh_bug($bug, shift) }, undef)
				if !defined shift->{'ts'};
		}, undef);
	});
}
# ]]]
# ]]]

# The /BUG subcommand dispatcher [[[
# /BUG URL [#<comment>]
#	Print the URL of the current bug or one of its comments.
sub cmd
{
	my ($arg, $srv, $qry) = @_;
	my ($win, @args, $cmd, $buz, $bug);

	# Show help for a single "/BUG".
	@args = shellwords($arg);
	return error("Parse error (mismatched quotation marks?)")
		if !@args && $arg !~ /^\s*$/;
	return cmd_help() if !@args;

	# Check the validity of $cmd.
	$cmd = lc(shift(@args));
	return error("Unknown subcommand") unless grep($cmd eq $_,
		qw(help restart state
			server con conn connect login disco disconnect
			open reload sum summary news browse url
			attach attachment attachments
			sniff unsniff blacklist unblacklist
			search
			rename tune take resolve reopen wtf ftw comment));

	# These commands are valid whether $win is associated
	# with a Bugzilla or not.
	$win = Irssi::active_win();
	if ($cmd eq 'help')
	{
		return cmd_help(@args);
	} elsif ($cmd eq 'restart')
	{
		return cmd_restart($win, @args);
	} elsif ($cmd eq 'state')
	{
		return cmd_state($win, @args);
	} elsif ($cmd eq 'server')
	{
		return cmd_server($win, @args);
	} elsif ($cmd eq 'con' || $cmd eq 'conn' || $cmd eq 'connect')
	{
		return cmd_conn($win, @args);
	} elsif ($cmd eq 'login')
	{
		return cmd_login($win, @args);
	}

	# Handle 2-argument OPEN and BROWSE.
	if ($cmd eq 'open' && @args >= 2)
	{
		defined ($buz = $Configs{shift(@args)})
			or return error("No such configuration");
		return cmd_open($win, $buz, shift(@args));
	} elsif ($cmd =~ /^sum|summary$/ && @args >= 2)
	{	# /BUG SUMMARY <alias> <bid>
		defined ($buz = $Configs{shift(@args)})
			or return error("No such configuration");
		return cmd_summary($win, $buz, @args);
	} elsif ($cmd eq 'browse' && @args >= 2 && $args[1] !~ /^#/)
	{	# /BUG BROWSE <alias> <bid> [<comment>]
		defined ($buz = $Configs{shift(@args)})
			or return error("No such configuration");
		return cmd_browse($win, $buz, @args);
	}

	# The next commands require a Bugzilla association.
	(($buz, $bug) = get_bugzilla_for_window($win))
		or return error("Not connected to Bugzilla");
	if ($cmd eq 'disco' || $cmd eq 'disconnect')
	{
		return cmd_disco($win, $bug);
	} elsif ($cmd eq 'open')
	{
		return cmd_open($win, $buz, shift(@args));
	} elsif ($cmd eq 'sum' || $cmd eq 'summary')
	{
		unshift(@args, $bug) if !@args;
		return cmd_summary($win, $buz, @args);
	} elsif ($cmd eq 'browse')
	{
		unshift(@args, $bug) if !@args || $args[0] =~ /^#/;
		return cmd_browse($win, $buz, @args);
	} elsif ($cmd eq 'search')
	{
		return cmd_search($win, $buz, @args);
	} elsif ($cmd eq 'sniff')
	{
		return error("Can only sniff queries")
			if !$qry || $bug;
		return cmd_sniff($win);
	} elsif ($cmd eq 'unsniff')
	{
		return cmd_unsniff($win);
	}

	# Commands only valid in bugwins.
	return error("Command only valid in a bugwin")
		if !defined $bug;
	if ($cmd eq 'url')
	{
		if (!@args)
		{
			$win->printq($$bug{'url'});
		} elsif ($args[0] =~ /^#([0-9]+)$/)
		{
			$win->printq("$$bug{'url'}#c$1");
		} else
		{
			error("Not a comment number");
		}
	} elsif ($cmd eq 'reload')
	{
		cmd_reload($win, $buz, $bug);
	} elsif ($cmd eq 'sum' || $cmd eq 'summary')
	{
		return error("Bug cannot be specified") if @args;
		cmd_summary($win, $buz, $bug);
	} elsif ($cmd =~ /^attach(?:ment(?:s)?)?$/)
	{
		cmd_attachment($win, $buz, $bug, @args);
	} elsif ($cmd eq 'news')
	{
		cmd_news($win, $buz, $bug, @args);
	} elsif ($cmd eq 'blacklist')
	{
		$Blacklisted{$$bug{'url'}} = 1;
		$win->command('WINDOW CLOSE');
		Irssi::print("Bug blacklisted");
	} elsif ($cmd eq 'unblacklist')
	{
		delete $Blacklisted{$$bug{'url'}};
		$win->print("Bug unblacklisted");
	} elsif ($cmd eq 'rename')
	{
		cmd_rename($win, $buz, $bug, @args);
	} elsif ($cmd eq 'tune')
	{
		cmd_tune($win, $buz, $bug, @args);
	} elsif ($cmd eq 'take')
	{
		cmd_take($win, $buz, $bug, @args);
	} elsif ($cmd eq 'resolve')
	{
		cmd_resolve($win, $buz, $bug, @args);
	} elsif ($cmd eq 'reopen')
	{
		cmd_reopen($win, $buz, $bug, @args);
	} elsif ($cmd eq 'wtf')
	{
		cmd_wtf($win, $buz, $bug, @args);
	} elsif ($cmd eq 'ftw')
	{
		cmd_ftw($win, $buz, $bug, @args);
	} elsif ($cmd eq 'comment')
	{
		cmd_comment($win, $buz, $bug, @args);
	} else
	{
		error("Must be unimplemented");
	}
}
# ]]]
# ]]]

# Main [[[
# Called when any window is closed.
sub window_destroyed
{
	my $win = shift;
	my $bug;

	if (delete $Bugzillas{$$win{'_irssi'}})
	{
		cmd_unsniff($win);
	} elsif (($bug = delete $Bugs{$$win{'_irssi'}}))
	{
		delete $Bugwins{$$bug{'url'}};
	}
}

# Main starts here
# Make SSL + proxy usable with LWP.  This trick is Crypt::SSLeay's.
if (!exists $ENV{'HTTPS_PROXY'})
{
	if (exists $ENV{'https_proxy'})
	{
		$ENV{'HTTPS_PROXY'} = $ENV{'https_proxy'};
	} elsif (exists $ENV{'http_proxy'})
	{	# It's likely that both protocols are proxied.
		$ENV{'HTTPS_PROXY'} = $ENV{'http_proxy'};
	}
}

if (Irssi::in_irssi())
{
	my $state;

	# Restore our preserved state if we can.
	Irssi::settings_add_str('boogie', "boogie_state", 'UNSET');
	$state = Irssi::settings_get_str("boogie_state");
	if ($state ne 'UNSET')
	{
		delete_setting("state");
		eval $state;
		if ($@)
		{
			Irssi::print("Failed to carry on state ($@)");
			load_configs();
		} else
		{
			Irssi::print("State preserved");
			install_sniffer() if %Sniffs;
		}
	} else
	{
		load_configs();
		Irssi::print("See /BUG HELP for an overview");
	}

	Irssi::theme_register(['hi', '%8$0']);
	Irssi::signal_add('window destroyed', \&window_destroyed);
	Irssi::command_bind('bug', 'cmd');
}
# ]]]

# LWP::UserAgent for authentication popup [[[
package Boogie::LWP;
use strict;

our @ISA = qw(LWP::UserAgent);

sub new
{
	my ($pkg, $http_user) = @_;
	my $self;

	# Don't try to access https:// through LWPs proxying mechanism,
	# but let the lower layer deal with it.
	$self = LWP::UserAgent::new($pkg,
		env_proxy => 1, cookie_jar => { });
	delete $$self{'proxy'}{'https'};
	$$self{'boogie_http_user'} = $http_user
		if defined $http_user;

	return $self;
}

# freeze() and toast() are used by Data::Dumper when we try to carry on
# our state.  Return something that represents our current state.
sub freeze
{
	my $self = shift;

	# Prune everything but a few things.
	%$self = 
	(
		proxy	=> $$self{'proxy'},
		cookies => $self->cookie_jar()->{'COOKIES'},
		user	=> $$self{'boogie_http_user'},
	);

	return $self;
}

# Recreate a usable $self from the struct returned by freeze().
sub toast
{
	my $freezed_self = shift;
	my $living_self;

	# Reconstruate a new LWP::UserAgent object.
	$living_self = ref($freezed_self)->new($$freezed_self{'user'});
	$living_self->cookie_jar()->{'COOKIES'} = $$freezed_self{'cookies'}
		if defined $$freezed_self{'cookies'};
	$$living_self{'proxy'} = $$freezed_self{'proxy'};

	return $living_self;
}

# Base class overrides
sub get_basic_credentials
{
	@{shift()}{qw(boogie_http_user boogie_http_pass)}
}

sub prepare_request
{
	my ($self, $request) = (shift, shift);
	my $auth;

	# Save the Authorization: header so it will always be available
	# in $self.
	$$self{'boogie_http_auth'} = $request->authorization();
	return $self->SUPER::prepare_request($request, @_);
}

# Clear all authentication-related info, either because this user agent
# will be used for another Bugzilla or because the HTTP user is changed.
sub auth_flush
{
	my ($self, $user) = @_;

	delete $$self{'boogie_http_pass'};
	$self->default_headers()->remove_header('Authorization');
}
# ]]]

# Parsers [[[
# XML::Parser style class to parse XML-RPC responses [[[
# Returns an arrya-of-struct-of-...-like structure.
package Boogie::XMLRPC;
use strict;

# XML-RPC represents values like this: [[[
#
#<Value>:
#	<Int>: text
#	<String>: text
#	<Struct>:
#		<Member>:
#			<Name>: text
#			<Value>: ...
#		<Member>:
#			<Name>: text
#			<Value>:
#		...
#	<Array>:
#		<Data>:
#			<Value>: ...
#			<Value>: ...
#			...
#
# We parse the response with a PDA where the current state is the tag
# of the most recently started element and %STATES are the possible
# transitions which reflects the XML schema.  @Values can be ARRAYs,
# HASHes and SCALARs.  When the construction of the topmost value is
# finished we add it to its parent, if that's applicable.
# ]]]
our $STRVAL = qr/^(?:boolean|int|string|datetime\.iso8601)$/;
our %STATES =
(
	_INIT		=> qr/^methodresponse$/,
	methodresponse	=> qr/^(?:params|fault)$/,
	params		=> qr/^param$/,
	param		=> qr/^value$/,
	fault		=> qr/^value$/,
	value		=> qr/^(?:array|struct|$STRVAL)$/,
	array		=> qr/^data$/,
	data		=> qr/^value$/,
	struct		=> qr/^member$/,
	member		=> qr/^(?:name|value)$/,
);

# "my" would be visible in all subsequent packages.
our (@Stack, @Values, $Curtext);

sub Init
{
	@Stack = ();
	@Values = ();
	$Curtext = undef;
}

sub Start
{
	my ($p, $tag) = @_;
	my $expect;

	$tag = lc($tag);
	$expect = $STATES{ @Stack ? $Stack[-1] : '_INIT' };
	defined $expect && $tag =~ $expect
		or die "not XML-RPC: $tag: unexpected tag";
	push(@Stack, $tag);

	if ($tag =~ $STRVAL)
	{	# Scalar, start recording.
		$Curtext = '';
	} elsif ($tag eq 'array' || $tag eq 'params')
	{
		push(@Values, [ ]);
	} elsif ($tag eq 'struct')
	{
		push(@Values, { });
	} elsif ($tag eq 'member')
	{	# A structure member
		push(@Values, undef);
	} elsif ($tag eq 'name')
	{	# Name of a structure member
		$Curtext = '';
	}
}

sub Char
{
	$Curtext .= $_[1] if defined $Curtext && $_[1] !~ /^\s*$/
}

sub End
{
	my ($p, $tag) = @_;

	pop(@Stack);
	$tag = lc($tag);
	if ($tag =~ $STRVAL)
	{
		push(@Values, $Curtext);
		undef $Curtext;
	} elsif (($tag eq 'value' && @Stack && $Stack[-1] eq 'data')
		|| $tag eq 'param')
	{	# Array element
		my $value = pop(@Values);
		ref($Values[-1]) eq 'ARRAY'
			or die 'not XML-RPC: state fucked up';
		push(@{$Values[-1]}, $value);
	} elsif ($tag eq 'member')
	{
		my ($key, $value);

		@Values >= 3 && ref($Values[-3]) eq 'HASH'
			or die 'not XML-RPC: structure member '
				. 'missing value or has multiple values';
		$value = pop(@Values);
		$key   = pop(@Values);
		$Values[-1]->{$key} = $value;
	} elsif ($tag eq 'name')
	{
		if (!defined $Values[-1])
		{	# member: key, value
			$Values[-1] = $Curtext;
		} elsif (!defined $Values[-2])
		{	# member: value, key
			$Values[-2] = $Curtext;
		} else
		{
			die 'not XML-RPC: structure member '
				. 'has multiple names';
		}
		undef $Curtext;
	}
}

sub Final
{
	my $resp;

	@Values <= 1
		or die 'not XML-RPC: inconsistent final state';
	$resp = pop(@Values);

	# If there was a single output parameter rip the array.
	defined $resp && ref($resp) eq 'ARRAY' && @$resp == 1
		and $resp = $$resp[0];
	return $resp;
}
# ]]]

# XML::Parser style class to parse Bugzilla ctype=xml output [[[
# Returns a hash of bug fields or an arrayref of such hashes.
package Boogie::BuzXML;
use strict;

our (@Bugs, $Bug, $Current, $Curtext);

sub Init
{
	@Bugs = ();
	$Bug = $Current = $Curtext = undef;
}

sub Start
{
	my ($p, $tag, %attrs) = @_;

	$tag = lc($tag);
	if ($tag eq 'bug')
	{
		$Current = $Bug =
		{	# The elements we're interested in
			bug_id			=> undef,
			creation_ts		=> undef,
			delta_ts		=> undef,
			token			=> undef,
			short_desc		=> undef,
			assigned_to		=> undef,
			bug_status		=> undef,
			resolution		=> undef,
			priority		=> undef,
			bug_severity		=> undef,
			product			=> undef,
			component		=> undef,
			version			=> undef,
			target_milestone	=> undef,
			keywords		=> undef,
			dependson		=> undef,
			blocked			=> undef,
			_COMMENTS		=> [ ],
			_ATTACHMENTS		=> [ ],
		};
	}
	return if !defined $Bug;

	if ($tag eq 'bug' && defined $attrs{'error'})
	{
		$$Bug{'_ERROR'} = $attrs{'error'};
	} elsif (exists $$Current{$tag})
	{
		if ($tag eq 'assigned_to' || $tag eq 'who')
		{
			# Bugzilla 3.0 makes the e-mail address the name
			# if the real name is missing; later versions
			# leave the name attribute empty.
			if (!defined ($$Current{$tag} = $attrs{'name'})
				|| $attrs{'name'} =~ /^\s*$/)
			{
				$$Current{$tag} = '';
				$Curtext = \$$Current{$tag}
			}
		} elsif (!defined $$Current{$tag}
			|| !grep($tag eq $_, qw(dependson blocked)))
		{
			$$Current{$tag} = '';
			$Curtext = \$$Current{$tag};
		} else
		{	# While <keywords> is comma separated,
			# <dependson> and <blocked> are in their own
			# elements, so we need to comma separate them.
			$$Current{$tag} .= ', ';
			$Curtext = \$$Current{$tag};
		}
	} elsif ($tag eq 'long_desc')
	{
		push(@{$$Bug{'_COMMENTS'}}, $Current =
		{
			who		=> undef,
			bug_when	=> undef,
			thetext		=> undef,
		});
	} elsif ($tag eq 'attachment')
	{
		push(@{$$Bug{'_ATTACHMENTS'}}, $Current =
		{	# Make a comma-separated strings of flags.
			flags		=>
				join(', ',
					map({ $attrs{$_} && /^is(.+)/
						? $1 : () }
						keys(%attrs))),
			attachid	=> undef,
			date		=> undef,
			desc		=> undef,
			filename	=> undef,
		});
	}
}

sub Char
{
	$$Curtext .= $_[1] if defined $Curtext;
}

sub End
{
	my ($p, $tag) = @_;

	if (defined $Curtext)
	{
		$$Curtext =~ s/^\s+//;
		$$Curtext =~ s/\s+$//;
		undef $Curtext;
	}

	if ($tag eq 'long_desc')
	{
		$Current = $Bug;
	} elsif ($tag eq 'attachment')
	{	# Sanitize 'filename', just in case.
		$$Current{'filename'} =~ s!^.*/+!!;
		length($$Current{'filename'})
				&& $$Current{'filename'} ne '.'
				&& $$Current{'filename'} ne '..'
			or $$Current{'filename'} =
				"attachment-$$Current{'attachid'}";
		$Current = $Bug;
	} elsif ($tag eq 'bug')
	{
		# Add context information to the error message.
		defined $$Bug{'_ERROR'} && defined $$Bug{'bug_id'}
			and $$Bug{'_ERROR'} .= " ($$Bug{'bug_id'})";

		# Remove the time zome because it shouldn't be there (?)
		# in certain Bugzilla versions (?).
		$$Bug{'delta_ts'} =~ s/\s+[+-]\d+$//
			if defined $$Bug{'delta_ts'};

		push(@Bugs, $Bug);
		$Bug = $Current = undef;
	}
}

sub Final
{
	@Bugs <= 1 ? shift(@Bugs) : [ splice(@Bugs) ]
}
# ]]]

# HTML::Parser subclass to parse a Bugzilla process_bug.cgi reply [[[
package Boogie::ProcessHTMLResponse;
use strict;
use HTML::Parser;

# Unfortunately the reply is in HTML only.
our @ISA = qw(HTML::Parser);

# Get the response summary (title or heading), and the updated token
# and delta_ts out of the response.
sub new
{
	my ($self, $result, $tag);

	return $self = HTML::Parser->new(
		api_version => 3,
		start_document_h => [ sub
		{
			# Sometimes the summary is in the heading,
			# sometimes it's in the title.
			$$self{'result'} = $result =
			{
				title		=> undef,
				h1		=> undef,
				token		=> undef,
				delta_ts	=> undef,
			};
		} ],
		end_document_h => [ sub
		{
			# Sanitize %$results by removing whitespace.
			foreach (values(%$result))
			{
				next if !defined;
				s/^\s+//;
				s/\s+$//;
				s/\n+/ /g;
			}

			# The heading appears to be a more reliable
			# source of summary.
			$$result{'summary'} = delete $$result{'h1'};
			$$result{'summary'} = delete $$result{'title'}
				if !defined $$result{'summary'};
		} ],
		start_h => [ sub
		{
			$tag = shift;
			my $attrs = shift;

			if ($tag eq 'input' && defined $$attrs{'name'})
			{
				if ($$attrs{'name'} eq 'token'
					|| $$attrs{'name'} eq 'delta_ts')
				{
					$$result{$$attrs{'name'}} =
						$$attrs{'value'};
				}
			} elsif ($tag eq 'font'
				&& defined $$result{'title'}
				&& $$result{'title'} eq 'Internal Error'
				&& defined $$attrs{'size'}
				&& $$attrs{'size'} eq '+2')
			{
				# Invalid field values are disguised as
				# internal error.  Let's try to get the
				# explanation.
				$tag = 'title';
				$$result{$tag} = '';
			}

			undef $tag unless exists $$result{$tag};
		}, "tagname, attr" ],
		end_h => [ sub { undef $tag } ],
		text_h	=> [ sub
		{
			$$result{$tag} .= shift if defined $tag;
		}, "dtext" ]);
}
# ]]]

# HTML::Parser instance to parse a HTML show_activity.cgi [[[
# Returns an array of [ $when, $who, $line ] activities.
package Boogie::ActivityParser;
use strict;
use HTML::Parser;

our ($Table_begun, $Parsing);
our (@Current_activity);
our ($Cells_per_activity, $Cell_text);

# The activities are arranged in a <TABLE>:
#
# Who_1 | When_1 | What_1  | Removed_1  | Added_1
# Who_2 | When_2 | What_2  | Removed_2  | Added_2
# Who_3 | When_3 | What_31 | Removed_31 | Added_31
#       |        | What_32 | Removed_32 | Added_32
#       |        | What_33 | Removed_33 | Added_33
#
# When we parse the first <TR> of an activity record we can figure out the
# number of <TD>s it has by looking at the "Who" cell's rowspan attribute.
# After that we eat that many cells, save them in @Current activity and save
# the whole bunch when all the cells of the activity have been consumed.
sub new
{
	my $self;

	$self = HTML::Parser->new(api_version => 3,
		start_h => [ \&start,	"tagname, attr"	],
		text_h	=> [ \&text,	"dtext"		],
		end_h	=> [ \&end,	"self, tagname"	]);
	$$self{'result'} = [ ];

	$Table_begun = $Parsing = 0;
	@Current_activity = ();
	$Cells_per_activity = 0;
	$Cell_text = undef;

	return $self;

}

sub start
{
	my ($tag, $attrs) = @_;

	return if !$Parsing;
	return if $tag ne 'td';
	$Cell_text = '';
	$Cells_per_activity = 2+3*$$attrs{'rowspan'}
		if !$Cells_per_activity;
}

sub text
{
	$Cell_text .= shift if defined $Cell_text;
}

sub end
{
	my ($parser, $tag) = @_;

	if (!$Table_begun)
	{
		$Table_begun = $tag eq 'th';
		return;
	} elsif (!$Parsing)
	{
		$Parsing = $tag eq 'tr';
		return;
	} elsif ($tag eq 'table')
	{
		$parser->eof();
	} elsif ($tag eq 'td')
	{
		$Cell_text =~ s/^\s+//;
		$Cell_text =~ s/\s+$//;
		push(@Current_activity, $Cell_text);
		undef $Cell_text;

		$Cells_per_activity--;
		if (!$Cells_per_activity)
		{
			my $who  = shift(@Current_activity);
			my $when = shift(@Current_activity);
			while (@Current_activity)
			{
				my $what = shift(@Current_activity);
				my $old  = shift(@Current_activity);
				my $new  = shift(@Current_activity);
				my $line;

				if ($old ne '' && $new ne '')
				{
					$line = "$what: $old => $new";
				} elsif ($old ne '')
				{
					$line = "$what $old no more";
				} elsif ($new ne '')
				{
					$line = "$what => $new";
				} else
				{	# What?
					$line = $what;
				}

				push(@{$$parser{'result'}},
					[ $when, $who, $line ]);
			}
		}
	}
}
# ]]]

# HTML::Parser instance to grep the text of the specified element [[[
package Boogie::GrepTag;
use strict;
use HTML::Parser;

# Return a HTML::Parser which waits until it sees the tag then records
# the text in {'result'} until the element is closed then disconnects
# all handers and does nothing until EOF.
sub new
{
	my $class = shift;
	my $self;

	$self = HTML::Parser->new(api_version => 3,
		start_h => [ sub
		{	# We've found the element.
			$$self{'result'} = '';
			$self->handler(text => sub
			{	# Save the element's text.
				$$self{'result'} .= shift;
			}, "dtext");
			$self->handler(end => sub
			{	# Remove all the handlers.
				$self->handler($_ => undef)
					for qw(start text end);
			});
		} ]);
	$self->report_tags(@_);

	return $self;
}
# ]]]

# HTML::Parser-lookalike class to parse a buglist.cgi CSV response [[[
# Returns an array of array of tokens.
package Boogie::CSVParser;
use strict;
use Text::ParseWords;

# We'll have at most one instance/process.  The result is stored in @$self.
# Parse input on the fly and $Buffer incomplete lines.  $Error is an HTML
# parser which is fed by the input if it turns out to be an HTML error
# message.  If both variables are undefined we haven't read anything.
# Otherwise the input is being processed either as a CSV or HTML.
# Both variables cannot be defined at the same time.
our ($Buffer, $Error);

sub new
{
	$Buffer = $Error = undef;
	return bless([ ], shift);
}

sub parse
{
	my $self = shift;

	if (defined $Buffer)
	{	# Normal input continuition.
		$Buffer .= shift;
	} elsif (!defined $Error)
	{	# First input, let's see what it is.
		$Buffer = shift;
		if ($Buffer =~ /^</)
		{	# Must be an HTML error message, grep its <title>.
			$Error = Boogie::GrepTag->new('title');
			$Error->parse($Buffer);
			undef $Buffer;
			return;
		}
	} else
	{	# Error HTML continuition.
		$Error->parse(shift);
		return;
	}

	# Parse all the complete lines of $Buffer.
	push(@$self, [ quotewords(',', 0, $1) ])
		while $Buffer =~ s/^(.*?)\n//;
}

sub eof
{
	if (defined $Error)
	{	# die with the error message.
		my $error;

		$Error->eof();
		$error = $$Error{'result'};
		undef $Error;
		die defined $error ? $error : "Some Bugzilla error occurred";
	} elsif (defined $Buffer && length($Buffer))
	{	# Flush $Buffer;
		push(@{shift()}, [ quotewords(',', 0, $Buffer) ]);
	}

	undef $Buffer;
}
# ]]]
# ]]]

# Write a byte stream to a file as it arrives [[[
# Used to save attachments.
package Boogie::FileDumper;
use strict;

# The first argument is the output file name (overwritten).
# Returns the error message if it couldn't be opened.
sub new
{
	my $class = shift;
        local *OUT;
        my $self = *OUT;

	# Save the output filename in $$self.
	${*OUT{SCALAR}} = shift;
	open(OUT, '>', $$self) or return "$!";
	return bless(\$self, ref($class) || $class);
}

sub parse	{ print { shift } shift	or die "$!" }
sub eof		{ close(shift)		or die "$!" }
# ]]]

# Memorize a file [[[
# Used to show attachments.
package Boogie::FileSaver;
use strict;

sub new
{
	my $class = shift;
	my $self = '';
	return bless(\$self, ref($class) || $class);
}

sub parse	{ ${shift()} .= shift }
sub eof		{ }
# ]]]

# Test [[[
package Boogie::Mock::Window;
use strict;

sub new		{ bless({ _irssi => 1 }, shift) }
sub print	{ print $_[1], "\n" }
sub printq	{ shift->print(@_) }
sub set_name	{ }

package main;
use strict;

# Reset a bug to NEW state, assigned to someone else.
sub cmd_reset
{
	cmd_reopen(@_, 'reopen');
	change_bug_properties(@_,
	[
		knob			=> 'reassignbycomponent',
		set_default_assignee	=> 1,
		comment			=> 'reset',
	]);
	cmd_rename(@_, "some bug");
}

# Torture a bug.  Try it out at:
# -- https://landfill.bugzilla.org/bugzilla-3.0-branch
# -- https://landfill.bugzilla.org/bugzilla-3.2-branch
# -- https://landfill.bugzilla.org/bugzilla-3.4-branch
if (!Irssi::in_irssi())
{	# some test code
	require Data::Dumper;
	my ($win, $buz, $bug, $nologin, @args);

	die "usage: $0 <bug> [-nologin] <url> [<http-user>] <bugzilla-email>"
		if @ARGV < 3;
	$bug = shift;
	$nologin = shift if $ARGV[0] eq '-nologin';

	$win = Boogie::Mock::Window->new();
	$nologin ? cmd_conn($win, @ARGV) : cmd_login($win, @ARGV);
	$buz = $Bugzillas{$$win{'_irssi'}};

	cmd_search($win, $buz, qw(-comp FoodReplicator -subcomp VoiceInterface -prio P3));

#	cmd_open($win, $buz, $bug);
#	$bug = $Bugs{$$win{'_irssi'}};
#	@args = ($win, $buz, $bug);
#	cmd_reset(@args);
#
#	print "\nBEGIN TEST\n\n";
#	cmd_take(@args, '-assign');
#	cmd_take(@args);
#	cmd_take(@args, '-assign');
#	cmd_tune(@args, '-severity', 'minor');
#	cmd_comment(@args, 'work');
#	cmd_comment(@args, 'work more');
#	cmd_tune(@args, '-severity', 'normal');
#	cmd_rename(@args, "bug of the day");
#	cmd_resolve(@args, 'FIXED', 'done');
#	cmd_reopen(@args, 'nope');
}
# ]]]

# vim: set foldmarker=[[[,]]] foldmethod=marker:
# End of boogie.pl
