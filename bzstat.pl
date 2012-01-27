#!/usr/bin/perl -w
#
# bzstat.pl -- create statistics from a bugzilla XML dump
#
# Synopsis:
#   bzstat.pl [{-m|-mx} <bugzilla-user>] [-vvv|-q] [<files>...]
#
# If <bugzilla-user> is specified its reports, assignments and comments
# are counted.  If specified with -mx only exact matches are counted,
# otherwise it's enough to be a substring of the matched user names.
#
# The rest of the statistics are independent of the <bugzilla-user>,
# ie. this program does not tell how many bugs has the user fixed;
# that's impossible to figure out anyway.  The -v and -q flags adjust
# the output verbosity.
#
# bzstat.pl depends on libhtml-parser-perl.
#

use strict;
use HTML::Parser;

# Get $me.
my $me;
if (@ARGV >= 2 && $ARGV[0] =~ s/^-m//)
{
	$me  = shift eq 'x'
		? qr/^\Q$ARGV[0]\E$/
		: qr/\Q$ARGV[0]/;
	shift;
}

# Text formatting
my $MARGIN = '  ';
my $TWIDTH = ($ENV{'COLUMNS'} || 80) - length($MARGIN);
my $DASHES = 2;

sub printtable
{
	my ($n, $table) = @_;
	my ($fwidth, $lineno);

	foreach (@$table)
	{
		my $len = length("$$_[1]");
		defined $fwidth && $fwidth >= $len
			or $fwidth = $len;
	}

	foreach (@$table)
	{
		my ($key, $val) = @$_;
		my $lhs = "$key: ";
		my $rhs = length($lhs)+$fwidth <= $TWIDTH
				? sprintf('%*u',  $fwidth, $val)
				: "$val";
		my $pad = $TWIDTH - (length($lhs)+length($rhs));
		my $chr = !defined $n		? ' '
			: ++$lineno % $n == 0	? '.'
			:			  '-';
		print ($lhs, $pad > 0 ? ($chr x ($pad-1), ' ') : '', $rhs);
	}
}

sub printstat
{
	my ($title, $hash) = @_;

	print "$title:";
	printtable($DASHES,
		 [ sort({ $$b[1] <=> $$a[1] || $$a[0] cmp $$b[0] }
			map({ [ $MARGIN.$_, $$hash{$_} ] }
				keys(%$hash))) ]);
}

# Statistics
my $nbugs = 0;
my %arq =
(
	assigned_to	=> 0,
	reporter	=> 0,
	qa_contact	=> 0,
);
my (%categories);
my (%frequencies, %keywords);
my (%severities, %priorities, %flags);
my (%states, %whiteboard, %resolutions);
my @comments;

# Parsing
my $text;
my ($class, $prod, $comp);
my ($in_comment, $commenter, $commented_on);
my $parser = HTML::Parser->new(
	api_version	=> 3,
	xml_mode	=> 1,
	unbroken_text	=> 1,

	start_h => [ sub
	{
		my $tag = shift;
		if ($tag eq 'flag')
		{
			my $attrs = shift;
			$flags{"$$attrs{'name'} ($$attrs{'status'})"}++;
		} elsif (defined $me && $tag eq 'long_desc')
		{
			$in_comment = 1;
		}
	}, 'tagname,attr' ],

	text_h => [ sub
	{
		$text = shift;
	}, 'dtext' ],

	end_h => [ sub
	{
		my $tag = shift;
		if ($tag eq 'bug')
		{
			$nbugs++;
			$categories{"$class/$prod/$comp"}++;
			$class = $prod = $comp = undef;
		} elsif (exists $arq{$tag})
		{
			$arq{$tag}++ if defined $me && $text =~ $me;
		} elsif ($tag eq 'classification')
		{
			$class = $text;
		} elsif ($tag eq 'product')
		{
			$prod = $text;
		} elsif ($tag eq 'component')
		{
			$comp = $text;
		} elsif ($tag eq 'cf_occurence')
		{
			$frequencies{$text}++;
		} elsif ($tag eq 'keywords')
		{
			$keywords{$_}++ foreach split(/,\s*/, $text);
		} elsif ($tag eq 'bug_severity')
		{
			$severities{$text}++;
		} elsif ($tag eq 'priority')
		{
			$priorities{$text}++;
		} elsif ($tag eq 'bug_status')
		{
			$states{$text}++;
		} elsif ($tag eq 'status_whiteboard')
		{
			$whiteboard{$_}++ foreach split(/,\s*/, $text);
		} elsif ($tag eq 'resolution')
		{
			$resolutions{$text}++;
		} elsif ($in_comment)
		{
			if ($tag eq 'who')
			{
				$commenter = $text;
			} elsif ($tag eq 'bug_when')
			{
				$commented_on = $text;
			} elsif ($tag eq 'long_desc')
			{
				push(@comments, $commented_on)
					if $commenter =~ $me;
				$commenter = $commented_on = undef;
				$in_comment = 0;
			}
		}
		undef $text;
	}, 'tagname' ],
);

# Main starts here
# Get the output $verbosity.
my $verbosity = defined $me ? 1 : 2;
if (@ARGV && $ARGV[0] =~ /^-(v+)$/)
{
	$verbosity = length($1);
	shift;
} elsif (@ARGV && $ARGV[0] eq '-q')
{
	$verbosity = 0;
	shift;
}

# Get the @files to parse.
my @files;
if (@ARGV)
{
	foreach (@ARGV)
	{
		local *FH;
		open(FH, '<', $_) or die "$_: $!";
		push(@files, *FH);
	}
} else
{
	push(@files, \*STDIN);
}

$\ = "\n";
$parser->parse_file($_) foreach @files;
my @table = ([ 'Number of bugs' => $nbugs ]);
push(@table,
	[ $MARGIN . 'reported'		=> $arq{'reporter'}	],
	[ $MARGIN . 'assigned'		=> $arq{'assigned_to'}	],
	[ $MARGIN . 'managed'		=> $arq{'qa_contact'}	],
	[ 'Number of comments'		=> scalar(@comments)	])
	if defined $me;
printtable(undef, \@table);
foreach (
	[ 2, 'Programs/components/subcomponents' => \%categories  ],
	[ 2, 'Frequencies'			 => \%frequencies ],
	[ 2, 'Keywords'				 => \%keywords    ],
	[ 1, 'Severities'			 => \%severities  ],
	[ 1, 'Priorities'			 => \%priorities  ],
	[ 3, 'Flags'				 => \%flags       ],
	[ 1, 'States'				 => \%states      ],
	[ 2, 'Whiteboard notes'			 => \%whiteboard  ],
	[ 1, 'Resolutions'			 => \%resolutions ])
{
	printstat($$_[1], $$_[2]) if $verbosity >= $$_[0];
}

# End of bzstat.pl
