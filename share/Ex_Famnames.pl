#!/usr/bin/env perl
use strict; use warnings; use feature qw/say/;
STDOUT->autoflush; STDERR->autoflush;
use open IO => ':locale';

use FindBin qw($Bin);

use File::Basename qw/basename/;
use DateTime ();
use DateTime::Format::Strptime ();
use Getopt::Long qw/GetOptions/;

use Spreadsheet::Edit qw/read_spreadsheet alias apply sort_rows %crow/;
use Data::Dumper::Interp qw/dvis qsh qshlist/;
Data::Dumper::Interp::addrvis_digits(5);

use ODF::lpOD;
use ODF::lpOD_Helper;
use ODF::MailMerge qw/replace_tokens/;

sub commify_number($) {
  scalar reverse (reverse($_[0]) =~ s/(\d\d\d)(?=\d)(?!\d*\.)/$1,/gr)
}

my ($outpath, $also_pdf, $also_txt, $skelpath, $dbpath);
GetOptions(
  'o|outpath=s'  => \$outpath,
  '--pdf'        => \$also_pdf,
  '--txt'        => \$also_txt,
  's|skelpath=s' => \$skelpath,
  'd|dbpath=s'   => \$dbpath,
) or die "bad arguments";

$skelpath //= "$Bin/Ex_Famnames_Skeleton.odt";

$outpath //= "./".basename($skelpath) =~ s/_?Skel[a-z]*//r =~ s/\.odt/_output.odt/r;
die if $outpath eq $skelpath;

$dbpath //= "$Bin/family_names.csv";

#---------------------------------------------------------------

warn "> Reading $skelpath\n";
my $doc = odf_get_document($skelpath, read_only => 1) // die "$skelpath : $!";
my $body = $doc->get_body;

############################
# get the data
############################
warn "> Reading $dbpath\n";
read_spreadsheet($dbpath);

# Make aliases for uncertain column titles.
# These identifiers are used instead of actual column titles in
# {tokens} in the Skeleton document.
#   Side note: 'alias' throws an error if a regex does not match anything
#   or matches more than one column; so we are guaranteed that all columns
#   are correctly identified.
alias Name => qr/name/i;
alias Rank => qr/rank/i;
alias Origin => qr/origin/i;
alias Population => qr/pop/i;

my $highest_Rank = 0;
# "apply" visits all spreadsheet data rows (i.e. rows after the title row),
# executing the specified code block.  %crow is a tied hash which maps
# column titles *and aliases* to the corresponding data value in
# the "current row" being visited.
apply { $highest_Rank = $crow{Rank} if $crow{Rank} > $highest_Rank; };

########################################
# Replace "{Database Date}" with the modification time of the data file
########################################
my $dbpath_mt_unixtime = (stat($dbpath))[9];
my $dbpath_mt_dt = DateTime->from_epoch(epoch => $dbpath_mt_unixtime);
my $dbpath_mt_string = $dbpath_mt_dt->strftime("%Y-%m-%d");
replace_tokens($body, { "Database Date" => $dbpath_mt_string })
 == 1 or die "Did not find {Database Date}";

########################################
# Generate the table showing data alphabetized by Name
########################################
sort_rows { $a->{Name} cmp $b->{Name} };

# Visit all the data rows and create an entry in the document for each
{ my $engine = ODF::MailMerge::Engine->new($body, "{ByName_Proto}");
  apply {
    my $hash = {  # massage some of the data before displaying
      Name       => $crow{Name},
      Rank       => $crow{Rank},
      Origin     => $crow{Origin},
      Population => commify_number($crow{Population}),
    };
    $engine->add_record($hash);
  };
  $engine->finish();
}

########################################
# Generate the by-popularity table
########################################
sort_rows { $a->{Rank} <=> $b->{Rank} };
{ my $engine = ODF::MailMerge::Engine->new($body, "{ByPop_Proto}");
  apply {
    $engine->add_record(\%crow);
  };
  $engine->finish();
}

########################################
# Generate the by-origin table using a separate row for each name
# For brevity, origins including English are omitted.
########################################
{ my %Origin_to_Names;
  apply {
    push @{ $Origin_to_Names{$crow{Origin}} }, $crow{Name}
      if $crow{Origin} !~ /English/;
  };
  { my $engine = ODF::MailMerge::Engine->new($body, "{ByOriginNonEng_Proto}");
    foreach my $origin (sort keys %Origin_to_Names) {
      my $namelist = $Origin_to_Names{$origin};
  #use Data::Dumper::Interp; say dvis '## $origin\n   $namelist';
  die "bug" if grep /\n/s, @$namelist;
      my $hash = {
        Origin => $origin,
        Names  => $namelist,
      };
      $engine->add_record($hash);
    }
    $engine->finish();
  }
}

########################################
# Generate the complete by-origin table.
# The prototype encapsulates the {Name} tag in a frame
# so the frame is replicated instead of the whole row.
########################################
{ my %Origin_to_Names;
  apply {
    push @{ $Origin_to_Names{$crow{Origin}} }, $crow{Name};
  };
  { my $engine = ODF::MailMerge::Engine->new($body, "{ByOrigin2_Proto}");
    foreach my $origin (sort keys %Origin_to_Names) {
      my $namelist = $Origin_to_Names{$origin};
  #use Data::Dumper::Interp; say dvis '## $origin\n   $namelist';
  die "bug" if grep /\n/s, @$namelist;
      my $hash = {
        Origin => $origin,
        Names  => $namelist,
      };
      $engine->add_record($hash, debug => 0);
    }
    $engine->finish();
  }
}

########################################
# Write out the result
########################################
warn "> Writing $outpath\n";
$doc->save(target => $outpath);

if ($also_pdf) {
  my @cmd = ("libreoffice", "--convert-to", "pdf", $outpath);
  warn "> ", qshlist(@cmd),"\n";
  system @cmd;
}
if ($also_txt) {
  my @cmd = ("libreoffice", "--convert-to", "txt", $outpath);
  warn "> ", qshlist(@cmd),"\n";
  system @cmd;
}

exit 0;
