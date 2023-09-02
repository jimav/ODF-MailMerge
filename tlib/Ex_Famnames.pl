#!/usr/bin/env perl
use strict; use warnings; use feature qw/say/;
use FindBin qw($Bin);

use DateTime ();
use DateTime::Format::Strptime ();

use Spreadsheet::Edit qw/read_spreadsheet alias apply sort_rows %crow/;

use ODF::lpOD;
use ODF::lpOD_Helper;
use ODF::MailMerge qw/replace_tokens/;

sub commify_number($) {
  scalar reverse (reverse($_[0]) =~ s/(\d\d\d)(?=\d)(?!\d*\.)/$1,/gr)
}

my $outpath = "Ex_Famnames_output.odt";

my $skelpath = "$Bin/Ex_Famnames_Skeleton.odt";
my $dbpath = "$Bin/family_names.csv";

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
# Write out the result
########################################
warn "> Writing $outpath\n";
$doc->save(target => $outpath);

#end
