#!/usr/bin/env perl
use FindBin qw($Bin);
use lib $Bin;
use t_Common qw/oops/; # strict, warnings, Carp
use t_TestCommon #':silent', # Test2::V0 etc.
                 qw/:DEFAULT run_perlscript verif_no_internals_mentioned
                    $debug $savepath/;

#diag "WARNING: :silent temp disabled";

#use Spreadsheet::Edit qw/:all/;
use Spreadsheet::Edit qw/read_spreadsheet apply %crow/;
use Spreadsheet::Edit::IO 1000.006 ; #qw/openlibreoffice_path/;
use IO::Uncompress::Gunzip qw/gunzip $GunzipError/;
use Encode qw/decode/;

use ODF::lpOD;
use ODF::lpOD_Helper qw/:DEFAULT
                        TEXTLEAF_FILTER PARA_FILTER TEXTLEAF_OR_PARA_FILTER/;
BEGIN {
  *_abbrev_addrvis = \&ODF::lpOD_Helper::_abbrev_addrvis;
  # Unfortunately I forgot to EXPORT_OK this symbol...
  *openlibreoffice_path = \&Spreadsheet::Edit::IO::openlibreoffice_path;
}
use ODF::MailMerge;

my $lopath = openlibreoffice_path();
skip_all("LibreOffice is not avaialble") unless $lopath;
note "Using ", $lopath;

my $tdir = Path::Tiny->tempdir();

my $scriptpath     = path($Bin)->child("../share/examples/Ex_Famnames.pl");
my $ref_txt_gzpath = path($Bin)->child("../tlib/Ex_Famnames_output.txt.gz");

my $ref_octets;
gunzip $ref_txt_gzpath->canonpath => \$ref_octets or die "gunzip: $GunzipError";
my $ref_text = decode("UTF-8", $ref_octets);

my $odt_outpath = path($tdir)->child("output.odt");
my $txt_outpath = path($tdir)->child("output.txt");

run_perlscript($scriptpath->canonpath,"-o",$odt_outpath->canonpath);

{ my $saved_cwd = Path::Tiny->cwd;
  scope_guard { chdir $saved_cwd or die; note "chdir back to $saved_cwd"; };

  note "chdir $tdir";
  chdir $tdir or die "$tdir : $!";

  my @cmd = ($lopath, "--convert-to", "txt", $odt_outpath);
  note "system @cmd";
  is (system(@cmd), 0, "0 exit status");
}
my $got_text = $txt_outpath->slurp_utf8;

#$got_text =~ s/\s+//sg;
#$ref_text =~ s/\s+//sg;

# As of LO 24.2 Alpha (Sep 2023), there is a bug in the txt output filter
# that omits text in the frame at the top "COMMON FAMILY NAMES...".
# To still work when/if that bug is fixed, just delete everything
# before the first table title "Alphabetical List of Family Names".
$got_text =~ s/\A.*?(?=Alphabetical)//s;
$ref_text =~ s/\A.*?(?=Alphabetical)//s;

sub fold($) { local $_ = shift; s/([^\n]{76})/$1\n/sg; $_ }

# warn "##TEMP: Saving to /tmp/XX*.txt ...";
# path("/tmp/XXref.txt")->spew_utf8(fold($ref_text));
# path("/tmp/XXgot.txt")->spew_utf8(fold($got_text));

is($got_text, $ref_text, "Ex_Famnames demo output has correct chars");

done_testing;
