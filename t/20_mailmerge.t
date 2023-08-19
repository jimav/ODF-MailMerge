#!/usr/bin/env perl
use FindBin qw($Bin);
use lib $Bin;
use t_Common qw/oops/; # strict, warnings, Carp
use t_TestCommon ':silent', # Test2::V0 etc.
                 qw/:DEFAULT verif_no_internals_mentioned 
                    $debug $savepath/;

#use Spreadsheet::Edit qw/:all/;
use Spreadsheet::Edit qw/read_spreadsheet apply %crow/;

use ODF::lpOD;
use ODF::lpOD_Helper qw/:DEFAULT 
                        TEXTLEAF_COND PARA_COND TEXTLEAF_OR_PARA_COND/;
BEGIN {
  *_abbrev_addrvis = \&ODF::lpOD_Helper::_abbrev_addrvis;
}
use ODF::MailMerge;

# Get the text, inserting a specified marker after each paragraph
our $dbpfx = "[0] ";
sub get_text_with_paramarks($;$) {
  my ($context, $paramark) = @_;
  $paramark //= "\N{PILCROW SIGN}";
  say "${dbpfx}ENTRY: context=",fmt_node($context) if $debug;
  # Be careful to expand text from nested paragraphs (e.g. inside frames)
  # at the right position i.e. into the middle of the outer paragraph.
  my $result = "";
  my $elt = $context->passes(TEXTLEAF_COND) 
            ? $context
            : $context->Hnext_elt($context, TEXTLEAF_OR_PARA_COND, PARA_COND);
  say "${dbpfx}Initial elt=",fmt_node($elt) if $debug;

  while ($elt) {
    if ($elt->passes(PARA_COND)) {
      say "${dbpfx}RECURSING INTO ",_abbrev_addrvis($elt) if $debug;
      (local $dbpfx = $dbpfx) =~ s/(\d+)/ $1 + 1 /e;
      $result .= __SUB__->($elt, $paramark);
    } else {
      my $t = $elt->Hget_text;
      say "${dbpfx}---appending ", vis $t if $debug;
      $result .= $t;
    }
    $elt = $elt->Hnext_elt($context, TEXTLEAF_OR_PARA_COND, PARA_COND);
    say "${dbpfx}NEXT (within ",_abbrev_addrvis($context),") elt=", fmt_node($elt) if $debug;
  }
  $result .= $paramark if $context->passes(PARA_COND);
  say "${dbpfx}*FINAL* result for ",addrvis($context),ivis ' $result' if $debug;
  $result
}

my $master_copy_path = "$Bin/../tlib/Skeleton.odt";
note "> Reading (copy of) $master_copy_path" if $debug;
my $input_path = tmpcopy_if_writeable($master_copy_path);

###############################
## NULL mail merge
###############################
{ 
  my $doc = odf_get_document($input_path, read_only => 1);
  my $body = $doc->get_body;

# maximal addrvis() ndigits
() = fmt_tree($body);
() = get_text_with_paramarks($body, "¶");
if ($debug) {
  say "========================";
  say fmt_tree($body);
  say "========================";
}
  my $before_text = get_text_with_paramarks($body, "¶");
  say dvis '\n$before_text' if $debug;

  say "\nB Hget_text:", vis($body->Hget_text()) if $debug;

  my $engine = ODF::MailMerge::Engine->new($body, '{PROTO-TAG}',
                                           debug => $debug);

  #read_spreadsheet "$Bin/../tlib/Addrlist.csv";
  #apply {
  #  $engine->add_record(\%crow, debug => $debug);
  #};
  
  $engine->finish(debug => $debug);
  # n.b. the entire prototype table has been deleted now

  my $after_text = get_text_with_paramarks($body, "¶");
  say dvis '\n$after_text' if $debug;

  (my $exp = $before_text) =~ s/\{LAST NAME.*?{ZIP[^\}]*\}¶//s or oops;
  say dvis '\n       $exp' if $debug;

  is ($after_text, $exp, "Zero-record MaileMerge text check");

  if ($savepath) {
    (my $spath = $savepath) =~ s/(\.\w+$)/_NULL$1/;
    note "Saving result of zero-record MM to $spath ...";
    $doc->save(target => $spath);
  }
}

###############################
## SINGLE RECORD mail merge
###############################
{ 
  my $doc = odf_get_document($input_path, read_only => 1);
  my $body = $doc->get_body;

  my $before_text = $body->Hget_text();
  #say dvis '$before_text' if $debug;

  my $engine = ODF::MailMerge::Engine->new($body, '{PROTO-TAG}',
                                           debug => $debug);

  read_spreadsheet "$Bin/../tlib/Addrlist1.csv";
  apply {
    $engine->add_record(\%crow, debug => $debug);
  };
  
  $engine->finish(debug => $debug);

  my $after_text = $body->Hget_text();
  #say dvis '$after_text' if $debug;

  my $exp = $before_text;
  $exp =~ s/\{PROTO-TAG\}// or oops;
  $exp =~ s/\{LAST NAME.*?\}/Brown/ or oops;
  $exp =~ s/\{FIRST NAME.*?\}/, John/ or oops;
  $exp =~ s/\{Address1.*?\}/115 John Brown Road/ or oops;
  $exp =~ s/(?<=John Brown Road)\{Address2.*?\}//s or oops vis $exp;
  $exp =~ s/\{CITY.*?\}/Lake\N{U+A0}Placid,/ or oops;
  $exp =~ s/\{STATE.*?\}/NY/ or oops;
  $exp =~ s/\{ZIP.*?\}/12946/ or oops;
  is ($after_text, $exp, "Single-record MaileMerge text check");

  if ($savepath) {
    (my $spath = $savepath) =~ s/(\.\w+$)/_SINGLE$1/;
    note "Saving result of SINGLE-REC MM to $spath ...";
    $doc->save(target => $spath);
  }
}
#
###############################
## MULTI RECORD mail merge
###############################
{ 
  my $doc = odf_get_document($input_path, read_only => 1);
  my $body = $doc->get_body;

  my $before_text = $body->Hget_text();
  #say dvis '$before_text' if $debug;

  my $engine = ODF::MailMerge::Engine->new($body, '{PROTO-TAG}',
                                           debug => $debug);

  read_spreadsheet "$Bin/../tlib/Addrlist.csv";
  apply {
    $engine->add_record(\%crow, debug => $debug);
  };
  
  $engine->finish(debug => $debug);

  my $after_text = $body->Hget_text();
  #say dvis '$after_text' if $debug;

  like($after_text, qr/Brown, John.*Mott, Lucretia.*Tubman, Harriet/s,
       "Multi-record MM check");

  if ($savepath) {
    (my $spath = $savepath);
    note "Saving result to $spath ...";
    $doc->save(target => $spath);
  }
}

############################################
## Check "*" wildcard hash entry 
## and unhandled {token} diagnosis
############################################
{ 
  my $doc = odf_get_document($input_path, read_only => 1);
  my $body = $doc->get_body;

  my $engine = ODF::MailMerge::Engine->new($body, '{PROTO-TAG}',
                                           debug => $debug);

  my %wildcard_got;
  my %hash1 = (
    'CITY' => "Bogo City",
    '*' => sub {
      my ($tokname, $m, $custom_mods) = @_;
      say dvis '"*" callback: $tokname $m->{match} $custom_mods' if $debug;
      $wildcard_got{$tokname}++;
      if (int(rand(2)) == 0) {
        return(0); # do nothing
      } else {
        return(Hr_SUBST, ["bogon"]);
      }
    },
  );
  $engine->add_record(\%hash1, debug => $debug);

  is (\%wildcard_got,
      hash {
        field 'FIRST NAME' => 1;
        field 'LAST NAME' => 1;
        field Address1 => 1;
        field Address2 => 1;
        field STATE => 1;
        field ZIP => 1;
      },
      "'*' wildcard hash entry used correctly"
  );

  $engine->add_record(\%hash1, debug => $debug);
  $engine->add_record(\%hash1, debug => $debug);
  $engine->add_record(\%hash1, debug => $debug);
  $engine->add_record(\%hash1, debug => $debug);
  
  my %hash2 = (
    'FIRST NAME' => "John",
    'LAST NAME' => "Brown",
  );
  eval { $engine->add_record(\%hash2, debug => $debug) };
  verif_no_internals_mentioned($@);
  like($@, qr/nhandled token/, "Diagnose unhandled {token}");
}

done_testing();

