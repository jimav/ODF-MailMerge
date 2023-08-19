#!/usr/bin/env perl
use FindBin qw($Bin);
use lib $Bin;
use t_Common qw/oops/; # strict, warnings, Carp
use t_TestCommon ':silent', # Test2::V0 etc.
                 qw/:DEFAULT $debug $savepath/;

use ODF::lpOD;
use ODF::lpOD_Helper;
use ODF::MailMerge;

my $token_re = $ODF::MailMerge::token_re;

sub escape($) { local $_ = shift; s/([:\{\}\\])/\\$1/g; $_ }

for my $tokname ("A", "a b", "A_B", "A:B", "A\\B", "A{B:", "AB\\") {
  for my $modlist ([], ["mod1"], ["mod1=xx\nyy"], ["mod1","mod{2=val2"], 
                   ["M:od1","Mod2\\","Mod3}:=val3"]) {
    for my $prespace ("", " \t") {
      for my $postspace ("", "\t  ") {
        my $token = "{".$prespace.escape($tokname).$postspace
                    .join("", map{ ":".escape($_) } @$modlist)
                    ."}";
        my ($ptokname, @pmods) = eval{ ODF::MailMerge::_parse_token($token) };
        fail(dvisq '$token parse error: $@') if $@;
        unless ($ptokname eq $tokname) {
          fail(dvis '_parse_token $token : $ptokname ne $tokname');
        }
        unless (@$modlist == @pmods 
                && all { $modlist->[$_] eq $pmods[$_] } 0..$#pmods) {
          is(\@pmods, $modlist, "_parse_token bug with modifiers");
        }
      }
    }
  }
}
for my $bad_tokname ("A\tB", "a\nb", "A:\nfoo") {
  for my $modlist ([], ["mod1"], ["mod1","mod{2=val2"], 
                   ["M:od1","Mod2\\","Mod3}:=val3"]) {
    for my $prespace ("", " \t") {
      for my $postspace ("", "\t  ") {
        my $token = "{".$prespace.escape($bad_tokname).$postspace
                    .join("", map{ ":".escape($_) } @$modlist)
                    ."}";
        () = eval{ ODF::MailMerge::_parse_token($token) };
        unless ($@ =~ /token/) {
          fail(dvis '$bad_tokname failed to provoke an error ($token)');
        }
      } 
    } 
  }
}
pass "Finished token-parse tests";

my $master_copy_path = "$Bin/../tlib/Basic.odt";
my $input_path = tmpcopy_if_writeable($master_copy_path);
note "> Reading (copy of) $master_copy_path" if $debug;
my $doc = odf_get_document($input_path, read_only => 1);
my $body = $doc->get_body;

{
  # Note: Wildcard '*' hash entries are tested with Mail Merge
  my %hash = (
    "Address2" => "MULTI\nLINE", # token has ":unfold:delempty"
    "CITY" => "Lake Placid",     # token has ":suf=,:nb"
    "FIRST NAME" => "John",      # token has ":nb:pfx=, "
    "LAST NAME"  => "{LAST-NAME-INDIRECT}",
    "LAST-NAME-INDIRECT"  => "Brown",
    "ZIP" => "",                 # token has ":delempty,"
  );
  my $subst_count = replace_tokens($body, \%hash);

  # The file contains only a single template table which we mess with directly.
  # We introduce an indirection, so the total is +1
  is ($subst_count, 5+1, "returned count");

  my $table = $body->Hsearch("PROTO-TAG")->{para}->get_parent_table;

  { # Whole table
    my $text = $table->Hget_text;
    note dvis 'Table $text' if $debug;
    like($text, qr/^Brown, John.*\{Address1.*\}PROTO-TAGMULTI LINELake\N{NO-BREAK SPACE}Placid/,
         "Overall table content check");
  }
}

{ # Callback with custom modifier
  my %hash = (
    "Date" => sub {
      my ($key, $match, $mods) = @_;
      is($key, 'Date', 'user callback $key arg');
      is($match->{match}, '{Date:mymodif}', 'user callback $match arg');
      is($mods, ["mymodif"], 'user callback $mods arg');
      return (Hr_SUBST, ["8/18/2023"]);
    },
  );
  my $subst_count = replace_tokens($body, \%hash);
}

done_testing;

if ($savepath) {
  note "Saving to $savepath ...";
  $doc->save(target => $savepath);
}

