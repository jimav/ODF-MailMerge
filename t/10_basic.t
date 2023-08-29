#!/usr/bin/env perl
use FindBin qw($Bin);
use lib $Bin;
use t_Common qw/oops/; # strict, warnings, Carp
use t_TestCommon ###':silent', # Test2::V0 etc.
                 qw/:DEFAULT $debug $savepath/;
warn ":silent temp disabled";

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
        my ($ptokname, $smods, $cmods)
          = eval{ ODF::MailMerge::_parse_token($token) };
        fail(dvisq '$token parse error: $@') if $@;
        unless ($ptokname eq $tokname) {
          fail(dvis '_parse_token $token : $ptokname ne $tokname');
        }
        unless (@$smods == 0
                && @$cmods == @$modlist
                && all { $cmods->[$_] eq $modlist->[$_] } 0..$#$cmods) {
          is($cmods, $modlist, "_parse_token bug with modifiers",
             dvis '$tokname $modlist $prespace $postspace\n$token\n$ptokname $smods $cmods'
          )
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
{ my ($tokname, $std_mods, $custom_mods) = ODF::MailMerge::_parse_token(
     "{Foo:nb:AA=a1\na2 :BB:unfold:breakmulti:delempty:delrow:delpara"
    .":del=MY DELTAG"
    .":rep_first:rep_mid:rep_last:rep=MYEXPR:CC:reptag=MYREPTAG}" );

  fail() unless $tokname eq "Foo";
  is($custom_mods, ["AA=a1\na2 ", "BB", "CC"], "Custom mods separated");
  is($std_mods, [qw/nb unfold breakmulti delempty delrow delpara/,
                 "del=MY DELTAG",
                 qw/rep_first rep_mid rep_last rep=MYEXPR reptag=MYREPTAG/],
     "Standard :modifier recognition"
  );
}
pass "Finished token-parse tests";

my $master_copy_path = "$Bin/../tlib/Basic.odt";
my $input_path = tmpcopy_if_writeable($master_copy_path);
note "> Reading (copy of) $master_copy_path" if $debug;
my $doc = odf_get_document($input_path, read_only => 1);
my $body = $doc->get_body;

# Basic replace_tokens
{
  # Note: Wildcard '*' hash entries are tested with Mail Merge
  my %hash = (
    "Address2" => "MULTI\nLINE", # token has ":unfold:delempty"
    "CITY" => "Lake Placid",     # token has ":suf=,:nb"
    "FIRST NAME" => "John",      # token has ":nb:pfx=, "
    "LAST NAME"  => "{Brown}",
    "ZIP" => "",                 # token has ":delempty,"
    "Non-existent Token Name" => "Should not be found",
  );
  my $subst_count = replace_tokens($body, \%hash, debug => $debug);

  # The file contains only a single template table which we mess with directly.
  is ($subst_count, 5, "replace_tokens return count");

  my $table = $body->Hsearch("PROTO-TAG")->{para}->get_parent_table;

  { # Whole table
    my $text = $table->Hget_text;
    note dvis 'Table $text' if $debug;
    like($text, qr/^\{Brown\}, John.*\{Address1.*\}PROTO-TAGMULTI LINELake\N{NO-BREAK SPACE}Placid/,
         "Overall table content check",
         fmt_tree($table));
  }
}

{ # Callback with custom modifier
  my %hash = (
    "Date" => sub {
      my ($key, $match, $params) = @_;
      is($key, 'Date', 'User callback $key arg');
      is($match->{match}, '{Date:mymodif}', 'user callback $match arg');
      is($params->{custom_mods}, ["mymodif"], 'user callback $mods arg',
         dvis '$key $params');
      return (Hr_SUBST, ["8/18/2023"]);
    },
  );
  my $subst_count = replace_tokens($body, \%hash, debug => $debug);
}

{ foreach my $good_mod (':rep=$i == 0', ':rep=$i == $N') {
    my $test_para = odf_create_paragraph(text => "{Mytok}{Mytok:${good_mod}}");
}

fail("Todo: test :delempty");
fail("Todo: test :reprow");

done_testing;

if ($savepath) {
  note "Saving to $savepath ...";
  $doc->save(target => $savepath);
}

