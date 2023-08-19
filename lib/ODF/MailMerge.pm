#!/usr/bin/env perl
# License: Public Domain or CC0
# See https://creativecommons.org/publicdomain/zero/1.0/
# The author, Jim Avera (jim.avera at gmail) has waived all copyright and
# related or neighboring rights.  Attribution is requested but is not required.

use 5.018; # for unicode_strings, lexical_subs
use strict; use warnings FATAL => 'all'; 
no warnings "experimental::lexical_subs";
use feature qw(switch state say lexical_subs fc);
use feature qw(unicode_strings unicode_eval evalbytes);
use feature 'unicode_strings';
use utf8;

package ODF::MailMerge;

# Allow "use <thismodule> <someversion>;" in development sandbox to not bomb
# ...but don't let CPAN or test harnes scanners see this as defining $VERSION
{ no strict 'refs'; ${__PACKAGE__."::VER"."SION"} = 999.999; }

# VERSION from Dist::Zilla::Plugin::OurPkgVersion
# DATE from Dist::Zilla::Plugin::OurDate

use Carp;
our @CARP_NOT = ("ODF::lpOD_Helper", "ODF::lpOD");

use Scalar::Util qw/refaddr/;
use List::Util qw/first any none/;
use Data::Dumper::Interp 6.004 qw/visnew ivis dvis vis visq/;
use Spreadsheet::Edit::Log qw/oops btw/;

use ODF::lpOD;
use ODF::lpOD_Helper qw/:DEFAULT PARA_COND/;

use Exporter 'import';
our @EXPORT = qw/replace_tokens/;

our $debug;

# Recognize anything probably intended as a {token} expression, even if erroneous
our $token_re = qr/\{ (?<tokname> (?:[^:\{\}\\\n]+|\\[^\n])+    )
                      (?<mods>    (?: : (?:[^:\{\}\\]+|\\.)+ )* )
                   \}/xs;

use constant STANDARD_MODS => {
  map{ $_ => 1 } qw/pfx= suf= repl= default= nb unfold breakmulti delempty/
};

our %delempties;

sub _do_std_modifiers($$$) {
  my ($m, $content, $mods) = @_;
oops unless defined $content;

  push @$content, "" if @$content == 0;
  my $is_empty = none{ ref($_) eq "" && $_ ne "" } @$content;

  foreach (@$mods) {
    my ($id, $rhs) = @$_;
    if ($id eq "pfx") {
      oops "undef pfx rhs" unless defined $rhs;
      if (! $is_empty) {
        my $ix = first{ ref($content->[$_]) eq "" } 0..$#$content;
        $content->[$ix] = $rhs . $content->[$ix];
      }
    }
    elsif ($id eq "suf") {
      oops "undef suf rhs" unless defined $rhs;
      if (! $is_empty) {
        my $ix = first{ ref($content->[$_]) eq "" } reverse 0..$#$content;
        $content->[$ix] .= $rhs
      }
    }
    elsif ($id eq "default") {
      oops "undef default rhs" unless defined $rhs;
      if ($is_empty) {
        my $ix = ref($content->[0]) eq "" ? 0 : 1; # preserve an initial style
        splice(@$content, $ix);
        push @$content, $rhs;
      }
    }
    elsif ($id eq "repl") {
      oops "undef repl rhs" unless defined $rhs;
      # conflicts with :pfx or :suf were checked in _curried_Hreplace_callback()
      if (! $is_empty) {
        my $ix = ref($content->[0]) eq "" ? 0 : 1; # preserve an initial style
        splice(@$content, $ix);
        push @$content, $rhs;
      }
    }
    elsif ($id eq "nb") {
      foreach (@$content) {
        next if ref($_) ne "";
        s/ /\N{NO-BREAK SPACE}/sg;
      }
    }
    elsif ($id eq "unfold") {
      foreach (@$content) {
        next if ref($_) ne "";
        s/\n/ /sg;
      }
    }
    elsif ($id eq "breakmulti") {
      my $text = join("", grep{ref($_) eq ""} @$content);
      if ($text =~ /\n./s) {
        croak "Mal-formed [content] (does not end with plain string)"
           if ref($$content[-1]) ne "";
        $$content[-1] .= "\n";
      }
    }
    elsif ($id eq "delempty") {
      # If in a table, remember the containing row, otherwise just the
      # containing paragraph
      my $what = $m->{para}->parent("table:table-row") // $m->{para};
      $delempties{ refaddr($what) } = $what;
    }
    else {
      oops "bug: std? modifier ",vis($id);
    }
btw dvis 'AFTER processing Std $id $rhs, $content' if $debug;
  }
}

sub _parse_token($) {
  my $t = shift;
  $t =~ /^${token_re}$/ or oops dvis '$t';
  my ($tokname, $mods) = ($+{tokname}, $+{mods});

  $tokname =~ s/^[ \t]*//; $tokname =~ s/[ \t]*$//;
  $tokname =~ s/\\(.)/$1/sg; # un-escape

  croak "Invalid token ",vis($t)," -- token NAME may not contain tab or newline"
    if $tokname =~ /[\t\n]/;

  # Split :mod1:mod2:... discarding the initial :s
  my @mods;
  while ($mods =~ /\G:((?:[^:\\]+|\\.)+)/gsc) {
    push @mods, $1;
  }
  oops vis(pos($mods)) unless !defined(pos($mods)) || pos($mods)==length($mods);

  foreach (@mods) { 
    s/\\(.)/$1/sg; # un-escape
    if ((my $ix = index($_,'=')) >= 0) {
      croak "Invalid token ",vis($t),
            " -- newline or tab is allowed only in :modifier after '='"
        if substr($_,0,$ix) =~ /[\t\n]/;
    }
  }
  return ($tokname, @mods);
}

sub _curried_Hreplace_callback {
  my ($hash, $m) = @_;
  # This is called by Hreplace for every token expression, with $hash curried.
  
  my ($tokname, @mods) = _parse_token( $m->{match} );

  my $val = $hash->{$tokname} // $hash->{'*'};
  return(0)
    unless defined $val;

  my (@std_mods, @custom_mods);
  foreach (@mods) {
    my ($id, $eq, $rhs) = (/^((?:[^=]+|\\=)+)(?:(=)(.*))?$/s);
    if (STANDARD_MODS->{$id.($eq//"")}) {  # e.g. "pfx="
      push @std_mods, [$id, $rhs];
    } else {
      push @custom_mods, $_;
      croak "Unrecognized modifier ':$_' in ",$m->{match},
            "\n(custom :modifiers are only allowed when using a callback to process them)\n"
        unless ref($val) eq 'CODE';
    }
  }

  my $return_op = Hr_SUBST|Hr_RESCAN; # Hr will step over empty replacements
  my $content;
  if (ref($val) eq "") {
    $content = [$val];
  }
  elsif (ref($val) eq "ARRAY") {
    $content = $val
  }
  elsif (ref($val) eq 'CODE') {
    ($return_op, $content) = $val->($tokname, $m, \@custom_mods);
    if ($return_op != 0 && ref($content) ne "ARRAY") {
      croak "The callback for key ",visq($tokname),
            " returned ", visnew->avis1r($return_op, $content),
            ".\nWith a non-zero opcode, the second return value must be a [content] aref\n";
    }
  }
  else {
    croak "The hash value for key ",visq($tokname)," is an inappropriate reference ",visq($val);
  }

  if ($return_op & Hr_SUBST) {
    _do_std_modifiers($m, $content, \@std_mods);
    btw ivis 'Replacement: $m->{match} --> $content' if $debug;
    return($return_op, $content);
  } else {
    return($return_op);
  }
}

sub replace_tokens($$@) {
  my ($context, $hash, %opts) = @_;

  local $debug = $debug || $opts{debug};

  # Search paragraphs one by one to limit the scope of errors from a missing }
  my @paras = $context->Hdescendants_or_self(PARA_COND);
  @paras = ($context) unless @paras; # in case $context is a leaf or span

  my $repl_count = 0;
  foreach my $para (@paras) {
    my @r = $para->Hreplace($token_re, 
                            sub{ _curried_Hreplace_callback($hash, @_) },
                            debug => 0,
                           );
    $repl_count += scalar(@r);
btw dvis 'Replaced $token_re using $hash\nsubstitutions:\n   ',
    join("\n   ",map{ fmt_match($_) } @r) if $debug;
  }

  # Delayed actions after all tokens have been processed in $context
  my @tmp = values %delempties;
  %delempties = ();
  for my $what (@tmp) {
    oops if !$what->parent;
    my $text = $what->Hget_text();
    if (! defined($text) or $text =~ /\A\s*\z/s) {
   #   $what->delete;
    }
  }

  return $repl_count;
}

# Hack to remove officeooo:rsid text properties from text styles,
# which if cloned or otherwise used for multiple spans cause Libre Office 
# to hang or crash.
#
# Modified styles which have no remaining attributes are deleted, and spans 
# which were useing them are erased (moving their content up one level).
sub clean_rsids($;@) {
  my ($context, %opts) = @_;

  # Collect the names of rsid text styles 
  my %rsid_styles;
  {
    my $doc = $context->get_document;
    # This does not work due to a bug overloading "text" with the same-named
    # DataStyle type:
    # my @textstyles = $doc->get_styles('text');
    #FIXME ... I can't see why get_styles('text') is not correct!!
    ##    DataStyle::is_numeric_family('text') should return false...
    
    # The following was extracted from ODF::lpOD::Document::get_styles
    my $xp = '//style:style[@style:family="text"]';
    my @textstyles = ($doc->get_elements(STYLES,$xp), $doc->get_elements(CONTENT,$xp));
    foreach my $tstyle (@textstyles) {
      foreach my $tprop ($tstyle->descendants(qr/style:text-properties/)) {
        my %att = $tprop->get_attributes;
        if ($att{'officeooo:rsid'}) {
          my $tsname = $tstyle->get_name;
          $rsid_styles{$tsname} //= [$tstyle];
          push @{ $rsid_styles{$tsname} }, $tprop;
        }
      }
    }
  }

  # Check every span in the context
  foreach my $span ($context->Hdescendants_or_self('text:span')) {
    #my $parent = $span->parent;
    my $tsname = $span->get_attribute('style') // oops;
    if (my $v = $rsid_styles{$tsname}) {
      my ($tstyle, @tprops) = @$v;
      my $props_remain;
      for my $tprop (@tprops) {
        my %att = $tprop->get_attributes;
        delete $att{'officeooo:rsid'} // oops;
        if (keys %att) {
          $tprop->del_attributes;
          $tprop->set_attributes(%att);
          $props_remain = 1;
          btw "$tsname : rsid removed from tprop ",fmt_node($tprop) if $opts{debug}; 
        } else {
          btw "$tsname : Deleting rsid tprop ",fmt_node($tprop) if $opts{debug}; 
          $tprop->delete;
        }
      }
      if ($props_remain) {
        btw "$tsname : Leaving span intact (still has attributes)"
          if $opts{debug};
      } else {
        btw "$tsname : Deleting rsid style ",fmt_tree($tstyle, internals => 1),
            "\n  and erasing span ",fmt_node($span) if $opts{debug}; 
        $tstyle->delete; # should only be referenced this one place!
        $span->erase; # XML::Twig
        # FIXME: There were old comments in the code copied from RFFMDirGenODF
        # to the effect that ODF::lpOD overrides XML::Twig methods with 
        # incompatible APIs and breaks XML::Twig::Elt::erase().
        # But I don't see that now...
      }
    }
  }
}#clean_rsids

package ODF::MailMerge::Engine;

use ODF::lpOD;
use ODF::lpOD_Helper;
use Data::Dumper::Interp;
use Carp;
our @CARP_NOT = ("ODF::MailMerge", "ODF::lpOD_Helper", "ODF::lpOD");

sub new {
  my $class = shift;
  my ($context, $proto_tag, %opts) = @_;

  ODF::MailMerge::clean_rsids($context, %opts);

  my $m = $context->Hsearch($proto_tag) 
           // croak ivis 'proto_tag $proto_tag not found';

  my $proto_table = $m->{segments}->[0]->get_parent_table
           // croak(ivis 'proto_tag $proto_tag is not in a Table');

  $m->{para}->Hreplace($proto_tag, [""]); # [] ?

  bless {
    proto_table => $proto_table
  },$class
}

sub add_record {
  my ($self, $hash, %opts) = @_;
  local $debug = $debug || $opts{debug};

  my $proto_table = $self->{proto_table};

  my $table = $proto_table->clone;
  $table->set_name($proto_table->Hgen_table_name());
  $proto_table->insert_element($table, position => PREV_SIBLING);

  my sub wrapper_cb {
    my ($tokname, $m, $custom_mods) = @_;
    my $val = $hash->{$tokname} // $hash->{'*'};
    if (defined $val) {
       if (ref($val) ne "") {
         croak "hash value must be a string or CODE ref (not $val)"
           unless ref($val) eq "CODE";
         return $val->($tokname, $m, $custom_mods);
       } else {
         return (Hr_SUBST|Hr_RESCAN, [$val]);
       }
    } else {
      croak "Unhandled token ",vis($m->{match}),
            " (the hash has no entry for '$tokname' or '*')";
    }
  
  }       
  ODF::MailMerge::replace_tokens($table, {'*' => \&wrapper_cb}, %opts);
}

sub finish {
  my ($self, %opts) = @_;
  delete($self->{proto_table})->delete();
}

1;
__END__

=pod

=encoding UTF-8

=head1 NAME

ODF::MailMerge - "Mail Merge" or just substitute tokens in ODF documents

=head1 SYNOPSIS

 use ODF::lpOD;
 use ODF::lpOD_Helper;
 use ODF::MailMerge qw/replace_tokens/;
 
 my $doc = odf_get_document("/path/to/file.odt");
 my $body = $doc->get_body;
 
 # Simple replacement of '{who}', '{last words}' and '{zzz}' 
 # everywhere in the document.
 my $hash = {
   who => "John Brown",
   'last words' => [ 
      [color => "#50FFEE", "bold"], 
      " I deny everything but...the design on my part to free the slaves." 
   ],
   zzz => \&callback,
 };
 replace_tokens($body, $hash);
 
 # Mail-merge:
 #   1. Find a prototype table containing the token "{mmproto}".
 #   2. Replace tokens in that table using data from a spreadsheet,
 #      replicating the table as many times as necessary for all rows.
 #
 my $engine = ODF::MailMerge::Engine->new($body, "{mmproto}");
 
 use Spreadsheet::Edit qw/read_spreadsheet apply %crow/;
 read_spreadsheet "/path/to/data.xlsx!Sheet1";
 apply {
   $engine->add_record(\%crow);  # %crow is a tied hash to current row
 };
 $engine->finish();

 $doc->save(target => "/path/to/output.odt");

=head1 DESCRIPTION

This tool uses ODF::lpOD and ODF::lpOD_Helper to patch ODF documents.
Token strings of the form "{key}" or "{key:modifiers...}"
are replaced with values from a hash indexed by "key".

Optional :modifiers within tokens
can change the value actually substituted or have side-effects
such as removing lines which contain only white space.

A "mail merge" function replicates a template table as many times as needed
to plug in values from multiple data records.

=head1 THE PARADIGM

First, manually create a prototype ODF document (using e.g. LibreOffice)
containing static content and {tokens} to be interpolated, formatted
as desired.
To use "mail merge", create a Table which displays a single "entry"
(record) with {token}s where data values should be plugged in.  
This table will be replicated as many times as there are data records.

Substituted values will have the same formatting as the tokens which were
replaced.  This is quite powerful.

For example, to generate a multi-column "member directory", create a table
in the prototype document with tokens like {Name}, {Address}, etc. 
using any desired styles;
place that table in a Frame which has the desired number of columns.  

When processed, the table will be cloned and appended within 
it's frame, flowing into successive columns and new pages as needed.
The prototype table's style can keep all rows on the same page/column
to prevent splitting entries, and the Frame may be formatted to control
inter-entry spacing, borders, etc.

=head1 MAIL MERGE

Often data comes from a spreadsheet or CSV, but the API simply requires
a Perl hash which maps {token} names to values for the current entry.  

The example in the SYNOPSIS reads a spreadsheet using L<Spreadsheet::Edit>, 
which provides just such a hash via the tied variable "%crow" (current row);
this hash maps column titles (among other things) to data values in the 
row being visited by 'apply'.
Therefore tokens {Name} and {Address} would be 
replaced by appropriate values from the "Name" and "Address" columns.

=head2 $engine = ODF::MailMerge::Engine-E<gt>new($context, $proto_tag);

Creates a new mail-merge engine which will use the protototype
table containing $proto_tag.

I<$context> is usually the document body e.g. C<$doc-E<gt>get_body>.

I<$proto_tag> is a tag used to locate the prototype table within $context.
The tag may appear anywhere within the table; 
the tag will be immediately deleted.

=head2 B<$engine-E<gt>add_record($hashref);>

The prototype table is first cloned and appended to any previous copies.

Then all {key} or {key:modifier...} strings in the clone are 
replaced by looking up "key" in the specified hash as described
at "TOKEN REPLACEMENT" below. An exception occurs if an unhandled 
token is found.

=head2 B<$engine-E<gt>finish();>

This must be called after the last C<add_record> to clean up.  
It deletes the prototype table, 
leaving behind only the clones with instantiated values.

=head1 SIMPLE SUBSTITUTION

=head2 $count = replace_tokens($context, $hash);

This function replaces tokens without using the mail-merge mechanism.

$context is the document body or any descendant; $hash maps token names
to replacement values as described at "TOKEN REPLACEMENT".

All instances of tokens in $context are replaced if their names
exist in %$hash.   Any tokens not named in %$hash are left as-is unless 
the hash contains a '*' wildcard entry.

=head1 TOKEN REPLACEMENT

In the hash you provide,
I<keys> are token names without the curly brackets or :modifiers. 
For example, a key "First Name" will be used for token "{First Name}"
or "{First Name:...}" . 

Tokens may contain any character including spaces and newlines, except:

=over

=item - Leading & trailing spaces around Token names are ignored

=item - Newlines and tabs are allowed only in :modifiers after an '='

=item - Use \: \{ \} to denote literal : {  } characters

=back

=for comment =back
=for comment 
=for comment For example, S<"{   Side Note   :pfx=\{NOTE\:\n:suf=\n\}}"> would produce
=for comment 
=for comment    ...{NOTE:
=for comment    <value of $hash->{'Side Note'}>
=for comment    }...

The hash key B<'*'> is a wildcard, used if no other key matches.

A hash value may be a replacement string (or formatted [content] spec as 
described later), or a callback subref.

If the value is a string or [content], then the token is replaced by the 
indicated content and the search is repeated starting with the 
newly-substituted result; 
I<if the replacement contains {tokens} they too will be replaced> 
just as if they had existed in the original content.

=head2 Token :modifiers

Zero or more :modifiers may be appended to a token name to 
modify the replacement value or for side-effects.
For example B<{Name:pfx=Hello :nb}> would be replaced by
the value given by C<$hash-E<gt>{Name}> prepended with "Hello "
and with all spaces made non-breaking.

The standard :modifiers are

  :pfx=ANYTHING or :suf=ANYTHING 
                    - Prepend or append ANYTHING to the value if the 
                      initial value is *not* empty.

  :default=ANYTHING - Use ANYTHING if the initial value *is* empty
                      (does not trigger :pfx :suf or :repl)

  :repl=ANYTHING    - Replace the current value with ANYTHING if it is 
                      not empty (ANYTHING may be empty).

  :nb               - Convert spaces to non-breaking

  :unfold           - Convert embedded newlines to spaces

  :breakmulti       - Append a newline if the value contains an 
                      embedded newline.
  
  :delempty         - Delete the table row (or if not in a table, then 
                      the containing paragraph) if the row (or para)
                      contains only white space after all tokens have
                      been processed.

Standard :modifiers are executed in the order given.  
For example ":nb" will change spaces in the current value to non-breaking 
but not spaces inserted by a subsequent :modifier such as ":pfx=some thing".

=head2 Eliding Empty Lines

The :delempty modifier causes the table row which contained it to be
deleted if it ends up containing only white space.

To make this work, non-white content in the row must be supplied only via 
token substitutions including possible :modifiers.  For example,

   {AREA_CODE:pfx=(:suf=):delempty} {FIRST3:suf=-}{LASTFOUR}

would normaly produce e.g. "(202) 456-1111" but if
the AREA_CODE, FIRST3, and LASTFOUR fields are all empty 
then the :pfx and :suf modifiers will not be activated and the
final result will be a single space -- causing the row to be entirely 
deleted from the table.

=head2 Callbacks and custom :modifiers

If the hash value for a token is a sub reference, the sub is called with

  ($key, $match, \@custom_modifiers)

I<$key> is the hash key, i.e. the token name;

I<$match> is a result hashref from ODF::lpOD_Helper's B<Hsearch>:

  $match->{match} is the complete "{token}" including any modifiers.
  $match->{para} is the paragraph which contained the token.

I<\@custom_modifiers> is a ref to an array of unrecognized :modifier strings
(excluding the ':') found in the token.  
It is up to your code to do what it wants with them.
Note: An exception occurs if unrecognized :modifiers are encountered
when a callback is not being used.

The callback's return values indicate whether and how to replace
the token.  The protocol uses the Hr_* constants exported 
by L<ODF::lpOD_Helper>:

  return(Hr_SUBST, [content])

    The token will be replaced by [content] (see below) after applying
    any standard :modifiers in the token.  Then searching continues 
    immediately after the substituted content.

  return(Hr_SUBST|Hr_RESCAN, [content])

    The token will be replaced but searching will be restarted
    at the beginning of the new substituted content; any {tokens} in 
    the replacement will be processed.

  return(0)

    Leaves the {token} as-is.  This can be used when {token} will be 
    somehow handled later, perhaps as a side-effect of processing a 
    different token.

=head2 [content] Specifiers

See L<ODF::lpOD_Helper> for details.   In brief, this is an arrayref
S<< I<[item, item, ...]> >> where each I<item> is either a plain string
or a sub-array of I<[format properties...]> describing a local style
to be appled to the immediately-following text string.

For example B<["John Brown"]> means just the string "John Brown", whereas
B<[[color =E<gt> "red", "bold"], "John Brown"]> means insert 
"John Brown" in red, bold text, overriding the original style of
the {token}.

Local styles are needed only to override the original style 
in the document, for example to style different parts of the
content differently or to use styling known only at run-time.

=head1 clean_rsids($context);

I<Note: This is handled automatically by the Mail Merge engine.  You only
need to call C<clean_rsids> yourself if you directly clone content 
previously created using LibreOffice.>

This unpleasant hack removes special "rsid" styles inserted by some
versions of LibreOffice to track (AFAICT) changes or undo history.

LibreOffice may insert special spans around every edit, using unique
text styles containing an B<officeooo:rsid> property.  If these spans
are cloned, Libre Office will crash because it expects their styles to
be referenced exactly once.

Gory detail: Every span in $context (which may be the document body)
is examined; if it references a
text style with a 'officeooo:rsid' attribute in a descendant 
style:text-properties node, then that attribute is removed.
If the text-properties contains other attributes then everything
else is left as-is (this is the case when the style has an additional
purpose besides holding an rsid attribute).  
If the text-properties node has no other
attributes it is deleted, and if the ancestor style has no surviving
text-properties then the style is deleted and the span which
referenced it is erased, moving up the span's childen.

=head1 SEE ALSO

L<ODF::lpOD_Helper>, L<Sreadsheet::Edit>

=for comment The command-line tool B<ODFedit> provides access to some
=for comment features of ODF::MailMerge without writing Perl code.
=for comment C<cpanm App::ODFedit> will install it.

=head1 AUTHOR

Jim Avera (jim.avera at gmail)

=head1 LICENSE

CC0 1.0 / Public Domain.   However this requires ODF::lpOD to function so
as a practical matter you must comply with ODF::lpOD's license.

=cut

#end
