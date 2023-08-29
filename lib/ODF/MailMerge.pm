#!/usr/bin/env perl License: Public Domain or CC0
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
use List::Util qw/first any none all max min sum0/;
use Data::Dumper::Interp 6.004 qw/visnew ivis dvis vis visq/;
use Spreadsheet::Edit::Log qw/oops btw/;

use ODF::lpOD;
use ODF::lpOD_Helper 6.001 qw/:DEFAULT PARA_COND Hr_MASK/;

use constant ROW_COND => "table:table-row";

use Exporter 'import';
our @EXPORT = qw/replace_tokens/;

our $debug;

# Recognize anything probably intended as a {token} expression
our $token_re = qr/\{ (?<tokname> (?:[^:\{\}\\\n]+|\\[^\n])+    )
                      (?<mods>    (?: : (?:[^:\{\}\\]+|\\.)+ )* )
                   \}/xs;

# FIXME: Add :spanup (and :spanleft?) to span if *cell* content is blank

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

  my (@std_mods, @custom_mods);
  foreach (@mods) {
    s/\\(.)/$1/sg; # un-escape
    if ((my $equal_ix = index($_,'=')) >= 0) {
      croak "Invalid token ",vis($t),
            " -- newline or tab is allowed only in :modifier after '='"
        if substr($_,0,$equal_ix) =~ /[\t\n]/;
    }
    if (/^(?: nb|unfold|breakmulti
             |del(?:empty|row|para|=.*)
             |rep(?:_first|_mid|_last|=.*)
             |reptag=.*
          )$/xs) {
      push @std_mods, $_;
    } else {
      push @custom_mods, $_;
    }
  }
  return ($tokname, \@std_mods, \@custom_mods);
}

sub _dryrun_rt($$$@) {
  my ($context, $hash, $tokname_infos, %opts) = @_;

  my @matches = $context->Hsearch($token_re, multi => TRUE);
  for my $m (@matches) {
    my ($tokname, $std_mods, $custom_mods) = _parse_token( $m->{match} );

    # Get the possibly-multiple values for this token.  $val is undef
    # if the token is unknown and should not be replaced with anything
    # (either because there was no hash entry or the callback says so).
    my $val = $hash->{$tokname} // $hash->{'*'};
    my $return_op = Hr_SUBST;
    if (ref($val) eq "CODE") {
      ($return_op, $val)
        = $val->($tokname, $m->{match}, $m->{para}, $custom_mods);
    }
    next
      if ! defined $val;

    # Custom modifiers only make sense when using a callback
    croak "Invalid modifer ",vis(":$_")," in token ",$m->{match}
      for @$custom_mods;

btw dvis '_dryrun_rt: $tokname $return_op $val' if $debug;

    # Convert $val to a [list of values] if not alrady
    if (ref $val) {
      croak ivis 'Value contains an illegal ref type (not ARRAY): $val'
        if any{ref($_) && ref($_) ne "ARRAY"} $val, eval{@$val};

      if (none{ref} @$val) {
        # $val is already a [list of plain "strings"]
      }
      elsif (all{
              !ref($_) or   # "plain string"
              any{ref} @$_  # [ "str", [...], ... ]
             } @$val) {
        # There are 3 levels;  $val must already be a list containing
        # styled values like [...,[style desc],"string to be styled",...]
        # (more than 3 levels implies an invalid [content] descriptor)
      } else {
        # $val is an array with only one nested array level; it must
        # be a single single [styled content] descriptor
        $val = [ $val ];
      }
    } else {
      $val = [$val]; # a single "string"
    }

    # Check for conditional-instantiation modifiers
    my $cond_expr;
    foreach (@$std_mods) {
      if    (/^rep_first$/)     { $cond_expr = '$i==0' }
      elsif (/^rep_mid$/  )     { $cond_expr = '$i>0 && $i<$N' }
      elsif (/^rep_even_mid$/)  { $cond_expr = '$i>0 && $i<$N && int($i%2)==0' }
      elsif (/^rep_odd_mid$/)   { $cond_expr = '$i>0 && $i<$N && int($i%2)==1' }
      elsif (/^rep_last$/ )     { $cond_expr = '$i==$N' }
      elsif (/^rep_even_last$/) { $cond_expr = '$i==$N && int($i%2)==0' }
      elsif (/^rep_odd_last$/)  { $cond_expr = '$i==$N && int($i%2)==1' }
      elsif (/^rep=(.*)$/ ) {
        croak "Unsafe/disallowed expression in ",vis($_)
          if do{ local $_ = $1;
                 /[\@:\\]|\$(?![iN]\b)/a or (/(?!int\b)\w+/
               };
        $cond_expr = $1;
      }
    }

    # Save info about this instance of $tokname
    push @{ $tokname_infos }, {
      para         => $m->{para},
      para_voffset => $m->{para_voffset},
      cond_expr    => $cond_expr, # undef if not conditional
      values       => $val,
    };
  }#foreach token in context
}# _dryrun_rt

sub _dosubst_rt($$$$$) { # returns Hreplace result list
  my ($to_instantiate, $info_values, $i, $to_deletes, $to_keeps) = @_;
  $to_instantiate->Hreplace($token_re, sub {
    my $m = shift;
    my ($tokname, $std_mods, $custom_mods) = _parse_token( $m->{match} );
    btw dvis '_dosubst_rt Hreplace cb: $tokname $info_values $i' if $debug;
    return(0)
      unless exists $info_values->{$tokname};
    my $values = $info_values->{$tokname}
                  // oops dvis '$tokname $info_values $m->{match}';
    if (@$values == 0) { # *no* value; do not replace it
      return(0);
    }
    my $val = $values->[$i] // oops;
    my $content = ref($val) ? $val : [$val];
    foreach (@$std_mods) {
      if    (/^rep/) {
        next; # handled in _dryrun_rt
      }
      elsif ($_ eq "nb") {
        foreach (@$content) {
          next if ref;
          s/ /\N{NO-BREAK SPACE}/sg;
        }
      }
      elsif ($_ eq "unfold") {
        foreach (@$content) {
          next if ref;
          s/\n/ /sg;
        }
      }
      elsif ($_ eq "breakmulti") {
        my $text = join("", grep{! ref} @$content);
        if ($text =~ /\n./s) {
          croak "Mal-formed [content] (does not end with plain string)"
             if ref($$content[-1]);
          $$content[-1] .= "\n";
        }
      }
      elsif (/^del/) {
        my $to_delete =
             $_ eq "delempty" ? $to_instantiate :  # rop
             $_ eq "delrow"   ? $m->{para}->Hself_or_parent(ROW_COND)  :
             $_ eq "delpara"  ? $m->{para}->Hself_or_parent(PARA_COND) :
             /^del=(.+)$/     ? $m->{para}->Hself_or_parent($1)        :
             oops;
        if (none{ !ref && length } @$content) {
          # The replacement value is empty
          $to_deletes->{refaddr $to_delete} = $to_delete;
        } else {
          $to_keeps->{refaddr $to_delete} = 1;
        }
      }
      else { oops dvis '$_ $m->{match} $std_mods' }
    }
    return (Hr_SUBST, $content);
  }, debug => $debug);
}#_dosubst_rt

sub replace_tokens($$@) {
  my ($context, $hash, %opts) = @_;
  local $debug = $debug || $opts{debug};

  $context->get_document->Hclean_for_cloning() unless caller eq __PACKAGE__;

  # Perform a dry-run to locate all the tokens containing defined values.
  {
    my %tokname_infos;
    _dryrun_rt($context, $hash, \%tokname_infos, %opts);

btw dvis '%tokname_infos' if $debug;

    # Segregate templates for a given token name into groups to instantiate
    # together taking into account the number of values for the token name.
    # Each group has
    #   - a lone unconditional token
    #   - an unconditional token followed by conditional token(s)
    #   - conditional token(s) not preceded by an unconditional token.
    #
    # Grouped templates must be in adjacent rops
    # (rop=row, or para if not in a table).
    # Multiple templates in the *same* rop are allowed but not well supported
    # (FIXME - replicate within the rop?)
    #
    # rops are replicated as needed so that there are enough templates
    # for the number of values (max of all tokens in the rop group),
    # and the templates are edited to make their conditions match exactly
    # one value index.
    #
    # Each time a template is replicated, *all* templates for any tokname
    # in the same rop(s) are replicated similarly.  For example
    #    {TokA}       {TokB}
    # becomes
    #    {TokA :_repi=0}       {TokB :_repi=0}
    #    {TokA :_repi=1}       {TokB :_repi=1}
    #    ...                    ...
    # up to the maximum value index for TokA or TokB ("" is substituted for
    # conditional tokens whose _repi exceeds the value range).

...find max $i for tokens in same rop
...expand templates for each tokname to accomodate the the max $i
   So afterwards



    for my $tokname (keys %tokname_infos) {
      my $infos = $tokname_infos{$tokname};
      my @group;
      for my $info (@$infos) {
        my $rop = $info->{para}->parent(ROW_PARA) // $info->{para};
        unless (@group) { @group = ([$rop, $info]); next }
        my $prev_sib = $rop->next_sibling;
        my $follows_prev = ($prev_sib && $prev_sib == $group[-1][0])
        if ($follows_prev or ! $info->{cond_expr}) {
          # This one starts a new group, either because it is not adjacent
          # or it is adjancent but is unconditional (and not the first).
          _setup_group(\@group);
          @group = ([$rop, $info]);
          next
        }
        push @group, [$rop, $info];
      }
      _setup_group(\@group) if @group;
    }
  }

========
  my $repl_count = 0;
  # Visit rops in random order.  If it is a 'regular' row (not bearing :rep*
  # modifiers), look for immediately-following alternatives template rows
  # and replace the group with the final result.
  my (%to_deletes, %to_keeps);
  foreach (keys %rop_info) {
    my $info = $rop_info{$_} // next; # previously deleted
    next
      if defined $info->{rep_expr};  # not a 'regular' row
    delete $rop_info{$_};

    my $rop = $info->{rop};
    my @templates = ([$rop, "1"]);
    while (my $next_elt = $templates[-1][0]->next_sibling) {
      last unless (my $next_info = $rop_info{refaddr $next_elt});
      last unless defined (my $rep_expr = $next_info->{rep_expr});
      push @templates, [ $next_info->{rop}, $rep_expr ];
      delete $rop_info{refaddr $next_elt};
    }
    push @templates, shift(@templates);
    # Now @template holds special template rows, if any, followed by
    # the "regular" row.  Each has an expression string (referencing $i & $N)
    # which evals true if that row should be instantiated. The expr string
    # for the regular row is "1" so it will always be used if none others
    # are appropraite (or if there are no alternatives).

btw dvis '  @templates' if $debug;

    my $N = max( map{scalar(@$_)} values %{$info->{values}} );
    for my $i (0..$N-1) {
      my $templ;
      foreach (@templates) {
        if (eval $_->[1]) {
          $templ = $_->[0];
          last
        }
      }
btw dvis '  $i $N $templ' if $debug;
      my $to_instantiate = $templ->clone;
      $rop->insert_element($to_instantiate, position => PREV_SIBLING);
      my @r = _dosubst_rt($to_instantiate, $info->{values}, $i,
                          \%to_deletes, \%to_keeps);
      btw 'SUBST RESULTS: ',fmt_Hreplace_results(@r) if $debug;
      $repl_count += scalar(@r);
    }

    # Finally, delete all the template rows.
    foreach (@templates) {
      btw dvis 'Deleting template $_ ',fmt_node($_->[0]) if $debug;
      $_->[0]->delete
    }
  }
  oops dvis 'Leftover %rop_info\n' if keys %rop_info;

  # Delete rows, etc. with tokens containing :del* if all such tokens
  # in the rop had empty values.
  foreach my $address (keys %to_deletes) {
    if ($to_keeps{$address}) {
      btw ivis 'KEEPING $elt because only some tokens with :del* are empty' if $debug;
      next;
    }
    my $elt = $to_deletes{$address};
    btw ivis 'DELETING $elt due to :del*' if $debug;
    $elt->delete
  }

  return $repl_count
}

package ODF::MailMerge::Engine;

use ODF::lpOD;
use ODF::lpOD_Helper;
use Data::Dumper::Interp;
use Carp;
our @CARP_NOT = ("ODF::MailMerge", "ODF::lpOD_Helper", "ODF::lpOD");

sub new {
  my $class = shift;
  my ($context, $proto_tag, %opts) = @_;

  $context->get_document->Hclean_for_cloning(); # remove 'rsid' styles

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
    my $rop = Hr_SUBST;
    my $val = $hash->{$tokname} // $hash->{'*'};
    if (ref($val) eq 'CODE') {
      ($rop, $val) = $val->(@_);
    }
    unless (defined $val) {
      # Ordinarily replace_tokens() simply ignores {token}s which are
      # not being replaced.  However during Mail Merge every token should
      # have some value
      croak "Unhandled token ",vis($m->{match}),
            " (the hash has no entry for '$tokname' or '*')";
    }
    return ($rop, $val)
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
 #   1. Find the prototype table containing the token "{mmproto}".
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
such as removing lines when there is no value to substitute.

A "mail merge" function replicates a template object (e.g. table or section)
as many times as needed to plug in values from multiple data records.

=head1 THE PARADIGM

First, manually create a prototype ODF document using e.g. LibreOffice,
containing static content and {tokens} to be interpolated, formatted
as desired.  To use "mail merge", create a table or other ODF construct
which represents a single entry or record,
with {token}s where data values should be plugged in.

Substituted values will have the same formatting as the tokens which were
replaced.  This is quite powerful.

For example, to generate a multi-column "member directory", create a
prototype table with tokens like {Name}, {Address}, etc.
using any desired styles;
place that table in a Section with the desired number of columns.

When processed, the table will be cloned and appended within
it's Section, flowing into successive columns and new pages as needed.
The prototype table's properties can be set to prevent breaking entries
at column/page boundaries, and control borders, inter-entry spacing, etc.

=head1 SIMPLE SUBSTITUTION

=head2 $count = replace_tokens($context, $hash);

This function replaces tokens without using the mail-merge mechanism.

$context is the document body or any descendant; $hash maps token names
to replacement values as described at "TOKEN REPLACEMENT".

All instances of tokens in $context are replaced if their names
exist in %$hash.
Token names not in %$hash are left as-is unless
the hash contains a '*' wildcard entry.

=head1 MAIL MERGE OVERVIEW

The essential "mail merge" capabilities are:

=over

=item 1.

A template of some kind specifies how to display data from
one database record, with db field references where field values
should be plugged in.  That template is copied as many times as there are
database records, plugging in specific values for the field references.

=item 2.

One or more fields may have *no* value in a particular record,
in which case
I<the containing row, paragraph etc.can be deleted>
to avoid leaving undesirable blank space.
For example a mailing list may allow a secondary addressee line
which most of the time is not used.

=item 3.

One or more fields may have *multiple* values.
In that case
I<part of the containing row, paragraph, etc. can be
replicated to accomodate extra values for the same field.>
For example a personnel directory may allow each person
to have any number of telephone numbers.

=back

=head1 MAIL MERGE API

ODF::MailMerge does not care where the data comes from, as long as you
can provide a hash table which maps token names to values for a particular
record.

The example in the SYNOPSIS reads a spreadsheet using L<Spreadsheet::Edit>,
which provides just such a hash via the tied variable "%crow" (current row);
this hash maps column titles (among other things) to data values in the
row being visited by 'apply'.
Therefore tokens {Name} and {Address} would be
replaced by appropriate values from the "Name" and "Address" columns.

=head2 $engine = ODF::MailMerge::Engine-E<gt>new($context, $proto_tag);

Create a new mail-merge engine which will replicate the protototype
object containing $proto_tag.  The proto object could be a I<table>
(good for things like personnel-directory), a I<section> (might be
used for form letters), or any other ODF text container.

I<$context> is usually the document body e.g. C<$doc-E<gt>get_body>.

I<$proto_tag> is a tag used to locate the prototype object within $context.
The tag may appear anywhere within the object and will be deleted
(and so has no effect on the final result).

=head2 B<$engine-E<gt>add_record($hashref);>

The prototype object is first cloned and appended to any previous copies.

Then all {key} or {key:modifier...} strings in the clone are
replaced by looking up "key" in the specified hash as described
at "TOKEN REPLACEMENT" below. An exception occurs if an unhandled
token is found.

=head2 B<$engine-E<gt>finish();>

This must be called after the last C<add_record> to clean up.
It deletes the prototype,
leaving behind only the clones with instantiated values.

=head1 TOKEN REPLACEMENT

In the hash you provide, B<keys> are token names without the curly
brackets or :modifiers.
For example, the key "First Name" would be used for token "{First Name}"
or "{First Name:...}" .

The hash key B<'*'> is a wildcard, used if there is no entry for
a token name.

Token names may contain internal spaces but leading and trailing spaces
around the name (but not inside :modifiers) are ignored.
Literal : { or } characters must be backslashed i.e. \: \{  or \}.

A B<hash value> may be:

  * "string"                      - a replacement value string
  * [[Style info], "string", ...] - a styled replacement value
  * [list of possibly-multiple replacement values]
  * CODE ref                      - a callback (see "CALLBACKS")

=head2 [Styled content] values

See L<ODF::lpOD_Helper> for details.   In brief, these are refs to arrays
containing [style spec] sub-arrays and plain strings, where a [style spec]
describes a local style to be applied to the immediately following text string.
As used here, the first item I<must> be a [style spec] sub-array.

For example B<[[color =E<gt> "red", "bold"], "John Brown"]> means substitute
"John Brown" in red, bold text, overriding the style of
the {token}.  Multiple pairs describe adjacent but differently-styled segments.

Styled values are not needed unless you must override the original style
of the {token}.

=head2 Token :modifiers

:modifiers appended to a token name change the replacement value
or have other effects.
For example B<{Address:nb}> would be replaced by
the value given by C<$hash-E<gt>{Address}> with all regular spaces
replaced by non-breaking spaces.

The standard :modifiers are

  :nb         - Convert spaces to non-breaking

  :unfold     - Convert embedded newlines to spaces

  :breakmulti - Append newline if the value contains embedded newlines.

  :delrow, :delpara, :del=tag
              - Delete the containing row, paragraph, etc. if the
                token value is empty or missing ("" or undef).

  :rep_first, :rep_mid, :rep_last
              - See below.  Used to provide multiple templates used
                when replicating a row, paragraph, etc. to accomodate
                a multi-valued token.

=head2 Eliding Empty Lines (:delrow, etc.)

These modifiers cause the containing row, paragraph, etc. to be deleted
if the token value is "" or undef.

Note that the row, etc. is deleted if it's token's replacement value is
empty I<even if other tokens have values in the deleted row>.

=head2 Multi-value tokens

If a token has multiple values, then by default the
containing table row is replicated, or if the token is not in a table
then the containing paragraph.

A B<< :reptag=I<tag> >> modifier may be given if a larger construct
(not just the containing row or paragraph) should be replicated.
'tag' is an L<XML::Twig> search condition, usually an ODF tag name
such as I<table:table>.  To see the tags in an existing document, run this:

  perl -MODF::lpOD -MODF::lpOD_Helper -E "say fmt_tree_brief odf_get_document(shift)->get_body;" "/path/to/file.odt"

Where the following documentation refers to replicating "rows" it means
the appropriate ODF object type.

B<Replicating rows with more than one token>

A row is replicated enough times for the token with the most values.
Tokens which have fewer values are instantiated in the initial rows and
empty values ("") substituted in later rows.  For example, given

  ┌──────────────┬────────────────┬───────────────────────┐
  │{Name}        │ {Phone}        │ {Email}               │
  └──────────────┴────────────────┴───────────────────────┘

if the {Phone} token had four values and {Email} had two,
the result would be four copies of the row, looking like this:

  ┌──────────────┬────────────────┬───────────────────────┐
  │John Hancock  │ (415) 555-1212 │ j.hancock@gmail.com   │
  ├──────────────┼────────────────┼───────────────────────┤
  │              │ (650) 555-1212 │ j.hancock@hotmail.com │
  ├──────────────┼────────────────┼───────────────────────┤
  │              │ (800) 555-1212 │                       │
  ├──────────────┼────────────────┼───────────────────────┤
  │              │ (900) 888-7777 │                       │
  └──────────────┴────────────────┴───────────────────────┘

Next we'll see how to improve this by by eliminating interior borders;

Three additional template rows, which can have different formatting,
may be provided which are used for the first, middle and last rows,
as indicating by B<:rep_first>, B<:rep_mid> and B<:rep_last> modifiers
coded in any token:

  ┌──────────────┬────────────────┬───────────────────────┐
  │{Name}        │ {Phone}        │ {Email}               │
  └──────────────┴────────────────┴───────────────────────┘
  ┌──────────────┬────────────────┬───────────────────────┐
  │{Name}        │ {Phone}        │ {Email:rep_first}     │
  ╵              ╵                ╵                       ╵
  ╷              ╷                ╷                       ╷
  │{Name}        │ {Phone}        │ {Email:rep_mid}       │
  ╵              ╵                ╵                       ╵
  ╷              ╷                ╷                       ╷
  │{Name}        │ {Phone}        │ {Email:rep_last}      │
  └──────────────┴────────────────┴───────────────────────┘

(The extra space between rows is just for illustration to show
the absent horizontal borders).  The result after substitution:

  ┌──────────────┬────────────────┬───────────────────────┐
  │John Hancock  │ (415) 555-1212 │ j.hancock@gmail.com   │
  │              │ (650) 555-1212 │ j.hancock@hotmail.com │
  │              │ (800) 555-1212 │                       │
  │              │ (900) 888-7777 │                       │
  └──────────────┴────────────────┴───────────────────────┘

The specialzed template rows, if present, must immediately follow the
"main" template row which has no :rep* modifiers.

In this example the "main" template row is not used and is not instantiated
in the result.  If there was only a single value for each token
then the "main" template row would be used and the specialised
templates ignored.

===BEGIN EXPERIMENTAL, UNSUPPORTED FEATURE===

B<:rep=EXPR> indicates that the template row should be used when the Perl
expression EXPR is true.  While EXPR is evaluated,
B<$i> is the replicate index (first row is 0)
and B<$N> is the total number of replicates.

For example, the following five template rows could be used to
eliminate interior borders like in the above example, but also
alternate colors or other formatting of odd & even rows:

  ┌───────────────────────────────────────────────────────────┐
  │EVEN (first)   {Token Name:rep_first}                      │
  ╵                                                           ╵
  ╷                                                           ╷
  │EVEN (middle)  {Token Name:rep=$i>0 && $i<$N && ($i%2)==0} │
  ╵                                                           ╵
  ╷                                                           ╷
  │ODD (middle)   {Token Name:rep=$i>0 && $i<$N && ($i%2)==1} │
  ╵                                                           ╵
  ╷                                                           ╷
  │EVEN (last)    {Token Name:rep=$i == N && ($i % 2)==0}     │
  └───────────────────────────────────────────────────────────┘
  ╷                                                           ╷
  │ODD (last)     {Token Name:rep=$i == N && ($i % 2)==1}     │
  └───────────────────────────────────────────────────────────┘

===END EXPERIMENTAL, UNSUPPORTED FEATURE===

=head2 CALLBACKS

If a hash value is a sub reference, the sub is called with

  ($token_name, \%params)

I<$token_name> is the just the name "Foo" from "{Foo:modifiers...}".

I<\%params> contains additional parameters, including:

=over

B<token =E<gt> "{token:modifiers}"> -- the complete token being processed

B<< para =E<gt> <paragraph node> >> -- the paragraph containing the token

B<custom_mods =E<gt> ["mod1", "mod2", ...]>

This array contains unrecognized :modifier strings
(excluding the ':') found in the token.  It is up to your code
to do what it wants with them.
Note: An exception occurs if unrecognized :modifiers are encountered
when a callback is not being used.

=back

The callback's return values indicate whether and how to replace
the token.  The protocol uses the Hr_* constants exported
by L<ODF::lpOD_Helper>:

  return(Hr_SUBST, <value>)

B<< <value> >> may be any of the allowed hash values (except for a callback).
If a [list of values] is returned and there
is actually more than one value, then
the containing row will be replicated as described a "Multi-value tokens".

  return(0)

The token is not replaced, but left as-is, and processing continues.
This only makes sense if the token will somehow be processed later,
for example via a separate call to C<replace_tokens>.

FIXME: Define local MM_SUBST to avoid showing Hr_* dependencies?

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
