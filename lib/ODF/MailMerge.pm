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

use Scalar::Util qw/refaddr blessed/;
use List::Util qw/first any none all max min sum0/;
use List::MoreUtils qw/before after uniq/;
use Data::Dumper::Interp 6.004
       qw/visnew ivis dvis dvisq ivisq vis visq addrvis/;
use Spreadsheet::Edit::Log qw/oops btw/;
use Clone ();

use ODF::lpOD;
use ODF::lpOD_Helper 6.001 qw/:DEFAULT
                              PARA_COND
                              Hr_MASK
                              arraytostring hashtostring/;

use constant ROW_COND => "table:table-row";
use constant ROW_OR_PARA_COND => Hor_cond(PARA_COND, ROW_COND);
use constant ROW_OR_BODYROOT_COND => "table:table-row|office:text";

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
sub _to_content_list(_) {
  my $val = shift;
  # Convert hash value which is a single value or [content spac]
  # to a [list of [content spec]s].
  #
  # A [content spec] is a list of "text strings" and [style descriptor]
  # sub-arrays which apply to the immediately-following text string
  # (see ODF::lpOD_Helper for details).
  #
  if (ref $val) {
    croak ivis 'Value contains an illegal ref type (not ARRAY): $val'
      if any{ref($_) && ref($_) ne "ARRAY"} $val, eval{@$val};

    if (none{ref} @$val) {
      # [all...non-refs] must be ["str"] or ["str1", "str2"]
      $val = [ map{ [$_] } @$val ];  # --> [ ["str1"], ["str2] ]
    }
    elsif (all{ref} @$val) {
      # [ [...], [...], [...] ]
      # Must be list of [content subarrays]  -- OK AS IS
      croak ivisq 'Invalid replacement value $val'
        unless all{ any{!ref} @$_ } @$val; # [content] must incl a "str"
    }
    else { # [ mixed refs and "strings" ]  -- must be a single [content] spec
      croak ivisq 'Invalid [content spec] replacement value $val'
        if any{ ref && any{ref} @$_ } @$val;
      $val = [ $val ];
    }
  }
  elsif (defined $val) {
    $val = [ [$val] ]; # "single string" --> [ ["string"] ]
  }
  $val
}

sub _para_to_rop($) {
  my $maybe_para = shift // oops;
  #if (my $row = $maybe_para->parent(ROW_COND)) {
  if (my $row = eval{ $maybe_para->Hself_or_parent(ROW_COND) }) {
    oops unless $row->tag eq "table:table-row"; ###TEMP
    return wantarray ? ($row, "row") : $row
  } else {
    oops unless $maybe_para->tag =~ /^text:[ph]$/; ###TEMP
    return wantarray ? ($maybe_para, "paragraph") : $maybe_para
  }
}
sub _mk_tokhash_key($$) {
  my ($rop, $tokname) = @_;
  refaddr($rop)."/$tokname";
}

# This encapsulates the common token processing in both dryrun and substitution
# passes.  Usually replacement values are saved by the first pass and so
# this is not called on the 2nd pass, but in some cases (multiple instances
# of the same tokname in a single paragraph) the 2nd pass has to re-process
# a token from scratch.
#
# Returns () if the token should not be replaced, otherwise man details
# including a (ref to) array of [content] specs.
sub _get_content_list($$$$) {
  my ($m, $tokname, $users_hash, $custom_mods) = @_;
  my $val = $users_hash->{$tokname} // $users_hash->{'*'};
  return undef
    unless defined($val);
  my $token = $m->{match};
  my $para  = $m->{para};
  if (ref($val) eq "CODE") {
    (my $return_op, $val) = $val->($tokname, $token, $para, $custom_mods);
    croak("callback returned Hr_SUBST without a value or vice-versa: $token")
      if !defined($val) ^ !($return_op & Hr_SUBST);
    return undef
      unless defined($val);
  } else {
    croak "Invalid modifer ",visq(":$_")," in token $token",
          "\n(A callback is required to use custom modifiers)\n"
      for @$custom_mods;
  }
  my $content_list = _to_content_list($val);
btw visnew->ivisq('CCC $val --> $content_list') if $debug;
  $content_list
}

sub _get_cond_expr($) {
  my $std_mods = shift;
  my $cond_expr;
  foreach (@$std_mods) {
    my $cexpr;
    if (/^rep/) {
      if    (/^rep_first$/)     { $cexpr = '$i==0' }
      elsif (/^rep_mid$/  )     { $cexpr = '$i>0 && $i<$N' }
      elsif (/^rep_even_mid$/)  { $cexpr = '$i>0 && $i<$N && int($i%2)==0' }
      elsif (/^rep_odd_mid$/)   { $cexpr = '$i>0 && $i<$N && int($i%2)==1' }
      elsif (/^rep_last$/ )     { $cexpr = '$i==$N' }
      elsif (/^rep_even_last$/) { $cexpr = '$i==$N && int($i%2)==0' }
      elsif (/^rep_odd_last$/)  { $cexpr = '$i==$N && int($i%2)==1' }
      elsif (/^rep_only$/)      { $cexpr = '$N==1' }
      elsif (/^rep=(.*)$/ ) {
        croak "Unsafe/disallowed expression ",visq($1)," in ",visq($_)
          if do{ local $_ = $1;
                 /[\@:\\]|\$(?![iN]\b)/a
                 or grep{ !/(?:int|i|N|[0-9]+)$/ } /(\w+)/g };
        $cexpr = $1;
      }
      else { oops } #out of sync changes to std_mod definitions?
    }
    if (defined $cexpr) {
      croak "Multiple instantiation conditions not allowed in ",
            visq(join ":", @$std_mods)
        if defined($cond_expr);
      $cond_expr = $cexpr;
    }
  }
 return $cond_expr
}

sub _rt_dryrun($$$) {
  my ($context, $users_hash, $tokhash) = @_;

  my @matches = $context->Hsearch($token_re, multi => TRUE);
  for my $m (@matches) {
    my $token = $m->{match};
    my ($tokname, $std_mods, $custom_mods) = _parse_token($token);
    my $content_list
            = _get_content_list($m, $tokname, $users_hash, $custom_mods);
    next
      unless defined $content_list;
    my $cond_expr = _get_cond_expr($std_mods);
    my ($rop, $rop_name) = _para_to_rop($m->{para});
    my $tokhash_key = _mk_tokhash_key($rop, $tokname);
    if (exists $tokhash->{$tokhash_key}) {
      croak "The same token name may not appear multiple times in the same\n",
            "$rop_name if the token has multiple values and/or when\n",
            "conditional instantiation is used:\n$token\n"
        if @$content_list > 1 or defined $cond_expr;
      next; # 2nd instance will be parsed again in the substitution pass
    }
    $tokhash->{$tokhash_key} = {
      rop          => $rop,
      tokname      => $tokname,
      cond_expr    => $cond_expr,
      content_list => $content_list,
      token        => $token, # just for debugging?
    };
  }#foreach token in context
}# _rt_dryrun

sub _rt_dosubst($$$$) { # returns Hreplace result list
  my ($context, $users_hash, $tokhash, $to_deletes) = @_;
  $context->Hreplace($token_re, sub {
    my $m = shift;
    my $token = $m->{match};
    my ($tokname, $std_mods, $custom_mods) = _parse_token($token);
    my ($rop, $rop_name) = _para_to_rop($m->{para});
    my $tokhash_key = _mk_tokhash_key($rop, $tokname);

    my $content_list;
    if (my $info = $tokhash->{$tokhash_key}) {
      $info = $info;
      $content_list = $info->{content_list} // oops;
btw dvis 'XX retrieved $tokhash_key -> $info $content_list' if $debug;
      oops dvis '$m\n$info\n' if @$content_list > 1;
    } else {
      # A token is not in %tokhash if it is in an added (replicated) rop,
      # or the 2nd instance of the same token in rop (in which case
      # multi-values are not allowed).
      $content_list
        = _get_content_list($m, $tokname, $users_hash, $custom_mods);
btw dvis 'YY *no* info, $users_hash->{$tokname} $content_list' if $debug;
      return(0)
        unless defined $content_list;
      oops dvis '$token' if @$content_list > 1;
    }

    my $content = $content_list->[0];
    foreach (@$std_mods) {
      if ($_ eq "nb") {
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
      elsif (/^rep/) { }  # handled in first pass
      elsif (/^del/) {
        my $elt =
          $_ eq "delempty" ? $rop :
          $_ eq "delrow"   ? $m->{para}->Hself_or_parent(ROW_COND)  :
          $_ eq "delpara"  ? $m->{para}->Hself_or_parent(PARA_COND) :
          /^del=(.+)$/     ? $m->{para}->Hself_or_parent($1)        :
          oops;
        if (none { !ref && length } @$content) {
          $to_deletes->{refaddr $elt} //= [1, $elt];
        } else {
          # Non-empty content in this token; suppress deletion
          # even if another token with :del* is empty
          $to_deletes->{refaddr $elt} = [0, $elt];
        }
      }
      else { oops dvis '$_ $std_mods $m' }
    }

    return (Hr_SUBST, $content);
  }, debug => $debug);
}#_rt_dosubst

sub _rt_replicate($$) {
  my ($subtree_root, $tokhash) = @_;
  # Find groups of adjacent rops containing alternative templates to
  # instantiate (possibly-)multi-value tokens.  Replace the group by
  # one or more rops, sufficient for the maximal number of values of
  # any token they contain ("" will be supplied for 'missing' values
  # of tokens with fewer values than the maximal token in a rop).
  #
  # These groups may be:
  #   1. A lone regular rop (no conditionals)
  #
  #   2. A regular rop followed by conditionals (does not include
  #      any *following* regular rop, which if present starts a new group).
  #
  #   3. A set of conditional rops not preceded by a regular rop

  # Build hash of all rops containg any tokens
  my %rophash; # [rop, cond_expr, tokinfo_list, maxN]
  foreach my $info (values %$tokhash) {
    # info->{rop tokname cond_expr content_list token}
    my $rop = $info->{rop};
    my $ropinfo = $rophash{refaddr $rop}
                             //= {rop => $rop, tokinfos => [], maxN => 0};
    if (defined(my $tok_cexpr = $info->{cond_expr})) {
      if (defined(my $rop_cexpr = $ropinfo->{cond_expr})) {
        croak "Conflicting conditionals in the same row:",
              visq($tok_cexpr)," for {",$info->{tokname},"} vs. ",
              visq($rop_cexpr)," for another token in ",refaddr($rop)
        if $rop_cexpr ne $tok_cexpr;
      } else {
        $ropinfo->{cond_expr} = $tok_cexpr;
      }
      btw dvis 'C3 $tok_cexpr $info $ropinfo' if $debug;
    }
    push @{ $ropinfo->{tokinfos} }, $info;
    $ropinfo->{maxN} = max($ropinfo->{maxN}, scalar(@{$info->{content_list}}));
  }
btw dvis 'RRR1 completed %rophash' if $debug;

  my sub _process_group(@) {
    my @group = @_;
    my $first_rop = $group[0];
    my $first_ropinfo = $rophash{refaddr $first_rop};

    # If the first is unconditional, give it an always-true condition
    # but move it to the end of the search order so it will be used only
    # if none of the conditional rops work
    if (!defined $first_ropinfo->{cond_expr}) {
      foreach my $tokinfo (@{ $first_ropinfo->{tokinfos} }) {
        oops dvis '$first_rop $first_ropinfo $tokhash' if defined $tokinfo->{cond_expr};
      }
      $first_ropinfo->{cond_expr} = "1";
      push @group, (shift @group) ;
    }

    # To keep this logic simple, the appropriate template is always cloned
    # and the copy inserted before $first_rop; at the end all templates
    # are deleted, leaving only the clones behind.
    my $N = $rophash{refaddr $first_rop}->{maxN};
btw dvis 'AAA $N $first_ropinfo @group' if $debug;
    for (my $i=0; $i < $N; $i++) {
      my $templ;
      foreach (@group) {
        # Doing string eval using $i & $N
        my $ok = eval $rophash{refaddr $_}->{cond_expr}
                    // oops dvis '$@ $_ $rophash{refaddr($_)}';
        if ($ok) {
          $templ = $_;
          last
        }
      }
      croak "No conditionally-instantiatable row matches \$i=$i \$N=$N\n",
            "The tokens brearing instantiation conditions are:\n   ",
            join("\n   ",
                 map{ uniq
                      grep{/:rep/} map{ $_->{token} }
                      @{ $rophash{refaddr $_}->{tokinfos} }
                    } @group
                ), "\n"
        unless $templ;
      if ($templ == $subtree_root) {
        # Replication not possible when top context is the (one and only) rop
        unless ($N == 1) {
          my $info = $rophash{refaddr $templ}{tokinfos}[0];
          my (undef, $rop_name) = _para_to_rop($templ);
          croak "Replication to handle the $N-value token ", $info->{token},
                " is not possible\n",
                "because it is in a $rop_name which *is* the top context (",
                addrvis($subtree_root),")\n"
        }
        return;
      }
      my $new_rop = $templ->clone;
      $first_rop->insert_element($new_rop, position => PREV_SIBLING);
btw ivis 'BBB inserted $new_rop as PREV_SIB of $first_rop\n' if $debug;
      foreach my $tokinfo (@{ $rophash{refaddr $templ}->{tokinfos} }) {
        my $tokname = $tokinfo->{tokname} // oops;
        my $old_info = $tokhash->{ _mk_tokhash_key($templ, $tokname) };
        my $new_key = _mk_tokhash_key($new_rop, $tokname);
        oops if exists $tokhash->{$new_key};
        $tokhash->{$new_key} = {
          # This will be used by the Hreplace callback to find the value
          #rop          => $new_rop,
          #tokname      => $tokname,
          #cond_expr    => $old_info->{cond_expr}, # just for debugging??
          content_list => [ $old_info->{content_list}->[$i] // [""] ],
          #token        => $old_info->{token}, # just for debugging??
        };
btw dvis 'B B Created $new_key $tokhash->{$new_key}' if $debug;
      }
btw dvis 'C C $i $new_rop' if $debug;
    }
    foreach my $rop (@group) {
      btw ivis 'D D Deleting $rop' if $debug;
      $rop->delete;
      ### FOR DEBUG (not necessary)
      foreach my $tokname(map{$_->{tokname}}
                          @{ $rophash{refaddr $rop}{tokinfos} }) {
        my $key = _mk_tokhash_key($rop, $tokname);
        btw dvis 'Deleting OBSOLETE tokhash $key ...' if $debug;
        delete $tokhash->{$key};
      }
    }
  }

  # Find groups of alternative conditional rops and expand/collapse each one
  my %seen;
  foreach my $ropaddr (keys %rophash) {
    next if $seen{$ropaddr}++;
    my $ropinfo = $rophash{$ropaddr};
    my $rop = $ropinfo->{rop};

    my @group = ($rop);
    if ($ropinfo->{cond_expr}) {
      # Search preceding adjacents to find the first in the group
      my $elt = $rop;
      while ($elt = $elt->prev_sibling) {
        my $addr = refaddr $elt;
        last unless defined(my $ropinfo = $rophash{$addr});
        last if $seen{$addr}++;
        push @group, $elt;
        last if !defined $ropinfo->{cond_expr}; # stop *on* a non-conditional
      }
    }
    # Search following adjacents to find the last in the group
    my $elt = $rop;
    while ($elt = $elt->next_sibling) {
      my $addr = refaddr $elt;
      last unless defined(my $ropinfo = $rophash{$addr});
      last if !defined $ropinfo->{cond_expr}; # stop before a non-conditional
      last if $seen{$addr}++;
      push @group, $elt;
    }
    # N.B. Each isolated non-conditional rop is a "group", which will be
    # replicated if it contains multi-valued tokens

    _process_group(@group);
  }
  foreach my $ropaddr (keys %rophash) {
    oops dvis 'missed $ropaddr' unless $seen{$ropaddr};
    btw dvis 'seen: $ropaddr' if $debug;
  }
}#rt_replicate

sub replace_tokens($$@) {
  my ($context, $hash, %opts) = @_;
  local $debug = $debug || $opts{debug};
oops unless blessed($context);

  unless (caller eq __PACKAGE__ or !$context->{parent}) {
    my $doc = $context->document();
    eval { $doc->Hclean_for_cloning() };
    oops dvis '$context $context->{parent} $doc\n$@\n',fmt_tree($context, ancestors=>1) if $@;
  }

# 1. Do a "dry-run" (search-only) pass to locate all tokens
#    and save information about them in %tokhash including
#    values and std_modifiers.
#    Conditional-instantiation :modifiers (only) are evaluated
#    and the resulting cond_expr, if any, saved.
  my %tokhash;
  _rt_dryrun($context, $hash, \%tokhash);
  btw dvis 'AFTER DRY-RUN: %tokhash' if $debug;
  #btw(Data::Dumper->new([\%tokhash])->Indent(1)->Maxdepth(2)->Dump) if $debug;

# 2. Scan %tokhash to identify template groups (either a lone regular
#    rop which contains multi-value tokens, or adjacent rops containing
#    tokens bearing instantiation conditions pluse possibly one regular rop).
#
#    Replicate/reduce as needed, leaving exactly one rop for each value
#    of all multi-value tokens in the rop (defaulting to "" if one token
#    has fewer values than another).  Adjusts %tokhash entries to match.
#
#    Replace the list of all values with the one specific value in
#    the %tokhash entry
  _rt_replicate($context, \%tokhash);
btw dvis 'AFTER REPLICATE: %tokhash\ncontext=',fmt_tree($context) if $debug;

# 3. Do Hreplace.  In the callback:
#      If rop is not in %tokinfo:
#        (Re)parse the token
#      else
#        Fetch saved values & std_modifiers
#      (croak if multiple values at this point)
#
#      Apply std_mods to the value
#      return (Hr_SUBST, [content])
  my %to_deletes;
  my @rr = _rt_dosubst($context, $hash, \%tokhash, \%to_deletes);

# 4. Modify table cells to implement ":spandown" or ":delinteriorborders"
  #_fixup_tables(\%toklist);  # FIXME todo

# 5. Delete elements which contained token(s) with :del* modifiers where
#    all such tokens were replaced by ""
  foreach (values %to_deletes) {
    my ($to_delete, $elt) = @$_;
    if ($to_delete) {
      btw ivis 'DELETING due to :del* : $elt ',vis($elt->Hget_text) if $debug;
      $elt->delete;
    } else {
      btw ivis 'KEEPING $elt because some tokens are not empty' if $debug;
    }
  }

  # ??? should replace count be reduced by the number of tokens in
  # objects removed via $to_delete ???
  return scalar(@rr)
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

  $context->document->Hclean_for_cloning(); # remove 'rsid' styles

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

  # Ordinarily replace_tokens() simply ignores {token}s which are
  # not being replaced.  However during Mail Merge every token should
  # have some value.  This wrapper callback enforces that.
  my sub wrapper_cb {
    my ($tokname, $token, $para, $custom_mods) = @_;
    my $return_op = Hr_SUBST;
    my $key = exists($hash->{$tokname}) ? $tokname :
              exists($hash->{'*'}) ? '*' :
              croak "Unhandled token ", vis($token),
                    " (the hash has no entry for '$tokname' or '*'";
    my $val = $hash->{$key} //
              croak "Unhandled token ", vis($token),
                    " (the hash entry for '$key' contains undef)";
    if (ref($val) eq 'CODE') {
      ($return_op, $val) = $val->(@_);
      croak "Unhandled token ", vis($token),
            ivis '; the callback in hash{$key} returned ($return_op,$val)\n'
        unless ($return_op & Hr_SUBST)==0 || defined $val;
    }
    return ($return_op, ODF::MailMerge::_to_content_list($val))
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
