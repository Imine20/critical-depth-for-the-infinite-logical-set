#!/usr/bin/perl
use strict;
use warnings;
use Cwd qw(abs_path);
use File::Basename qw(basename dirname);
use File::Find qw(find);
use Digest::SHA qw(sha256_hex);
use JSON::PP;
use Fcntl qw(O_WRONLY O_CREAT O_EXCL);

# Portable dependency-evidence check. Never launches Lean, Lake, Git or builds.
# Canonical host paths go only to the explicitly local path-record argument.
my ($mode,$repo,$raw_paths,$receipt_path,$runtime,$manifest,$path_record)=@ARGV;
defined $path_record && @ARGV==7 or die "dependency checker arguments\n";
($mode eq 'source-built' || $mode eq 'lake-cache' || $mode eq 'trusted-cache') or die "dependency mode\n";
my $json=JSON::PP->new->canonical;
sub bytes {open my $f,'<:raw',$_[0] or die "cannot read checker input: $!\n";local $/;return <$f>;}
sub digest {open my $f,'<:raw',$_[0] or die "cannot read artifact: $!\n";my $h=Digest::SHA->new(256);$h->addfile($f);return $h->hexdigest;}
sub save_new {my ($p,$s)=@_;sysopen my $f,$p,O_WRONLY|O_CREAT|O_EXCL or die "new evidence output: $!\n";binmode $f;print {$f} $s or die "write evidence\n";close $f or die "close evidence\n";}
my %root_package=(Mathlib=>'mathlib',Batteries=>'batteries',Qq=>'Qq',Aesop=>'aesop',
  ProofWidgets=>'proofwidgets',ImportGraph=>'importGraph',LeanSearchClient=>'LeanSearchClient',
  Plausible=>'plausible',Cli=>'Cli');
my $lock=decode_json(bytes("$repo/lake-manifest.json"));
my %pins;
for my $p (@{$lock->{packages}}) {
  defined $p->{name} && defined $p->{rev} && $p->{rev}=~/\A[0-9a-f]{40}\z/ or die "nonimmutable lock\n";
  !exists $pins{$p->{name}} or die "duplicate lock package\n";
  $pins{$p->{name}}=$p->{rev};
}
my %allowed=map {$_=>1} values %root_package;
keys(%pins)==keys(%allowed) && !grep {!$allowed{$_}} keys %pins or die "unexpected package lock\n";
$raw_paths ne '' && $raw_paths!~/[\r\n\\]/ or die "unsafe/empty public path list\n";
my @given=split /:/,$raw_paths,-1;
!grep {$_ eq ''} @given or die "empty public path component\n";
my (%paths,%seen);
for my $given (@given) {
  $given=~m{\A/} || $mode eq 'lake-cache' or die "explicit public output roots must be absolute\n";
  my $canonical=abs_path($given);
  if ($mode eq 'lake-cache') {
    next unless defined $canonical && -d $canonical;
    my @matching=grep {my $p=abs_path("$repo/.lake/packages/$_/.lake/build/lib/lean");defined $p && $p eq $canonical} keys %pins;
    next unless @matching;
    @matching==1 or die "ambiguous package output root\n";
    !$seen{$canonical}++ or next;
    $paths{$matching[0]}=$canonical;
  } else {
    defined $canonical && -d $canonical or die "missing explicit public output root\n";
    my $pkg=basename($canonical);
    $allowed{$pkg} && !exists $paths{$pkg} && !$seen{$canonical}++ or die "duplicate/unapproved explicit public output root\n";
    $paths{$pkg}=$canonical;
  }
}
keys(%paths)==keys(%pins) or die "all nine locked public output roots are required\n";
for my $path (values %paths) {
  for my $own (qw(CriticalDepth CriticalDepthMathlib)) {
    for my $part ('',qw(.olean .olean.private .olean.server .ir .ir.sig .ilean)) {
      !-e "$path/$own$part" or die "own project artifact in public roots\n";
    }
  }
}
# Lean also searches its bundled library. Forbid fallback public/project roots.
for my $root (keys %root_package,qw(CriticalDepth CriticalDepthMathlib)) {
  for my $part ('',qw(.olean .olean.private .olean.server .ir .ir.sig .ilean)) {
    !-e "$runtime/lib/lean/$root$part" or die "public/project namespace in bundled runtime\n";
  }
}

my (%expected,%counts,$module_count);
$module_count=0;
if ($mode eq 'source-built') {
  my $receipt=decode_json(bytes($receipt_path));
  $receipt->{schema}==1 && $receipt->{status} eq 'ALL_PUBLIC_DEPENDENCIES_SOURCE_BUILT' &&
    exists $receipt->{cached_public_proof_artifacts_used} && !$receipt->{cached_public_proof_artifacts_used}
    or die "source receipt status\n";
  ref($receipt->{modules}) eq 'HASH' or die "source receipt modules\n";
  for my $module (sort keys %{$receipt->{modules}}) {
    $module=~/\A[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\z/ or die "receipt module identifier\n";
    my $r=$receipt->{modules}{$module};my ($root)=split /\./,$module;my $pkg=$root_package{$root};
    defined $pkg && $r->{package} eq $pkg && $r->{package_commit} eq $pins{$pkg} &&
      $r->{source_git_blob}=~/\A[0-9a-f]{40}\z/ && $r->{source_sha256}=~/\A[0-9a-f]{64}\z/
      or die "source package/pin record mismatch\n";
    (my $relative=$module)=~s{\.}{/}g;
    my $base=basename($relative);my $dir=dirname($relative);$dir='' if $dir eq '.';
    my %parts;
    for my $a (@{$r->{artifact_hashes}}) {
      $a->{file}=~/\A\Q$base\E\.(?:olean(?:\.(?:server|private))?|ilean|ir(?:\.sig)?)\z/ &&
        $a->{sha256}=~/\A[0-9a-f]{64}\z/ && $a->{bytes}=~/\A(?:0|[1-9][0-9]*)\z/ && !$parts{$a->{file}}++
        or die "invalid/duplicate artifact record\n";
      my $rel=($dir ne ''?"$dir/":'').$a->{file};
      !exists $expected{"$pkg/$rel"} or die "duplicate receipt artifact\n";
      $expected{"$pkg/$rel"}={sha256=>$a->{sha256},bytes=>0+$a->{bytes}};
    }
    $parts{"$base.olean"} && $parts{"$base.ilean"} or die "required main artifact part absent\n";
    if (grep {$parts{"$base$_"}} qw(.olean.server .olean.private .ir .ir.sig)) {
      !grep {!$parts{"$base$_"}} qw(.olean.server .olean.private .ir .ir.sig) or die "incomplete module artifact parts\n";
    }
    $counts{$pkg}++;$module_count++;
  }
  $module_count>0 && $module_count==$receipt->{module_count} &&
    $json->encode(\%counts) eq $json->encode($receipt->{package_counts}) or die "source receipt module counters\n";
}

my %actual;
for my $pkg (sort keys %paths) {
  my $root=$paths{$pkg};
  find({no_chdir=>1,wanted=>sub {
    my $file=$File::Find::name;
    !-l $file or die "symlink in public output tree\n";
    return unless -f $file;
    if ($mode eq 'source-built' && $file=~/\.(?:so(?:\.[0-9]+)*|dylib|dll|lib|a|o|bc|exe)\z/) {die "native artifact in source-only public outputs\n";}
    return unless $file=~/\.(?:olean(?:\.(?:private|server))?|ilean|ir(?:\.sig)?)\z/;
    my $relative=substr($file,length($root)+1);my $key="$pkg/$relative";
    $relative!~/[\r\n\\]/ or die "invalid artifact filename\n";
    my $hash=digest($file);my $size=0+(-s $file);
    if ($mode eq 'source-built') {
      exists $expected{$key} && $expected{$key}{sha256} eq $hash && $expected{$key}{bytes}==$size
        or die "unreceipted/changed public artifact: $key\n";
    }
    $actual{$key}={package=>$pkg,artifact=>$relative,sha256=>$hash,bytes=>$size};
  }},$root);
}
keys(%actual)>0 or die "no public proof artifacts\n";
if ($mode eq 'source-built') {keys(%actual)==keys(%expected) or die "missing receipted public artifact\n";}
my $lines=join '',map {$json->encode($actual{$_})."\n"} sort keys %actual;
save_new($manifest,$lines);
save_new($path_record,join(':',map {$paths{$_}} sort keys %paths)."\n");
print $json->encode({dependency_mode=>$mode,package_count=>0+keys(%paths),
  ($mode eq 'source-built'?(source_built_module_count=>$module_count):()),
  artifact_count=>0+keys(%actual),artifact_manifest_sha256=>sha256_hex($lines)}),"\n";
