#!/bin/sh
# Required main-source audit and separate fresh-artifact consumer.
# Bootstrap and independent-environment provenance belong to clean_replay.sh.
set -eu
set -f
release_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$release_root"
case "${CRITICAL_DEPTH_DEPENDENCY_MODE:-lake-cache}" in
  lake-cache) ;;
  *) printf 'The public release replay requires dependency mode lake-cache.\n' >&2; exit 2 ;;
esac
release_consumer_hash=14556a208ecf58045e5124c836e2e1bf662a46292d8856674b728a26f7cc25d5
release_consumer_marker='TRUSTED_CACHE_EXTERNAL_CONSUMER_PASSED call_count=3 imported_main_count=2 exact_three_count=5'
test "$(sha256sum mathlib-review/SourceConsumer.lean | cut -d ' ' -f 1)" = "$release_consumer_hash"
release_runs="$release_root/.verification/release"
mkdir -p "$release_runs"
test ! -L "$release_runs"
test "$(realpath "$release_runs")" = "$release_runs"
release_out=$(mktemp -d "$release_runs/run.XXXXXXXX")
release_passed=0
release_exit() {
  release_code=$?
  trap - 0
  if [ "$release_passed" -ne 1 ]; then
    printf 'REJECTED\n' > "$release_out/status.txt"
    printf 'Release replay rejected; local diagnostics: %s\n' "$release_out" >&2
    if [ "$release_code" -eq 0 ]; then release_code=2; fi
  fi
  exit "$release_code"
}
trap release_exit 0
trap 'exit 130' INT
trap 'exit 143' TERM
printf 'RUNNING\n' > "$release_out/status.txt"
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$release_out/start.utc"

# The JSON manifests contain repository-relative names, byte counts and hashes.
release_inputs() {
  perl - "$release_root" <<'PERL'
use strict; use warnings; use JSON::PP; use Digest::SHA; use File::Spec;
my $root=shift @ARGV;
my @files=qw(lean-toolchain lakefile.toml lake-manifest.json
  scripts/verify.sh scripts/verify_release.sh scripts/verify_public_dependencies.pl
  mathlib-review/CriticalDepthMathlib.lean mathlib-review/SourceConsumer.lean
  mathlib-review/ALIGNED_MATHEMATICAL_STATEMENTS.md mathlib-review/AUDIT_EXPECTED.txt
  mathlib-review/PAYLOAD_SHA256.txt mathlib-review/lean-toolchain
  mathlib-review/lakefile.toml mathlib-review/lake-manifest.json
  manuscript/shallow_logical_operators_depth_threshold.tex AUTHOR_SEMANTIC_APPROVAL.json);
my @entries;
for my $relative (@files) {
  my $path="$root/$relative";
  -f $path && !-l $path or die "missing/symlink input: $relative\n";
  open my $fh,'<:raw',$path or die "read input: $relative\n";
  my $hash=Digest::SHA->new(256); $hash->addfile($fh);
  push @entries,{file=>$relative,bytes=>0+(-s $path),sha256=>$hash->hexdigest};
}
print JSON::PP->new->canonical->pretty->encode(\@entries);
PERL
}

# Every package is an actual clean checkout at the revision in the lockfile.
# This supplements the lower verifier's immutable cache-artifact manifests.
release_packages() {
  perl - "$release_root" <<'PERL'
use strict; use warnings; use JSON::PP;
my $root=shift @ARGV;
sub run_git {
  my ($dir,@args)=@_;
  open my $fh,'-|','git','-c',"safe.directory=$dir",'-C',$dir,@args or die "launch git\n";
  local $/; my $s=<$fh>; close $fh or die "git failed\n"; return $s // '';
}
sub checkout {
  my ($dir,$untracked)=@_;
  my $head=run_git($dir,'rev-parse','HEAD'); chomp $head;
  $head=~/\A[0-9a-f]{40}\z/ or die "invalid checkout revision\n";
  my $status=run_git($dir,'status','--porcelain',"--untracked-files=$untracked");
  $status eq '' or die "checkout contains uncommitted source changes\n";
  return $head;
}
my $project=checkout($root,'all');
open my $fh,'<:raw',"$root/lake-manifest.json" or die "read lock\n";
my $lock=do {local $/; decode_json(<$fh>)};
my %expected=map {$_=>1} qw(mathlib batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible Cli);
my @packages;
for my $package (sort {$a->{name} cmp $b->{name}} @{$lock->{packages}}) {
  my ($name,$rev)=@{$package}{qw(name rev)};
  defined $name && delete $expected{$name} && defined $rev && $rev=~/\A[0-9a-f]{40}\z/
    or die "unexpected or mutable dependency lock\n";
  my $head=checkout("$root/.lake/packages/$name",'no');
  $head eq $rev or die "package HEAD differs from lock: $name\n";
  push @packages,{package=>$name,commit=>$head,tracked_source_clean=>JSON::PP::true};
}
!keys(%expected) or die "incomplete dependency lock\n";
print JSON::PP->new->canonical->pretty->encode({project_commit=>$project,
  project_worktree_clean=>JSON::PP::true,packages=>\@packages});
PERL
}

# Include all emitted Lean artifact parts, without assuming platform-specific parts exist.
release_artifacts() {
  perl - "$1" "$2" <<'PERL'
use strict; use warnings; use JSON::PP; use Digest::SHA;
my ($dir,$module)=@ARGV;
$module=~/\A(?:CriticalDepthMathlib|SourceConsumer)\z/ or die "artifact module\n";
my @entries;
for my $suffix (qw(.olean .ilean .olean.private .olean.server .ir .ir.sig)) {
  my $file="$module$suffix"; my $path="$dir/$file";
  if (!-e $path) {die "required artifact absent: $file\n" if $suffix eq '.olean' || $suffix eq '.ilean'; next;}
  -f $path && !-l $path && -s $path or die "invalid artifact: $file\n";
  open my $fh,'<:raw',$path or die "read artifact\n";
  my $hash=Digest::SHA->new(256); $hash->addfile($fh);
  push @entries,{file=>$file,bytes=>0+(-s $path),sha256=>$hash->hexdigest};
}
print JSON::PP->new->canonical->pretty->encode(\@entries);
PERL
}

release_inputs > "$release_out/inputs.before.json"
release_packages > "$release_out/checkouts.before.json"
# Capture the exact successful directory returned by this invocation, never enumerate old runs.
sh scripts/verify.sh > "$release_out/main-driver.local.log" 2>&1
cat "$release_out/main-driver.local.log"
test "$(grep -c '^CURRENT_SOURCE_AUDIT_RUN=' "$release_out/main-driver.local.log")" -eq 1
release_main=$(sed -n 's/^CURRENT_SOURCE_AUDIT_RUN=//p' "$release_out/main-driver.local.log")
case "$release_main" in "$release_root"/.verification/current/run.*) ;; *) exit 2 ;; esac
test -d "$release_main"
test ! -L "$release_main"
test "$(realpath "$release_main")" = "$release_main"
test "$(cat "$release_main/exit.txt")" -eq 0
test "$(cat "$release_main/dependency-mode.txt")" = lake-cache
cmp "$release_main/expected-audit-marker.txt" "$release_main/final-audit-marker.txt"
sha256sum -c "$release_main/inputs-before.local.sha256" > "$release_out/main-inputs.before.local.txt"
release_artifacts "$release_main" CriticalDepthMathlib > "$release_out/main-artifacts.before.json"
cp "$release_main/public-artifacts.after.jsonl" "$release_out/public-artifacts.before.jsonl"
release_lean=$(sed -n '1p' "$release_main/toolchain-paths.local.txt")
release_prefix=$(sed -n '2p' "$release_main/toolchain-paths.local.txt")
test "$(wc -l < "$release_main/toolchain-paths.local.txt")" -eq 2
test -x "$release_lean"
release_public=$(cat "$release_main/LEAN_PATH.local.txt")
test -n "$release_public"
unset LEAN_SRC_PATH
export LEAN_NUM_THREADS=1
# Main compilation and imported-artifact checking use exactly the same public dependencies.
export LEAN_PATH="$release_main:$release_public"
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$release_out/consumer-start.utc"
release_consumer_status=0
"$release_lean" -j 1 -M 6144 -DmaxHeartbeats=3000000 -R mathlib-review \
  -o "$release_out/SourceConsumer.olean" -i "$release_out/SourceConsumer.ilean" \
  mathlib-review/SourceConsumer.lean > "$release_out/SourceConsumer.log" 2>&1 || release_consumer_status=$?
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$release_out/consumer-end.utc"
printf '%s\n' "$release_consumer_status" > "$release_out/consumer-exit.txt"
test "$release_consumer_status" -eq 0
test "$(grep -c '^TRUSTED_CACHE_EXTERNAL_CONSUMER_PASSED ' "$release_out/SourceConsumer.log")" -eq 1
grep '^TRUSTED_CACHE_EXTERNAL_CONSUMER_PASSED ' "$release_out/SourceConsumer.log" > "$release_out/consumer-marker.txt"
printf '%s\n' "$release_consumer_marker" > "$release_out/consumer-expected-marker.txt"
cmp "$release_out/consumer-expected-marker.txt" "$release_out/consumer-marker.txt"
release_artifacts "$release_out" SourceConsumer > "$release_out/consumer-artifacts.json"
release_artifacts "$release_main" CriticalDepthMathlib > "$release_out/main-artifacts.after.json"
cmp "$release_out/main-artifacts.before.json" "$release_out/main-artifacts.after.json"
sha256sum -c "$release_main/inputs-before.local.sha256" > "$release_out/main-inputs.after.local.txt"
perl scripts/verify_public_dependencies.pl lake-cache "$release_root" \
  "$release_public" - "$release_prefix" "$release_out/public-artifacts.after.jsonl" \
  "$release_out/LEAN_PATH.after.local.txt" > "$release_out/dependency-check.after.json"
cmp "$release_main/LEAN_PATH.local.txt" "$release_out/LEAN_PATH.after.local.txt"
cmp "$release_out/public-artifacts.before.jsonl" "$release_out/public-artifacts.after.jsonl"
release_inputs > "$release_out/inputs.after.json"
cmp "$release_out/inputs.before.json" "$release_out/inputs.after.json"
release_packages > "$release_out/checkouts.after.json"
cmp "$release_out/checkouts.before.json" "$release_out/checkouts.after.json"
(cd mathlib-review && sha256sum -c PAYLOAD_SHA256.txt) > "$release_out/payload.after.txt"
cp "$release_main/CriticalDepthMathlib.log" "$release_out/CriticalDepthMathlib.log"
cp "$release_main/final-audit-marker.txt" "$release_out/main-marker.txt"
cp "$release_main/toolchain.txt" "$release_out/toolchain.txt"
cp "$release_main/compiler-start.utc" "$release_out/main-start.utc"
cp "$release_main/compiler-end.utc" "$release_out/main-end.utc"
sha256sum "$release_lean" | cut -d ' ' -f 1 > "$release_out/compiler.sha256"
date -u +%Y-%m-%dT%H:%M:%S.%NZ > "$release_out/end.utc"

# No absolute host paths or inherited historical approval claims enter this receipt.
perl - "$release_out" <<'PERL' > "$release_out/VERIFICATION.json"
use strict; use warnings; use JSON::PP; use Digest::SHA;
my $out=shift @ARGV;
sub text {open my $fh,'<:raw',"$out/$_[0]" or die "read receipt input\n"; local $/; my $s=<$fh>; $s=~s/\s+\z//; return $s;}
sub json {return decode_json(text($_[0]));}
sub evidence {
  my ($file)=@_; open my $fh,'<:raw',"$out/$file" or die "read evidence\n";
  my $h=Digest::SHA->new(256); $h->addfile($fh);
  return {file=>$file,bytes=>0+(-s "$out/$file"),sha256=>$h->hexdigest};
}
my $main=text('main-marker.txt');
$main=~/\ASTANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED / or die "main audit marker\n";
my %audit=($main=~/([a-z_]+)=([0-9]+)/g); $_=0+$_ for values %audit;
my $consumer=text('consumer-marker.txt');
$consumer eq 'TRUSTED_CACHE_EXTERNAL_CONSUMER_PASSED call_count=3 imported_main_count=2 exact_three_count=5'
  or die "consumer audit marker\n";
my $receipt={schema=>1,status=>'PASS',validation=>'MAIN_SOURCE_AND_FRESH_ARTIFACT_CONSUMER',
  dependency_policy=>'TRUSTED_PINNED_PUBLIC_CACHE',
  clean_environment_provenance=>'Recorded separately by the bootstrap runner; not established by this verifier alone.',
  source_inputs=>json('inputs.after.json'),checkouts=>json('checkouts.after.json'),
  toolchain=>{version=>text('toolchain.txt'),compiler_sha256=>text('compiler.sha256')},
  interval=>{start=>text('start.utc'),end=>text('end.utc')},
  main=>{exit_code=>0,start=>text('main-start.utc'),end=>text('main-end.utc'),
    audit_marker=>$main,audit=>\%audit,artifacts=>json('main-artifacts.after.json'),
    log=>evidence('CriticalDepthMathlib.log')},
  consumer=>{exit_code=>0,start=>text('consumer-start.utc'),end=>text('consumer-end.utc'),
    audit_marker=>$consumer,call_count=>3,imported_main_count=>2,exact_three_count=>5,
    artifacts=>json('consumer-artifacts.json'),log=>evidence('SourceConsumer.log')},
  bindings=>{inputs_unchanged=>JSON::PP::true,package_checkouts_unchanged=>JSON::PP::true,
    main_artifacts_unchanged_during_consumer=>JSON::PP::true,public_artifacts_unchanged=>JSON::PP::true},
  public_artifact_manifest=>evidence('public-artifacts.after.jsonl'),
  recursive_axiom_allowlist=>['propext','Classical.choice','Quot.sound'],
  semantic_scope=>'Formal main theorems and the recorded external calls; manuscript semantic approval is a separate bound record. CAD proof-route identity is not claimed.'};
print JSON::PP->new->canonical->pretty->encode($receipt);
PERL
printf 'PASS\n' > "$release_out/status.txt"
release_passed=1
printf 'RELEASE_SOURCE_AND_CONSUMER_PASSED\n'
printf 'RELEASE_VERIFICATION_RUN=%s\n' "$release_out"
