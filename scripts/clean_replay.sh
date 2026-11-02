#!/usr/bin/env bash
# Linux x86_64 replay with a fresh toolchain, public cache, and project build.
set -Eeuo pipefail
umask 022
export PYTHONDONTWRITEBYTECODE=1

usage() {
  printf 'Usage: bash %s FULL_GIT_COMMIT /absolute/new-workspace\n' "$0" >&2
  exit 2
}
[[ $# -eq 2 ]] || usage
[[ $1 =~ ^[0-9a-fA-F]{40}$ ]] || usage
replay_commit=${1,,}
[[ $2 == /* && $2 != *$'\n'* && $2 != *$'\r'* ]] || usage

# Deliberately exclude any inherited Elan/Lake installation from PATH.
export PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
for replay_command in bash curl git perl python3 tar gzip sha256sum realpath \
    uname date tee mkdir cp cmp mktemp grep sed cut; do
  command -v "$replay_command" >/dev/null || {
    printf 'Required command is unavailable: %s\n' "$replay_command" >&2
    exit 2
  }
done
[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] || {
  printf 'This bootstrap requires Linux x86_64.\n' >&2
  exit 2
}
replay_workspace=$(realpath -m -- "$2")
[[ ! -e $replay_workspace && ! -L $replay_workspace ]] || {
  printf 'Refusing an existing workspace: %s\n' "$replay_workspace" >&2
  exit 2
}
[[ -d $(dirname -- "$replay_workspace") ]] || {
  printf 'The workspace parent directory must already exist.\n' >&2
  exit 2
}
mkdir -- "$replay_workspace"
mkdir -- "$replay_workspace/bootstrap" "$replay_workspace/cache" \
  "$replay_workspace/config" "$replay_workspace/data" "$replay_workspace/tmp"
cp -- "$0" "$replay_workspace/bootstrap/clean_replay.sh"
exec > >(tee -a "$replay_workspace/bootstrap.log") 2>&1

replay_stage=initialization
replay_started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
replay_run=''
replay_url=https://github.com/Imine20/critical-depth-for-the-infinite-logical-set.git
replay_elan_url=https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz
replay_elan_sha=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63

replay_status() {
  python3 - "$replay_workspace" "$1" "$2" "$replay_stage" \
    "$replay_started" "$replay_commit" "$replay_run" <<'PY'
import datetime, json, pathlib, sys
root, status, exit_code, stage, started, commit, run = sys.argv[1:]
record = {
    "status": status, "exit_code": int(exit_code), "stage": stage,
    "started_utc": started,
    "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "requested_commit": commit, "verification_run": run or None,
    "dependency_mode": "fresh-public-cache",
    "scope": "fresh project and consumer compilation; Mathlib closure uses downloaded caches; locked Cli library is built from source",
}
pathlib.Path(root, "status.json").write_text(json.dumps(record, indent=2) + "\n")
PY
}
replay_finish() {
  replay_exit=$?
  trap - EXIT
  if [[ $replay_exit -eq 0 && $replay_stage == complete ]]; then
    replay_status PASSED 0
    printf 'CLEAN_REPLAY_PASSED commit=%s workspace=%s\n' "$replay_commit" "$replay_workspace"
  else
    [[ $replay_exit -ne 0 ]] || replay_exit=1
    replay_status FAILED "$replay_exit"
    printf 'Clean replay failed at stage %s; records retained in %s\n' \
      "$replay_stage" "$replay_workspace" >&2
  fi
  exit "$replay_exit"
}
trap replay_finish EXIT
replay_status RUNNING 0

# Keep HOME unchanged. Only task-specific directories and search paths change.
# Proxy and certificate settings may be inherited; their values are not logged.
while IFS= read -r replay_variable; do
  case "$replay_variable" in
    LEAN_*|LAKE_*|ELAN_*|MATHLIB_*|CRITICAL_DEPTH_*) unset "$replay_variable" ;;
  esac
done < <(compgen -e)
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY \
  GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_COMMON_DIR GIT_NAMESPACE \
  GIT_CONFIG GIT_CONFIG_COUNT GIT_CONFIG_PARAMETERS GIT_CEILING_DIRECTORIES
export ELAN_HOME="$replay_workspace/elan"
export MATHLIB_CACHE_DIR="$replay_workspace/cache/mathlib"
export XDG_CACHE_HOME="$replay_workspace/cache/xdg"
export XDG_CONFIG_HOME="$replay_workspace/config"
export XDG_DATA_HOME="$replay_workspace/data"
export CARGO_HOME="$replay_workspace/cache/cargo"
export npm_config_cache="$replay_workspace/cache/npm"
export NPM_CONFIG_CACHE="$npm_config_cache"
export TMPDIR="$replay_workspace/tmp"
export TMP="$TMPDIR" TEMP="$TMPDIR"
export GIT_CONFIG_GLOBAL="$replay_workspace/config/gitconfig"
export GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0
export GIT_ASKPASS=/bin/false SSH_ASKPASS=/bin/false
export LEAN_NUM_THREADS=1
: > "$GIT_CONFIG_GLOBAL"
mkdir -p -- "$MATHLIB_CACHE_DIR" "$XDG_CACHE_HOME"
python3 - "$replay_workspace" "$replay_commit" "$replay_url" \
  "$replay_elan_url" "$replay_elan_sha" <<'PY'
import json, os, pathlib, platform, subprocess, sys
root, commit, url, elan_url, elan_sha = sys.argv[1:]
record = {
    "commit": commit, "repository_url": url,
    "elan_version": "4.2.4", "elan_asset_url": elan_url,
    "elan_asset_sha256": elan_sha,
    "platform": platform.platform(), "python": platform.python_version(),
    "git": subprocess.check_output(["git", "--version"], text=True).strip(),
    "curl": subprocess.check_output(["curl", "--version"], text=True).splitlines()[0],
    "environment": {key: os.environ[key] for key in (
        "ELAN_HOME", "MATHLIB_CACHE_DIR", "XDG_CACHE_HOME", "XDG_CONFIG_HOME",
        "XDG_DATA_HOME", "CARGO_HOME", "npm_config_cache", "TMPDIR", "PATH",
        "GIT_CONFIG_GLOBAL")},
    "proxy_configured": any(os.environ.get(key) for key in (
        "http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY")),
    "home_changed": False,
    "isolation": "fresh task directories on the host OS; not a container",
}
pathlib.Path(root, "environment.json").write_text(json.dumps(record, indent=2) + "\n")
PY

replay_stage=elan-download
curl --disable --fail --location --retry 3 --proto '=https' --tlsv1.2 \
  "$replay_elan_url" -o "$replay_workspace/bootstrap/elan.tar.gz"
printf '%s  %s\n' "$replay_elan_sha" "$replay_workspace/bootstrap/elan.tar.gz" \
  | sha256sum -c -
tar -xzf "$replay_workspace/bootstrap/elan.tar.gz" -C "$replay_workspace/bootstrap"
replay_stage=elan-install
"$replay_workspace/bootstrap/elan-init" -y --no-modify-path --default-toolchain none
export PATH="$ELAN_HOME/bin:$PATH"
elan --version | tee "$replay_workspace/elan-version.txt"
grep -Eq '^elan 4\.2\.4([[:space:]]|$)' "$replay_workspace/elan-version.txt"

replay_stage=checkout
replay_repository="$replay_workspace/repository"
git -c core.autocrlf=false clone --no-checkout -- "$replay_url" "$replay_repository"
git -C "$replay_repository" config core.autocrlf false
git -C "$replay_repository" checkout --detach "$replay_commit"
[[ $(git -C "$replay_repository" rev-parse HEAD) == "$replay_commit" ]]
cd "$replay_repository"
cmp scripts/clean_replay.sh "$replay_workspace/bootstrap/clean_replay.sh"
[[ -z $(git status --porcelain --untracked-files=all) ]]
[[ ! -e .lake ]]
cp -- lean-toolchain lake-manifest.json "$replay_workspace/bootstrap/"
sha256sum lean-toolchain lake-manifest.json lakefile.toml scripts/clean_replay.sh \
  scripts/verify_release.sh > "$replay_workspace/bootstrap/checkout-inputs.sha256"
replay_toolchain=$(python3 - <<'PY'
import pathlib, re
toolchain = pathlib.Path("lean-toolchain").read_text().strip()
if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(?:-[A-Za-z0-9.-]+)?", toolchain):
    raise SystemExit("lean-toolchain must pin an official Lean release")
print(toolchain)
PY
)
replay_stage=toolchain-install
elan toolchain install "$replay_toolchain"
elan which lean | tee "$replay_workspace/lean-path.txt"
replay_lean=$(realpath -- "$(elan which lean)")
[[ $replay_lean == "$ELAN_HOME"/toolchains/*/bin/lean ]]
lean --version | tee "$replay_workspace/lean-version.txt"
lake --version | tee "$replay_workspace/lake-version.txt"

replay_check_inputs() {
  sha256sum -c "$replay_workspace/bootstrap/checkout-inputs.sha256"
  [[ $(git rev-parse HEAD) == "$replay_commit" ]]
  [[ -z $(git status --porcelain --untracked-files=all) ]]
  python3 - "$1" <<'PY'
import json, pathlib, re, subprocess, sys
root = pathlib.Path.cwd().resolve()
manifest = json.loads((root / "lake-manifest.json").read_text())
package_root = (root / manifest["packagesDir"]).resolve()
if package_root != root / ".lake" / "packages":
    raise SystemExit("Unexpected packagesDir")
packages = manifest["packages"]
if not packages:
    raise SystemExit("The dependency lock is empty")
records = []
for package in packages:
    name, rev = package["name"], package["rev"]
    if (package["type"] != "git" or not re.fullmatch(r"[A-Za-z0-9_-]+", name)
            or not re.fullmatch(r"[0-9a-f]{40}", rev)):
        raise SystemExit("Dependency is not pinned to an immutable Git commit")
    directory = package_root / name
    if directory.is_symlink() or directory.resolve().parent != package_root:
        raise SystemExit("Unexpected dependency directory")
    head = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output([
        "git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"
    ], text=True)
    if head != rev or dirty:
        raise SystemExit(f"Dependency checkout does not match its lock: {name}")
    records.append({"name": name, "revision": head, "tracked_files_clean": True})
pathlib.Path(sys.argv[1]).write_text(json.dumps(records, indent=2) + "\n")
PY
}

replay_stage=public-cache
# Bootstrap only the locked dependencies; never replace this with `lake update`.
lake exe cache get 2>&1 | tee "$replay_workspace/public-cache.log"
# Mathlib's import closure does not populate the locked Cli library output.
replay_stage=locked-cli-library
lake --no-cache build '@Cli/Cli:leanArts' 2>&1 | tee "$replay_workspace/locked-cli-library.log"
replay_check_inputs "$replay_workspace/dependencies.before.json"
replay_stage=source-and-consumer-verification
sh scripts/verify_release.sh 2>&1 | tee "$replay_workspace/verification.log"
[[ $(grep -c '^RELEASE_SOURCE_AND_CONSUMER_PASSED$' "$replay_workspace/verification.log") -eq 1 ]]
[[ $(grep -c '^RELEASE_VERIFICATION_RUN=' "$replay_workspace/verification.log") -eq 1 ]]
replay_run=$(sed -n 's/^RELEASE_VERIFICATION_RUN=//p' "$replay_workspace/verification.log")
[[ $replay_run == "$replay_repository"/.verification/release/run.* ]]
[[ $(realpath -- "$replay_run") == "$replay_run" ]]
[[ -s $replay_run/VERIFICATION.json ]]
printf '%s\n' "$replay_run" > "$replay_workspace/verification-run.txt"
replay_stage=final-input-check
replay_check_inputs "$replay_workspace/dependencies.after.json"
cmp "$replay_workspace/dependencies.before.json" "$replay_workspace/dependencies.after.json"
replay_stage=complete
