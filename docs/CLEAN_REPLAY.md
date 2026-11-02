# Fresh Linux replay

Run the wrapper from a checkout of the commit to be verified:

```sh
bash scripts/clean_replay.sh FULL_40_CHARACTER_COMMIT /absolute/new-workspace
```

Replace both arguments. The workspace must not exist, and its parent directory
must already exist. For the Windows host's WSL environment, use a path such as
`/mnt/e/Codex/work/20261103v2_release/clean-replay`. The wrapper refuses existing
directories, including empty ones, and never deletes an earlier run. A failed
run remains available for diagnosis; use a different workspace for a new run.

The wrapper supports Linux x86_64, including WSL Ubuntu 24.04. It requires Bash,
Git, curl, Perl, Python 3, tar, gzip, standard coreutils, grep, and sed on the
system PATH. Network access to GitHub release assets, the public repository,
and Mathlib's public cache is required. The host OS and these utilities are
prerequisites; this is not a container or an OS reproducibility claim.

## What the command does

1. Creates a new workspace and isolates `ELAN_HOME`, `MATHLIB_CACHE_DIR`,
   `XDG_CACHE_HOME`, configuration/data directories, and temporary files there.
   It removes inherited Lean/Lake/project overrides and uses a system PATH
   followed by the new Elan binaries. It leaves `HOME` unchanged and does not
   edit shell profiles. Proxy and certificate environment settings may be
   inherited; their values are not written to metadata.
2. Downloads the official Elan v4.2.4 Linux x86_64 asset from
   `https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz`
   and requires SHA-256
   `42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`.
   Installation uses `--no-modify-path --default-toolchain none`.
3. Clones the public HTTPS repository into the new workspace, checks out the
   full requested commit, and verifies that its wrapper matches the script
   being run. It installs the release named by that checkout's `lean-toolchain`
   into the isolated Elan directory.
4. Runs `lake exe cache get` using the committed dependency lock and an empty
   public-cache directory. It then runs
   `lake --no-cache build '@Cli/Cli:leanArts'` to build the locked Cli library
   from source, with Lake's build-cache downloads disabled. Mathlib's cached
   import closure does not populate that library's output directory. All nine
   pinned public output roots remain required. It never runs `lake update`
   and never imports a pre-existing project Lean search path or Mathlib cache.
5. Invokes `sh scripts/verify_release.sh`, which compiles the project source and
   its consumer in fresh verification directories. Before and after this
   verification, the wrapper checks the repository commit, recorded input
   hashes, clean repository status, every dependency's locked Git revision,
   and clean tracked dependency files.

Here, **fresh replay** means a newly installed Lean runtime, newly downloaded
public dependency caches, a newly source-built locked Cli library, and newly
compiled project/consumer artifacts. It does **not** mean that all public
dependencies or the Lean compiler were built from source. Consult the separate
dependency-source replay documentation for that stronger and more expensive
scope. This command verifies the formal
artifacts covered by the release verifier; it does not establish author
semantic approval or a line-by-line manuscript-to-Lean correspondence.

## Records and completion

All records stay in the new workspace:

- `bootstrap.log` records the overall run; `public-cache.log`,
  `locked-cli-library.log`, and `verification.log` record the cache download,
  locked Cli source build, and project/consumer verification stages.
- `environment.json`, `elan-version.txt`, `lean-version.txt`, and
  `lake-version.txt` identify the bootstrap and runtime environment.
- `bootstrap/` contains the running wrapper, downloaded installer, committed
  toolchain/lock snapshots, and input hashes.
- `dependencies.before.json` and `dependencies.after.json` record dependency
  revisions and tracked-file cleanliness.
- `verification-run.txt` locates the verifier's `VERIFICATION.json`, compiler
  logs, consumer evidence, and hash records under the fresh checkout.
- `status.json` records `RUNNING`, `FAILED`, or `PASSED`, the requested commit,
  the last stage, and the exit code. An interrupted or forcibly killed process
  may retain `RUNNING`; this is not completion evidence.

Successful completion requires exit code zero, `status.json` with `PASSED`,
and the terminal marker `CLEAN_REPLAY_PASSED`. A downloaded toolchain, fetched
cache, or started verifier alone does not establish completion. Local metadata
contains absolute paths; review it before copying it into a public release.
