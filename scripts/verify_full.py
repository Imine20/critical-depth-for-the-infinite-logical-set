#!/usr/bin/env python3
"""Replay every project module with the pinned, already installed dependencies.

Run from the repository root with:
    lake env python -B scripts/verify_full.py /absolute/path/to/new-output

This portable entry point preserves verify-v3.sh's module order, Lean options,
audit markers, and forbidden-log checks. It never installs dependencies. The
output directory must be new; existing project build objects are not imported.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time


EXPECTED_MODULES = 346
EXPECTED_AUDITS = 19
LEAN_PIN = "leanprover/lean4:v4.35.0"
LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
LEAN_OPTIONS = ["-j1", "-M6144", "-DmaxHeartbeats=3000000", "-R", "."]
FORBIDDEN_LOG = r"uses .sorry.|sorryAx|depends on axioms:.*native_decide"
ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / "mathlib-review"


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def digest(path: Path) -> dict[str, object]:
    require(path.is_file(), f"Missing input: {path}")
    h = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
            size += len(chunk)
    return {"bytes": size, "sha256": h.hexdigest()}


def write_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def parse_reference(text: str) -> tuple[list[str], list[tuple[str, str]]]:
    lists = re.findall(r"^modules='([^']*)'\s*$", text, re.MULTILINE)
    require(len(lists) == 1, "Expected one literal module list in verify-v3.sh")
    modules = lists[0].split()
    require(len(modules) == EXPECTED_MODULES, "Reference module count changed; review the runner")
    require(len(set(modules)) == len(modules), "Duplicate module in reference order")
    require(all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", m) for m in modules), "Invalid module name")
    markers = re.findall(r'^grep -F ([A-Z0-9_]+) "\$out/([A-Za-z0-9_]+)\.log"\s*$', text, re.MULTILINE)
    require(len(markers) == EXPECTED_AUDITS, "Reference audit count changed; review the runner")
    require(len(set(markers)) == len(markers), "Duplicate audit expectation")
    require(all(module in modules for _, module in markers), "Audit refers to an unlisted module")
    command = 'lean -j1 -M6144 -DmaxHeartbeats=3000000 -R . -o "$out/$module.olean" "$module.lean"'
    require(command in text, "Reference Lean command changed; review the runner")
    pattern = re.findall(r'^if grep -E \'([^\']+)\' "\$out"/\*\.log; then\s*$', text, re.MULTILINE)
    require(pattern == [FORBIDDEN_LOG], "Reference forbidden-log policy changed; review the runner")
    return modules, markers


def check_inventory(modules: list[str]) -> None:
    actual = {p.stem for p in PROOF.glob("*.lean")}
    expected = set(modules)
    require(actual == expected,
            f"Module inventory mismatch: unlisted={sorted(actual - expected)}, missing={sorted(expected - actual)}")
    require(not list(PROOF.glob("**/*.olean*")), "Project artifacts found in the source directory")


def run_text(args: list[str], cwd: Path, env: dict[str, str] | None = None) -> str:
    result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False)
    require(result.returncode == 0,
            f"Command failed ({result.returncode}): {args[0]} {' '.join(args[1:])}\n"
            + result.stderr.decode("utf-8", errors="replace"))
    return result.stdout.decode("utf-8", errors="strict").strip()


def git(args: list[str], cwd: Path = ROOT) -> str:
    return run_text(["git", "--no-optional-locks", "-c", f"safe.directory={cwd}", "-C", str(cwd), *args], ROOT)


def proof_inputs(modules: list[str]) -> dict[str, dict[str, object]]:
    paths = [f"mathlib-review/{m}.lean" for m in modules]
    paths += ["lean-toolchain", "lakefile.toml", "lake-manifest.json",
              "mathlib-review/lean-toolchain", "mathlib-review/lakefile.toml",
              "mathlib-review/lake-manifest.json", "mathlib-review/verify-v3.sh",
              "scripts/verify_full.py"]
    return {relative: digest(ROOT / relative) for relative in sorted(paths)}


def proof_commit_binding(modules: list[str]) -> dict[str, object]:
    head = git(["rev-parse", "HEAD"])
    require(re.fullmatch(r"[0-9a-f]{40}", head) is not None, "Expected a Git SHA-1 checkout")
    committed = {}
    for line in git(["ls-tree", "-r", "HEAD", "--", "mathlib-review"]).splitlines():
        metadata, path = line.split("\t", 1)
        committed[path] = metadata.split()[2]
    changed = []
    for module in modules:
        relative = f"mathlib-review/{module}.lean"
        data = (ROOT / relative).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
        if committed.get(relative) != blob:
            changed.append(relative)
    require(not changed, "Proof source differs from checkout HEAD: " + ", ".join(changed))
    return {"checkout_commit": head, "all_346_proof_files_match_commit_bytes": True,
            "working_tree_requirement": "Proof files match HEAD; documentation and runner edits are permitted."}


def dependency_state(lock: dict[str, object]) -> tuple[list[dict[str, object]], list[Path]]:
    packages = lock.get("packages")
    require(isinstance(packages, list) and packages, "Missing locked dependencies")
    packages_dir = (ROOT / str(lock.get("packagesDir", ".lake/packages"))).resolve()
    require(packages_dir.is_relative_to(ROOT), "Dependency directory escapes the checkout")
    rows, roots, names = [], [], set()
    for package in packages:
        require(package.get("type") == "git", "Only locked Git dependencies are supported")
        name, revision = package["name"], package["rev"]
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None,
                "Invalid dependency name")
        require(name not in names, "Duplicate dependency name")
        names.add(name)
        require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, "Dependency is not pinned to a commit")
        require(package.get("subDir") in (None, ""), "Review non-root Git dependency layout before use")
        directory = (packages_dir / name).resolve()
        require(directory.is_dir(), f"Missing installed dependency: {name}")
        actual = git(["rev-parse", "HEAD"], directory)
        require(actual == revision, f"Wrong dependency revision: {name}")
        require(not git(["status", "--porcelain=v1", "--untracked-files=no"], directory),
                f"Tracked dependency files are dirty: {name}")
        rows.append({"name": name, "revision": actual, "tracked_tree_clean": True})
        roots.append(directory)
    return rows, roots


def dependency_inputs(rows: list[dict[str, object]], roots: list[Path]) -> dict[str, dict[str, object]]:
    files = {}
    for row, directory in zip(rows, roots):
        name = str(row["name"])
        tracked = git(["ls-files", "-z"], directory).split("\0")
        for relative in tracked:
            path = Path(relative)
            if relative and (path.suffix == ".lean" or path.name in
                             {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}):
                files[f"dependencies/{name}/source/{path.as_posix()}"] = digest(directory / path)
        library = directory / ".lake/build/lib/lean"
        require(library.is_dir(), f"Missing dependency build artifacts: {name}")
        for path in sorted(library.rglob("*")):
            if path.is_file():
                files[f"dependencies/{name}/build/{path.relative_to(library).as_posix()}"] = digest(path)
        for path in sorted((directory / ".lake/build/lib").glob("*")):
            if path.is_file() and path.suffix in {".dll", ".so", ".dylib"}:
                files[f"dependencies/{name}/native/{path.name}"] = digest(path)
    return files


def lean_environment(output: Path, dependency_roots: list[Path], prefix: Path,
                     modules: list[str]) -> tuple[dict[str, str], list[str]]:
    inherited = os.environ.get("LEAN_PATH", "")
    require(bool(inherited), "LEAN_PATH is absent; run this script through lake env")
    approved = {(p / ".lake/build/lib/lean").resolve(): f"dependencies/{p.name}/build"
                for p in dependency_roots}
    approved[(prefix / "lib/lean").resolve()] = "toolchain/lib/lean"
    project_build = (ROOT / ".lake/build/lib/lean").resolve()
    paths, labels = [], []
    for item in inherited.split(os.pathsep):
        require(bool(item), "Empty LEAN_PATH component would admit the current directory")
        path = Path(item).resolve()
        if path == project_build:
            continue
        require(path in approved, f"Unapproved LEAN_PATH root: {path}")
        require(path.is_dir(), f"Missing LEAN_PATH directory: {approved[path]}")
        for module in modules:
            require(not (path / f"{module}.olean").exists(),
                    f"A dependency/toolchain root shadows project module {module}")
        if path not in paths:
            paths.append(path)
            labels.append(approved[path])
    required = {(p / ".lake/build/lib/lean").resolve() for p in dependency_roots}
    require(required.issubset(paths), "lake env does not expose all locked dependency build roots")
    environment = dict(os.environ)
    environment["LEAN_PATH"] = os.pathsep.join([str(output), *(str(p) for p in paths)])
    environment["LEAN_NUM_THREADS"] = "1"
    environment.pop("LEAN_SRC_PATH", None)
    environment.pop("LEAN_OPTS", None)
    return environment, ["fresh-output", *labels]


def main_replay(output: Path) -> int:
    require(output.is_absolute(), "Expected an absolute output directory")
    output = output.resolve()
    require(not output.exists(), "Output directory already exists; choose a new directory")
    require(output != ROOT and not output.is_relative_to(PROOF)
            and not output.is_relative_to(ROOT / "scripts")
            and not output.is_relative_to(ROOT / ".lake"), "Unsafe output directory")
    output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    receipt: dict[str, object] = {
        "schema": "critical-depth.full-replay.v1", "status": "RUNNING", "started_utc": utc_now(),
        "platform": {"system": platform.system(), "machine": platform.machine(),
                     "release": platform.release(), "python": platform.python_version()},
        "execution": "Fresh source compilation of all project modules against pinned dependency artifacts",
        "trust_boundary": "Installed Lean runtime/core library and pinned public dependency artifacts; not a dependency source rebuild",
        "module_count_expected": EXPECTED_MODULES, "audit_count_expected": EXPECTED_AUDITS,
        "module_results": [], "audit_results": [],
        "lean_options": LEAN_OPTIONS, "project_artifact_reuse": False,
        "publication_document_binding": "Manuscript and semantic documents are bound separately in the publication record.",
    }
    aliases = {str(ROOT): "<repository>", str(output): "<fresh-output>"}

    def checkpoint() -> None:
        write_json(output / "REPLAY.json", receipt)

    def portable(message: str) -> str:
        for actual, label in sorted(aliases.items(), key=lambda item: -len(item[0])):
            flags = re.IGNORECASE if os.name == "nt" else 0
            for spelling in {actual, actual.replace("\\", "/")}:
                message = re.sub(re.escape(spelling), lambda _: label, message, flags=flags)
        return message

    checkpoint()
    try:
        modules, markers = parse_reference((PROOF / "verify-v3.sh").read_text(encoding="utf-8"))
        check_inventory(modules)
        for path in [ROOT / "lean-toolchain", PROOF / "lean-toolchain"]:
            require(path.read_text(encoding="utf-8").strip() == LEAN_PIN, "Unexpected toolchain pin")
        require((ROOT / "lake-manifest.json").read_bytes() == (PROOF / "lake-manifest.json").read_bytes(),
                "Root and proof dependency locks differ")
        receipt["source_binding"] = proof_commit_binding(modules)
        before = proof_inputs(modules)
        write_json(output / "INPUTS.json", before)
        receipt["proof_input_manifest"] = {"path": "INPUTS.json", **digest(output / "INPUTS.json")}
        lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
        rows, dependency_roots = dependency_state(lock)
        for row, path in zip(rows, dependency_roots):
            aliases[str(path)] = f"<dependency:{row['name']}>"
        receipt["dependencies"] = rows
        compiler = shutil.which("lean")
        lake = shutil.which("lake")
        require(compiler is not None and lake is not None, "lean and lake must be installed on PATH")
        compiler_version = run_text([compiler, "--version"], ROOT)
        require("version 4.35.0," in compiler_version and LEAN_COMMIT in compiler_version,
                "Installed compiler does not match the pinned Lean version and commit")
        lake_version = run_text([lake, "--version"], ROOT)
        prefix = Path(run_text([compiler, "--print-prefix"], ROOT)).resolve()
        aliases[str(prefix)] = "<toolchain>"
        # Hash and invoke the actual toolchain executables, including when PATH
        # originally selected an elan launcher.
        executable_suffix = ".exe" if os.name == "nt" else ""
        compiler = str(prefix / "bin" / ("lean" + executable_suffix))
        lake = str(prefix / "bin" / ("lake" + executable_suffix))
        require(run_text([compiler, "--version"], ROOT) == compiler_version,
                "Toolchain prefix selects a different Lean compiler")
        require(run_text([lake, "--version"], ROOT) == lake_version,
                "Toolchain prefix selects a different Lake executable")
        receipt["toolchain"] = {"pin": LEAN_PIN, "compiler_version": compiler_version,
                                "lake_version": lake_version,
                                "lean_executable": digest(Path(compiler)), "lake_executable": digest(Path(lake))}
        (output / "toolchain.txt").write_text(compiler_version + "\n", encoding="utf-8")
        (output / "lake-version.txt").write_text(lake_version + "\n", encoding="utf-8")
        environment, search_labels = lean_environment(output, dependency_roots, prefix, modules)
        receipt["lean_search_path"] = search_labels
        print("Hashing locked dependency sources and build artifacts", flush=True)
        dep_before = dependency_inputs(rows, dependency_roots)
        write_json(output / "DEPENDENCY_INPUTS.json", dep_before)
        receipt["dependency_input_manifest"] = {"path": "DEPENDENCY_INPUTS.json",
                                                "file_count": len(dep_before),
                                                **digest(output / "DEPENDENCY_INPUTS.json")}
        checkpoint()
        for index, module in enumerate(modules, 1):
            print(f"[{index}/{len(modules)}] Checking {module}", flush=True)
            begin = time.monotonic()
            log_path = output / f"{module}.log"
            command = [compiler, *LEAN_OPTIONS, "-o", str(output / f"{module}.olean"), f"{module}.lean"]
            with log_path.open("wb") as log:
                result = subprocess.run(command, cwd=PROOF, env=environment, stdout=log,
                                        stderr=subprocess.STDOUT, check=False)
            entry = {"module": module, "exit_code": result.returncode,
                     "elapsed_seconds": round(time.monotonic() - begin, 6),
                     "log": {"path": log_path.name, **digest(log_path)}}
            receipt["module_results"].append(entry)
            checkpoint()
            require(result.returncode == 0, f"Lean compilation failed for {module}; see {module}.log")
            require((output / f"{module}.olean").is_file(), f"Compiler produced no artifact for {module}")
        for marker, module in markers:
            text = (output / f"{module}.log").read_text(encoding="utf-8", errors="replace")
            passed = marker in text
            receipt["audit_results"].append({"module": module, "marker": marker, "passed": passed})
            require(passed, f"Missing recursive audit marker: {marker}")
        for module in modules:
            text = (output / f"{module}.log").read_text(encoding="utf-8", errors="replace")
            require(re.search(FORBIDDEN_LOG, text) is None, f"Forbidden proof dependency reported in {module}.log")
        receipt["forbidden_log_pattern"] = FORBIDDEN_LOG
        receipt["forbidden_log_matches"] = []
        print("Rechecking source, dependencies, and input artifacts", flush=True)
        check_inventory(modules)
        require(proof_inputs(modules) == before, "Proof or verification inputs changed during replay")
        require(proof_commit_binding(modules) == receipt["source_binding"], "Checkout revision changed during replay")
        after_rows, after_roots = dependency_state(lock)
        require(after_rows == rows and after_roots == dependency_roots, "Dependencies changed during replay")
        require(dependency_inputs(after_rows, after_roots) == dep_before,
                "Dependency source or build artifacts changed during replay")
        require(run_text([compiler, "--version"], ROOT) == compiler_version, "Compiler version changed during replay")
        require(digest(Path(compiler)) == receipt["toolchain"]["lean_executable"], "Compiler executable changed")
        require(digest(Path(lake)) == receipt["toolchain"]["lake_executable"], "Lake executable changed")
        receipt["inputs_unchanged_after_replay"] = True
        artifacts = {path.relative_to(output).as_posix(): digest(path)
                     for path in sorted(output.rglob("*"))
                     if path.is_file() and path.name not in {"REPLAY.json", "REPLAY.json.tmp"}}
        receipt["output_files"] = artifacts
        receipt["status"] = "PASSED"
        receipt["exit_code"] = 0
    except (Exception, KeyboardInterrupt) as error:
        receipt["status"] = "FAILED"
        receipt["exit_code"] = 130 if isinstance(error, KeyboardInterrupt) else 1
        receipt["error"] = portable(f"{type(error).__name__}: {error}")
        print(receipt["error"], file=sys.stderr, flush=True)
    finally:
        if "output_files" not in receipt:
            receipt["output_files"] = {
                path.relative_to(output).as_posix(): digest(path)
                for path in sorted(output.rglob("*"))
                if path.is_file() and path.name not in {"REPLAY.json", "REPLAY.json.tmp"}}
        receipt["finished_utc"] = utc_now()
        receipt["elapsed_seconds"] = round(time.monotonic() - started, 6)
        checkpoint()
    if receipt["status"] == "PASSED":
        print(f"FULL_REPLAY_PASSED modules={len(modules)} audits={len(markers)}", flush=True)
    return int(receipt["exit_code"])


def self_test() -> None:
    """Exercise the coverage and policy guards without Lean or generated files."""
    text = (PROOF / "verify-v3.sh").read_text(encoding="utf-8")
    modules, markers = parse_reference(text)
    check_inventory(modules)
    require(modules[0] == "CriticalDepthMathlib" and modules[-1] == "UpdateBranchAudit", "Unexpected endpoints")
    require(markers[-1] == ("UPDATE_BRANCH_AUDIT_PASSED", "UpdateBranchAudit"), "Unexpected last audit")
    invalid = [text.replace("CriticalDepthMathlib SourceConsumer", "SourceConsumer SourceConsumer", 1),
               text.replace(" SourceConsumer ", " ", 1),
               text.replace("grep -F UPDATE_BRANCH_AUDIT_PASSED", "# removed audit", 1),
               text.replace("-M6144", "-M8192", 1),
               text.replace("sorryAx", "admittedAx")]
    for fixture in invalid:
        try:
            parse_reference(fixture)
        except VerificationError:
            pass
        else:
            raise VerificationError("Parser accepted a changed coverage/policy fixture")
    for line in ["warning: declaration uses 'sorry'", "depends on axioms: [sorryAx]",
                 "depends on axioms: [native_decide]"]:
        require(re.search(FORBIDDEN_LOG, line) is not None, "Forbidden-log fixture escaped")
    require(re.search(FORBIDDEN_LOG, "depends on axioms: [propext, Classical.choice, Quot.sound]") is None,
            "Standard axioms were rejected")
    # Mock directory existence so these search-path controls do not write even
    # temporary files or require an installed dependency cache.
    from unittest.mock import patch
    dependency = ROOT / ".lake/packages/test-dependency"
    library = dependency / ".lake/build/lib/lean"
    prefix = ROOT.parent / "test-toolchain"
    core = prefix / "lib/lean"
    output = ROOT.parent / "test-output"
    project_build = ROOT / ".lake/build/lib/lean"
    original = os.pathsep.join(map(str, [library, project_build, core]))
    with patch.object(Path, "is_dir", return_value=True), patch.object(Path, "exists", return_value=False):
        with patch.dict(os.environ, {"LEAN_PATH": original}):
            environment, labels = lean_environment(output, [dependency], prefix, modules)
            require(environment["LEAN_PATH"].split(os.pathsep) == list(map(str, [output, library, core])),
                    "Fresh output or dependency search order was not preserved")
            require(labels == ["fresh-output", "dependencies/test-dependency/build", "toolchain/lib/lean"],
                    "Search-path receipt is not portable")
        for inherited in [original + os.pathsep, str(core), str(ROOT / "ambient-artifacts")]:
            with patch.dict(os.environ, {"LEAN_PATH": inherited}):
                try:
                    lean_environment(output, [dependency], prefix, modules)
                except VerificationError:
                    pass
                else:
                    raise VerificationError("Unapproved or incomplete search path was accepted")
    with patch.object(Path, "is_dir", return_value=True), patch.object(Path, "exists", return_value=True), \
            patch.dict(os.environ, {"LEAN_PATH": original}):
        try:
            lean_environment(output, [dependency], prefix, modules)
        except VerificationError:
            pass
        else:
            raise VerificationError("A shadow project artifact was accepted")
    print(f"SELF_TEST_PASSED modules={len(modules)} audits={len(markers)} "
          f"negative_fixtures={len(invalid)} search_path_controls=5")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", nargs="?", type=Path)
    parser.add_argument("--self-test", action="store_true", help="Check the runner guards without Lean or writes")
    options = parser.parse_args()
    try:
        if options.self_test:
            require(options.output is None, "--self-test does not take an output directory")
            self_test()
            sys.exit(0)
        require(options.output is not None, "Provide an absolute path to a new output directory")
        sys.exit(main_replay(options.output))
    except VerificationError as error:
        print(str(error), file=sys.stderr)
        sys.exit(2)
