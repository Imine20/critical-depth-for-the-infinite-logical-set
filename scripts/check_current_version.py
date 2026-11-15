#!/usr/bin/env python3
"""Check current publication bytes and the packaged full-replay evidence.

Run `python -B scripts/check_current_version.py` from any directory, or provide
`--root /path/to/checkout`. This reads files and streams the evidence archive;
it does not extract files, invoke Lean, or change the checkout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile


MODULE_COUNT = 346
AUDIT_COUNT = 19
FORBIDDEN_LOG = r"uses .sorry.|sorryAx|depends on axioms:.*native_decide"
CONFIG_INPUTS = {
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "mathlib-review/lean-toolchain", "mathlib-review/lakefile.toml",
    "mathlib-review/lake-manifest.json", "mathlib-review/verify-v3.sh",
    "scripts/verify_full.py",
}
PUBLICATION_REQUIRED = {
    "manuscript/Update_branch.tex", "docs/math/CURRENT_MATHEMATICAL_STATEMENTS.md",
    "docs/CURRENT_THREE_LAYER_CORRESPONDENCE.md", "scripts/check_current_version.py",
}


class CheckError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def no_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json(data: bytes, label: str) -> dict[str, object]:
    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=no_duplicate_keys)
    except (UnicodeError, ValueError) as error:
        raise CheckError(f"Invalid JSON in {label}: {error}") from error
    require(isinstance(value, dict), f"Expected a JSON object: {label}")
    return value


def relative_name(value: object) -> str:
    require(isinstance(value, str) and bool(value), "Expected a nonempty relative path")
    require("\\" not in value and ":" not in value and "\0" not in value,
            f"Unsafe relative path: {value!r}")
    path = PurePosixPath(value)
    require(not path.is_absolute() and path.as_posix() == value
            and all(part not in {"", ".", ".."} for part in value.split("/")),
            f"Unsafe or noncanonical relative path: {value!r}")
    return value


def inside(root: Path, relative: object) -> Path:
    name = relative_name(relative)
    path = (root / name).resolve(strict=True)
    require(path.is_relative_to(root), f"Path escapes its declared directory: {name}")
    require(path.is_file(), f"Expected a regular file: {name}")
    return path


def descriptor(value: object, label: str) -> dict[str, object]:
    require(isinstance(value, dict), f"Missing byte descriptor: {label}")
    size, sha256 = value.get("bytes"), value.get("sha256")
    require(type(size) is int and size >= 0, f"Invalid byte length: {label}")
    require(isinstance(sha256, str) and re.fullmatch(r"[0-9a-f]{64}", sha256) is not None,
            f"Invalid SHA-256: {label}")
    return {"bytes": size, "sha256": sha256}


def path_map(value: object, label: str) -> dict[str, dict[str, object]]:
    require(isinstance(value, dict) and bool(value), f"Missing file map: {label}")
    result, folded = {}, set()
    for name, item in value.items():
        name = relative_name(name)
        require(name.casefold() not in folded, f"Case-colliding path in {label}: {name}")
        folded.add(name.casefold())
        result[name] = descriptor(item, f"{label}/{name}")
    return result


def file_digest(path: Path) -> dict[str, object]:
    h, size = hashlib.sha256(), 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(chunk)
            h.update(chunk)
    return {"bytes": size, "sha256": h.hexdigest()}


def compare_disk(root: Path, files: dict[str, dict[str, object]], label: str) -> None:
    for name, expected in files.items():
        require(file_digest(inside(root, name)) == expected, f"Byte mismatch: {label}/{name}")


def reference_policy(root: Path) -> tuple[list[str], list[tuple[str, str]]]:
    text = inside(root, "mathlib-review/verify-v3.sh").read_text(encoding="utf-8")
    lists = re.findall(r"^modules='([^']*)'\s*$", text, re.MULTILINE)
    require(len(lists) == 1, "Expected one reference module order")
    modules = lists[0].split()
    require(len(modules) == MODULE_COUNT and len(set(modules)) == MODULE_COUNT,
            "Reference module coverage is not 346 distinct modules")
    require(all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", m) for m in modules), "Invalid module name")
    current = {path.stem for path in (root / "mathlib-review").glob("*.lean")}
    require(set(modules) == current, "Reference order does not cover every current Lean module")
    markers = re.findall(r'^grep -F ([A-Z0-9_]+) "\$out/([A-Za-z0-9_]+)\.log"\s*$', text, re.MULTILINE)
    require(len(markers) == AUDIT_COUNT and len(set(markers)) == AUDIT_COUNT,
            "Reference audit coverage is not 19 distinct checks")
    require(all(module in current for _, module in markers), "Audit module is outside the source inventory")
    pattern = re.findall(r'^if grep -E \'([^\']+)\' "\$out"/\*\.log; then\s*$', text, re.MULTILINE)
    require(pattern == [FORBIDDEN_LOG], "Reference forbidden-log policy changed")
    return modules, markers


def check_receipt(receipt: dict[str, object], modules: list[str],
                  markers: list[tuple[str, str]]) -> dict[str, dict[str, object]]:
    require(receipt.get("schema") == "critical-depth.full-replay.v1", "Unexpected replay schema")
    require(receipt.get("status") == "PASSED" and type(receipt.get("exit_code")) is int
            and receipt["exit_code"] == 0, "Replay did not pass")
    require(receipt.get("module_count_expected") == MODULE_COUNT
            and receipt.get("audit_count_expected") == AUDIT_COUNT, "Replay coverage count mismatch")
    results = receipt.get("module_results")
    require(isinstance(results, list) and len(results) == MODULE_COUNT, "Incomplete module results")
    require([r.get("module") for r in results] == modules, "Replay order has missing, duplicate, or reordered modules")
    require(all(type(r.get("exit_code")) is int and r["exit_code"] == 0 for r in results),
            "A module compilation did not exit successfully")
    audits = receipt.get("audit_results")
    require(isinstance(audits, list) and len(audits) == AUDIT_COUNT, "Incomplete audit results")
    actual = [(r.get("marker"), r.get("module")) for r in audits]
    require(actual == markers and all(r.get("passed") is True for r in audits),
            "Audit expectations or outcomes differ from the full reference policy")
    require(receipt.get("forbidden_log_pattern") == FORBIDDEN_LOG
            and receipt.get("forbidden_log_matches") == [], "Forbidden-dependency check did not pass")
    require(receipt.get("inputs_unchanged_after_replay") is True, "Replay lacks its closing input check")
    require(receipt.get("project_artifact_reuse") is False, "Replay reused project artifacts")
    binding = receipt.get("source_binding", {})
    require(binding.get("all_346_proof_files_match_commit_bytes") is True
            and re.fullmatch(r"[0-9a-f]{40}", binding.get("checkout_commit", "")) is not None,
            "Replay lacks the proof-source commit binding")
    output_files = path_map(receipt.get("output_files"), "receipt.output_files")
    for result in results:
        name = f"{result['module']}.log"
        log = result.get("log", {})
        require(log.get("path") == name and name in output_files
                and descriptor(log, name) == output_files[name], f"Module log binding mismatch: {name}")
        require(f"{result['module']}.olean" in output_files, f"Missing compiled-artifact digest: {result['module']}")
    return output_files


def check_archive(root: Path, contents_path: Path, contents: dict[str, object],
                  receipt: dict[str, object], receipt_path: Path, proof_inputs_path: Path,
                  modules: list[str], markers: list[tuple[str, str]],
                  output_files: dict[str, dict[str, object]]) -> int:
    archive = contents.get("archive", {})
    archive_path = inside(contents_path.parent, archive.get("path"))
    require(archive_path.is_relative_to(root), "Evidence archive escapes repository")
    require(file_digest(archive_path) == descriptor(archive, "archive"), "Evidence archive digest mismatch")
    expected = path_map(contents.get("members"), "evidence.members")
    prohibited = {"CURRENT_VERSION.json", contents_path.name, archive_path.name,
                  contents_path.relative_to(root).as_posix(), archive_path.relative_to(root).as_posix()}
    require(not ({name.casefold() for name in expected} & {name.casefold() for name in prohibited}),
            "Evidence archive would create a self-referential binding")
    mandatory = {f"{m}.log" for m in modules} | {
        "REPLAY.json", "INPUTS.json", "DEPENDENCY_INPUTS.json", "toolchain.txt", "lake-version.txt"}
    require(mandatory.issubset(expected), "Archive omits required compiler logs or replay metadata")
    require(expected["REPLAY.json"] == file_digest(receipt_path), "Archived REPLAY descriptor differs from disk")
    require(expected["INPUTS.json"] == file_digest(proof_inputs_path), "Archived INPUTS descriptor differs from disk")
    require(receipt.get("proof_input_manifest", {}).get("path") == "INPUTS.json"
            and descriptor(receipt.get("proof_input_manifest"), "proof_input_manifest") == expected["INPUTS.json"],
            "Replay proof-input manifest binding mismatch")
    dep_manifest = receipt.get("dependency_input_manifest", {})
    require(dep_manifest.get("path") == "DEPENDENCY_INPUTS.json"
            and descriptor(dep_manifest, "dependency_input_manifest") == expected["DEPENDENCY_INPUTS.json"],
            "Replay dependency-input manifest binding mismatch")
    for name, item in expected.items():
        if name != "REPLAY.json":
            require(output_files.get(name) == item, f"Archive member is not bound by replay outputs: {name}")
    marker_by_module = {module: marker for marker, module in markers}
    module_logs = {f"{m}.log": m for m in modules}
    seen, folded = set(), set()
    with tarfile.open(archive_path, mode="r|gz") as archive_stream:
        for member in archive_stream:
            name = relative_name(member.name)
            require(member.isfile() and not member.issparse(), f"Non-regular archive member: {name}")
            require(name not in seen and name.casefold() not in folded, f"Duplicate archive member: {name}")
            require(name in expected, f"Unexpected archive member: {name}")
            require(member.size == expected[name]["bytes"], f"Archive size mismatch: {name}")
            seen.add(name)
            folded.add(name.casefold())
            stream = archive_stream.extractfile(member)
            require(stream is not None, f"Unreadable archive member: {name}")
            keep = name in module_logs or name == "DEPENDENCY_INPUTS.json"
            chunks, h, size = [], hashlib.sha256(), 0
            with stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    h.update(chunk)
                    size += len(chunk)
                    if keep:
                        chunks.append(chunk)
            require({"bytes": size, "sha256": h.hexdigest()} == expected[name], f"Archive bytes mismatch: {name}")
            if name in module_logs:
                text = b"".join(chunks).decode("utf-8", errors="replace")
                require(re.search(FORBIDDEN_LOG, text) is None, f"Forbidden dependency in archived log: {name}")
                marker = marker_by_module.get(module_logs[name])
                if marker is not None:
                    require(marker in text, f"Audit marker absent from archived log: {marker}")
            elif name == "DEPENDENCY_INPUTS.json":
                dependencies = path_map(parse_json(b"".join(chunks), name), name)
                require(type(dep_manifest.get("file_count")) is int
                        and len(dependencies) == dep_manifest["file_count"], "Dependency manifest count mismatch")
    require(seen == set(expected), "Missing archive members: " + ", ".join(sorted(set(expected) - seen)))
    return len(seen)


def check(root: Path) -> dict[str, int]:
    root = root.resolve(strict=True)
    require(root.is_dir(), "Repository root is not a directory")
    current = parse_json(inside(root, "CURRENT_VERSION.json").read_bytes(), "CURRENT_VERSION.json")
    require(current.get("schema") == "critical-depth.current-version.v1", "Unexpected current-version schema")
    publications = path_map(current.get("publication_files"), "publication_files")
    require(all(name.casefold() != "current_version.json" for name in publications),
            "CURRENT_VERSION.json cannot hash itself")
    require(PUBLICATION_REQUIRED.issubset(publications), "Current manuscript, statement, correspondence, or checker is unbound")
    compare_disk(root, publications, "publication")
    verification = current.get("verification", {})
    receipt_path = inside(root, verification.get("receipt_path"))
    proof_inputs_path = inside(root, verification.get("proof_inputs_path"))
    contents_path = inside(root, verification.get("evidence_contents_path"))
    for path in [receipt_path, proof_inputs_path, contents_path]:
        require(path.relative_to(root).as_posix() in publications, "Evidence metadata is absent from publication_files")
    modules, markers = reference_policy(root)
    inputs = path_map(parse_json(proof_inputs_path.read_bytes(), "INPUTS.json"), "proof_inputs")
    required_inputs = {f"mathlib-review/{m}.lean" for m in modules} | CONFIG_INPUTS
    require(len(inputs) == MODULE_COUNT + len(CONFIG_INPUTS) and set(inputs) == required_inputs,
            "Proof inputs must cover all 346 Lean modules and the eight exact configuration/runner files")
    compare_disk(root, inputs, "proof input")
    receipt = parse_json(receipt_path.read_bytes(), "REPLAY.json")
    output_files = check_receipt(receipt, modules, markers)
    contents = parse_json(contents_path.read_bytes(), "EVIDENCE_CONTENTS.json")
    archived = check_archive(root, contents_path, contents, receipt, receipt_path, proof_inputs_path,
                             modules, markers, output_files)
    return {"publication_files": len(publications), "proof_inputs": len(inputs),
            "modules": len(modules), "audits": len(markers), "archive_members": archived}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    try:
        counts = check(args.root)
    except (CheckError, OSError, ValueError, TypeError, AttributeError, KeyError, tarfile.TarError) as error:
        print(f"CURRENT_VERSION_CHECK_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
    print("CURRENT_VERSION_CHECK_PASSED " + " ".join(f"{key}={value}" for key, value in counts.items()))
    print("Checked publication bytes and recorded replay evidence; no Lean process was run.")
