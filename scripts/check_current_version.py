#!/usr/bin/env python3
"""Check current publication bytes and the packaged full-replay evidence.

Run `python -B scripts/check_current_version.py` from any directory, or provide
`--root /path/to/checkout`. This reads files and streams the evidence archive;
it does not extract files, invoke Lean, or change the checkout.
Timestamp checks compare bytes and recorded outcomes; they do not verify TSA signatures.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timedelta
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


def check_timestamp(root: Path, current: dict[str, object],
                    publications: dict[str, dict[str, object]],
                    proof_inputs: dict[str, dict[str, object]]) -> int:
    """Check timestamp bindings and declared outcomes, without cryptographic verification."""
    timestamp = current.get("timestamp")
    require(isinstance(timestamp, dict) and timestamp.get("protocol") == "RFC 3161",
            "Unexpected current timestamp protocol")
    directory = relative_name(timestamp.get("directory"))
    prefix = directory + "/"
    directory_path = (root / directory).resolve(strict=True)
    require(directory_path.is_dir() and directory_path.is_relative_to(root),
            "Timestamp directory escapes repository or is not a directory")
    metadata = {}
    for key in ["payload_manifest_path", "receipt_path", "readme_path"]:
        name = relative_name(timestamp.get(key))
        require(name.startswith(prefix) and name in publications,
                f"Timestamp metadata is outside its directory or publication binding: {key}")
        metadata[key] = name
    require(len(set(metadata.values())) == 3, "Timestamp metadata paths must be distinct")
    manifest_name = metadata["payload_manifest_path"]
    payload = parse_json(inside(root, manifest_name).read_bytes(), manifest_name)
    require(payload.get("schema") == "critical-depth.timestamp-payload.v1",
            "Unexpected timestamp payload schema")
    require(isinstance(current.get("repository"), str) and bool(current["repository"])
            and payload.get("repository") == current["repository"],
            "Timestamp payload repository differs from current publication")
    require(isinstance(payload.get("base_commit"), str)
            and re.fullmatch(r"[0-9a-f]{40}", payload["base_commit"]) is not None,
            "Timestamp payload lacks a base commit")
    require(payload.get("excluded_paths") == ["CURRENT_VERSION.json"]
            and payload.get("excluded_prefixes") == [prefix],
            "Timestamp payload exclusion policy differs from its binding graph")
    files = path_map(payload.get("files"), "timestamp.payload.files")
    require(all(name.casefold() != "current_version.json"
                and not name.casefold().startswith(prefix.casefold()) for name in files),
            "Timestamp payload includes CURRENT_VERSION or its own evidence directory")
    compare_disk(root, files, "timestamp payload")
    for name, expected in proof_inputs.items():
        require(files.get(name) == expected, f"Timestamp payload omits or changes proof input: {name}")
    for name, expected in publications.items():
        if not name.startswith(prefix):
            require(files.get(name) == expected,
                    f"Timestamp payload omits or changes publication file: {name}")
    actual_directory_files = set()
    for path in directory_path.rglob("*"):
        require(not path.is_symlink(), "Symlink in timestamp evidence directory")
        if path.is_file():
            actual_directory_files.add(path.relative_to(root).as_posix())
    recorded_directory_files = {name for name in publications if name.startswith(prefix)}
    require(actual_directory_files == recorded_directory_files,
            "Timestamp directory files differ from the publication binding")

    receipt_name = metadata["receipt_path"]
    receipt = parse_json(inside(root, receipt_name).read_bytes(), receipt_name)
    require(receipt.get("schema") == "critical-depth.rfc3161.v1"
            and receipt.get("protocol") == "RFC 3161", "Unexpected timestamp receipt schema or protocol")
    require(isinstance(receipt.get("tsa"), str)
            and re.fullmatch(r"https?://[^\s]+", receipt["tsa"]) is not None,
            "Timestamp receipt lacks its TSA endpoint")
    tokens = receipt.get("tokens")
    require(isinstance(tokens, list) and len(tokens) == 2, "Expected exactly two timestamp tokens")
    require(all(isinstance(token, dict) for token in tokens), "Invalid timestamp token record")
    inputs = [relative_name(token.get("input_path")) for token in tokens]
    require(set(inputs) == {"manuscript/Update_branch.tex", manifest_name},
            "Timestamp tokens must bind the current TeX and payload manifest once each")
    evidence_paths = set(metadata.values())
    checks = ["request", "file", "signature_chain", "revocation_at_gen_time",
              "revocation_at_verification_time"]
    for token, input_name in zip(tokens, inputs):
        require(descriptor(token.get("input"), input_name) == file_digest(inside(root, input_name)),
                f"Timestamp token input bytes differ: {input_name}")
        for kind in ["request", "response"]:
            name = relative_name(token.get(kind + "_path"))
            require(name.startswith(prefix) and name in publications and name not in evidence_paths,
                    f"Unbound, repeated, or cyclic timestamp {kind} path: {name}")
            evidence_paths.add(name)
            require(descriptor(token.get(kind), name) == publications[name],
                    f"Timestamp {kind} descriptor differs from publication: {name}")
            require(file_digest(inside(root, name)) == publications[name],
                    f"Timestamp {kind} bytes differ: {name}")
        require(token.get("status") == "granted", "Timestamp token was not granted")
        nonce = token.get("nonce")
        require(isinstance(nonce, str) and re.fullmatch(r"0x[0-9A-Fa-f]+", nonce) is not None,
                "Timestamp token has no hexadecimal nonce")
        require(int(nonce, 16) > 0, "Timestamp token nonce must be positive")
        time_utc = token.get("time_utc")
        require(isinstance(time_utc, str) and re.fullmatch(
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|\+00:00)", time_utc) is not None,
            "Timestamp token has no UTC issue time")
        require(datetime.fromisoformat(time_utc.replace("Z", "+00:00")).utcoffset() == timedelta(0),
                "Timestamp token issue time is not UTC")
        verification = token.get("verification")
        require(isinstance(verification, dict) and all(verification.get(key) == "OK" for key in checks),
                "Timestamp receipt does not record all required verification outcomes")
    return len(files)


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
    counts = {"publication_files": len(publications), "proof_inputs": len(inputs),
              "modules": len(modules), "audits": len(markers), "archive_members": archived}
    if "timestamp" in current:
        counts["timestamp_payload_files"] = check_timestamp(root, current, publications, inputs)
    return counts


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
    if "timestamp_payload_files" in counts:
        print("Checked timestamp file bindings and declared outcomes; TSA signatures were not reverified.")
