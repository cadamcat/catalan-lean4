#!/usr/bin/env python3
"""Reconstruct the ClassFieldTheory port from its recorded source and patch."""
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile


def _safe_path(value, label):
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError(label + ": invalid path")
    return path


def _git_blobs(root, commit, paths):
    specs = [f"{commit}:{path}" for path in paths]
    result = subprocess.run(
        ["git", "-C", str(root), "cat-file", "--batch"],
        input=("\n".join(specs) + "\n").encode(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode:
        raise ValueError("vendor_baseline_read_failed: " + result.stderr.decode(errors="replace").strip())

    blobs = {}
    output = result.stdout
    offset = 0
    for path in paths:
        end = output.find(b"\n", offset)
        if end < 0:
            raise ValueError("vendor_baseline_read_failed: truncated git output")
        header = output[offset:end].decode(errors="replace").split()
        offset = end + 1
        if len(header) == 2 and header[1] == "missing":
            raise ValueError("vendor_baseline_blob_missing: " + path)
        if len(header) != 3 or header[1] != "blob":
            raise ValueError("vendor_baseline_not_blob: " + path)
        size = int(header[2])
        blob = output[offset : offset + size]
        if len(blob) != size or output[offset + size : offset + size + 1] != b"\n":
            raise ValueError("vendor_baseline_read_failed: truncated blob " + path)
        blobs[path] = blob
        offset += size + 1
    if offset != len(output):
        raise ValueError("vendor_baseline_read_failed: trailing git output")
    return blobs


def check(root):
    root = root.resolve()
    vendor = root / "vendor" / "ClassFieldTheory"
    manifest = json.loads((vendor / "SOURCES.json").read_text())
    entries = manifest["files"]
    expected = {entry["path"] for entry in entries}
    if len(expected) != len(entries) or len(entries) != manifest["moduleCount"]:
        raise ValueError("vendor_inventory_count_mismatch")

    actual = {
        path.relative_to(vendor).as_posix()
        for path in (vendor / "Lean4").rglob("*.lean")
    }
    if actual != expected:
        raise ValueError("vendor_inventory_mismatch")
    for path in (vendor / "Lean4").rglob("*.lean"):
        if path.is_symlink():
            raise ValueError("vendor_symlink_rejected: " + path.relative_to(vendor).as_posix())

    upstream_commit = manifest["commit"]
    port_commit = manifest["portCommit"]
    baseline_commit = manifest["baselineProjectCommit"]
    patch_rel = _safe_path(manifest["portPatch"], "vendor_patch_path")
    patch_file = (vendor / Path(*patch_rel.parts)).resolve()
    if not patch_file.is_relative_to(vendor.resolve()):
        raise ValueError("vendor_patch_path_escape")
    patch_archive = patch_file.read_bytes()
    if hashlib.sha256(patch_archive).hexdigest() != manifest["portPatchSha256"]:
        raise ValueError("vendor_patch_hash_mismatch: " + patch_rel.as_posix())
    try:
        patch = gzip.decompress(patch_archive)
    except OSError as exc:
        raise ValueError("vendor_patch_decode_failed: " + patch_rel.as_posix()) from exc

    baseline_paths = []
    for entry in entries:
        path = _safe_path(entry["path"], "vendor_source_path")
        if not path.parts or path.parts[0] != "Lean4":
            raise ValueError("vendor_source_path_invalid: " + entry["path"])
        if (
            entry["sourceCommit"] != upstream_commit
            or entry["sourcePath"] != entry["path"]
            or entry["portCommit"] != port_commit
            or entry["portPath"] != entry["path"]
            or entry["patch"] != patch_rel.as_posix()
        ):
            raise ValueError("vendor_provenance_mismatch: " + entry["path"])
        baseline_path = "vendor/ClassFieldTheory/" + path.as_posix()
        baseline_paths.append(baseline_path)

    base_blobs = _git_blobs(root, baseline_commit, baseline_paths)
    for entry, baseline_path in zip(entries, baseline_paths):
        data = base_blobs[baseline_path]
        if len(data) != entry["baseBytes"] or hashlib.sha256(data).hexdigest() != entry["baseSha256"]:
            raise ValueError("vendor_upstream_source_mismatch: " + entry["sourcePath"])

    patch_paths = {
        line[6:].decode()
        for line in patch.splitlines()
        if line.startswith(b"+++ b/")
    }
    expected_patch_paths = {"vendor/ClassFieldTheory/" + path for path in expected}
    if patch_paths != expected_patch_paths:
        raise ValueError("vendor_patch_inventory_mismatch")

    with tempfile.TemporaryDirectory(prefix="cft-vendor-reconstruction-") as directory:
        reconstruction = Path(directory)
        for baseline_path, data in base_blobs.items():
            destination = reconstruction / baseline_path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
        reconstructed_patch = reconstruction / "vendor-port.patch"
        reconstructed_patch.write_bytes(patch)
        subprocess.run(["git", "init", "--quiet"], cwd=reconstruction, check=True)
        for operation in ("--check", None):
            command = ["git", "apply"]
            if operation:
                command.append(operation)
            command.extend(["--whitespace=nowarn", str(reconstructed_patch)])
            result = subprocess.run(
                command,
                cwd=reconstruction,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            if result.returncode:
                detail = result.stderr.decode(errors="replace").strip()
                raise ValueError("vendor_patch_apply_failed: " + detail)

        for entry in entries:
            relative = entry["path"]
            current_path = vendor / Path(*_safe_path(relative, "vendor_source_path").parts)
            reconstructed_path = reconstruction / "vendor" / "ClassFieldTheory" / Path(
                *_safe_path(relative, "vendor_source_path").parts
            )
            if current_path.read_bytes() != reconstructed_path.read_bytes():
                raise ValueError("vendor_patch_reproduction_mismatch: " + relative)

    license_path = vendor / "LICENSE"
    if hashlib.sha256(license_path.read_bytes()).hexdigest() != manifest["licenseSha256"]:
        raise ValueError("vendor_license_hash_mismatch")
    return len(entries)


if __name__ == "__main__":
    try:
        count = check(Path(__file__).resolve().parents[1])
    except (ValueError, OSError, KeyError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
    print(f"Reconstructed and verified {count} vendored ClassFieldTheory sources and the license.")
