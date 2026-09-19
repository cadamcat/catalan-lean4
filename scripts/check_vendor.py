#!/usr/bin/env python3
"""Check the vendored Lean inventory and hashes against the retained source manifest."""
import hashlib
import json
from pathlib import Path
import sys


def check(root):
    vendor = root / "vendor" / "ClassFieldTheory"
    manifest = json.loads((vendor / "SOURCES.json").read_text())
    entries = manifest["files"]
    expected = {entry["path"] for entry in entries}
    actual = {path.relative_to(vendor).as_posix() for path in (vendor / "Lean4").rglob("*.lean")}
    if len(expected) != len(entries) or len(entries) != manifest["moduleCount"]:
        raise ValueError("vendor_inventory_count_mismatch")
    if actual != expected:
        raise ValueError("vendor_inventory_mismatch")
    for entry in entries:
        source = (vendor / entry["path"]).resolve()
        if not source.is_relative_to(vendor.resolve()):
            raise ValueError("vendor_path_escape")
        data = source.read_bytes()
        if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError("vendor_source_hash_mismatch: " + entry["path"])
    if hashlib.sha256((vendor / "LICENSE").read_bytes()).hexdigest() != manifest["licenseSha256"]:
        raise ValueError("vendor_license_hash_mismatch")
    return len(entries)


if __name__ == "__main__":
    try:
        count = check(Path(__file__).resolve().parents[1])
    except (ValueError, OSError, KeyError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
    print(f"Verified {count} vendored Lean sources and the license.")
