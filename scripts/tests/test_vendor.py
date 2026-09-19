import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("check_vendor", Path(__file__).parents[1] / "check_vendor.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class VendorTests(unittest.TestCase):
    def fixture(self, root):
        vendor = root / "vendor" / "ClassFieldTheory"
        (vendor / "Lean4").mkdir(parents=True)
        data = b"-- test fixture\n"
        (vendor / "Lean4" / "Test.lean").write_bytes(data)
        (vendor / "LICENSE").write_bytes(b"test license")
        (vendor / "SOURCES.json").write_text(json.dumps({
            "moduleCount": 1,
            "files": [{"path": "Lean4/Test.lean", "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}],
            "licenseSha256": hashlib.sha256(b"test license").hexdigest()}))
        return vendor

    def test_valid_fixture(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.fixture(root)
            self.assertEqual(module.check(root), 1)

    def test_mutated_source_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            vendor = self.fixture(root)
            (vendor / "Lean4" / "Test.lean").write_text("changed")
            with self.assertRaisesRegex(ValueError, "vendor_source_hash_mismatch"):
                module.check(root)

    def test_unlisted_source_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            vendor = self.fixture(root)
            (vendor / "Lean4" / "Extra.lean").write_text("-- extra")
            with self.assertRaisesRegex(ValueError, "vendor_inventory_mismatch"):
                module.check(root)
