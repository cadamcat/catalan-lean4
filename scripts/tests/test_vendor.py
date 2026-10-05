import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "check_vendor", Path(__file__).parents[1] / "check_vendor.py"
)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class VendorReconstructionMutationControl(unittest.TestCase):
    def test_one_byte_mutation_fails_for_named_vendored_file(self):
        source = Path(__file__).resolve().parents[2]
        relative = "Lean4/ClassFieldTheory/AlgebraicNumberTheory/AdeleBaseChange.lean"

        with tempfile.TemporaryDirectory(prefix="cft-vendor-mutation-control-") as d:
            copy = Path(d) / "repo"
            subprocess.run(
                ["git", "clone", "--shared", "--no-checkout", str(source), str(copy)],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            shutil.copytree(
                source / "vendor" / "ClassFieldTheory",
                copy / "vendor" / "ClassFieldTheory",
            )

            vendored_file = copy / "vendor" / "ClassFieldTheory" / relative
            original = vendored_file.read_bytes()
            vendored_file.write_bytes(bytes([original[0] ^ 1]) + original[1:])

            with self.assertRaises(ValueError) as caught:
                module.check(copy)
            self.assertEqual(
                str(caught.exception),
                "vendor_patch_reproduction_mismatch: " + relative,
            )


if __name__ == "__main__":
    unittest.main()
