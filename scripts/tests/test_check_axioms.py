"""Disposable CLI controls for the axiom-log checker."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "check_axioms.py"


class CheckAxiomsTests(unittest.TestCase):
    def run_checker(self, source: str, log: str) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory(prefix="check-axioms-") as temporary:
            directory = Path(temporary)
            source_path = directory / "Axioms.lean"
            log_path = directory / "lean.log"
            source_path.write_text(source, encoding="utf-8")
            log_path.write_text(log, encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(SCRIPT), str(source_path), str(log_path)],
                capture_output=True,
                text=True,
                check=False,
            )

    def test_standard_multiline_and_no_axioms_reports_pass(self) -> None:
        result = self.run_checker(
            "#print axioms Demo.root'\n#print axioms Demo.noAxioms\n",
            "'Demo.root'' depends on axioms: [propext.{u_1},\n"
            "  Classical.choice, Quot.sound]\n"
            "'Demo.noAxioms' does not depend on any axioms\n",
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_missing_root_fails(self) -> None:
        result = self.run_checker(
            "#print axioms Demo.present\n#print axioms Demo.missing\n",
            "'Demo.present' does not depend on any axioms\n",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing root reports", result.stderr)

    def test_custom_axiom_with_apostrophe_name_fails(self) -> None:
        result = self.run_checker(
            "#print axioms Demo.root'\n",
            "'Demo.root'' depends on axioms: [customAxiom']\n",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("customAxiom'", result.stderr)

    def test_multiline_fourth_axiom_fails(self) -> None:
        result = self.run_checker(
            "#print axioms Demo.root\n",
            "'Demo.root' depends on axioms: [propext,\n"
            "  Classical.choice,\n  Quot.sound,\n  rogueFourthAxiom]\n",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("rogueFourthAxiom", result.stderr)

    def test_zero_reports_fails(self) -> None:
        result = self.run_checker("#print axioms Demo.root\n", "")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("zero parsed axiom reports", result.stderr)


if __name__ == "__main__":
    unittest.main()
