#!/usr/bin/env python3
"""Check every ``#print axioms`` command in an audit source against its captured Lean log."""

import argparse
from collections import Counter
from pathlib import Path
import re
import sys


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_ROOT = re.compile(r"^[ \t]*#print[ \t]+axioms[ \t]+(?P<name>\S+)", re.MULTILINE)
DEPENDENCY_REPORT = re.compile(
    r"'(?P<name>[^\r\n]*?)' depends on axioms:\s*\[(?P<axioms>.*?)\]", re.DOTALL
)
NO_AXIOMS_REPORT = re.compile(r"'(?P<name>[^\r\n]*?)' does not depend on any axioms")
RAW_REPORT = re.compile(r"depends on axioms\s*:\s*\[|does not depend on any axioms")
LEAN_ERROR = re.compile(
    r"(?:\.lean:\d+(?::\d+)?:\s*|^[ \t]*)(?:error|fatal error)(?:\([^)]*\))?:",
    re.IGNORECASE | re.MULTILINE,
)
UNIVERSE_SUFFIX = re.compile(r"\.\{[^}]*\}$")


def parse_expected_roots(source: str) -> list[str]:
    return [match.group("name") for match in EXPECTED_ROOT.finditer(source)]


def parse_reports(log: str) -> list[tuple[str, list[str]]]:
    reports: list[tuple[str, list[str]]] = []
    for match in DEPENDENCY_REPORT.finditer(log):
        raw_axioms = match.group("axioms").replace("\n", " ").split(",")
        axioms = [
            UNIVERSE_SUFFIX.sub("", item.strip())
            for item in raw_axioms
            if item.strip()
        ]
        reports.append((match.group("name"), axioms))
    reports.extend((match.group("name"), []) for match in NO_AXIOMS_REPORT.finditer(log))
    return reports


def describe_counts(counts: Counter[str]) -> str:
    return ", ".join(
        f"{name} (x{count})" for name, count in sorted(counts.items())
    ) or "none"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("audit_source", type=Path, help="Lean source containing #print axioms commands")
    parser.add_argument("captured_log", type=Path, help="captured stdout/stderr from Lean")
    args = parser.parse_args()

    try:
        source = args.audit_source.read_text(encoding="utf-8")
        log = args.captured_log.read_text(encoding="utf-8", errors="replace")
    except OSError as error:
        parser.error(str(error))

    expected = parse_expected_roots(source)
    reports = parse_reports(log)
    actual = [name for name, _ in reports]
    expected_counts = Counter(expected)
    actual_counts = Counter(actual)
    raw_report_count = len(RAW_REPORT.findall(log))
    issues: list[str] = []

    if not expected:
        issues.append("audit source contains no #print axioms commands")
    if not reports:
        issues.append("captured log contains zero parsed axiom reports")
    if raw_report_count != len(reports):
        issues.append(
            f"unparsed axiom reports: found {raw_report_count} report header(s), "
            f"parsed {len(reports)}"
        )
    missing = expected_counts - actual_counts
    unexpected = actual_counts - expected_counts
    if missing:
        issues.append(f"missing root reports: {describe_counts(missing)}")
    if unexpected:
        issues.append(f"unexpected root reports: {describe_counts(unexpected)}")

    nonstandard = [
        (root, axiom)
        for root, axioms in reports
        for axiom in axioms
        if axiom not in ALLOWED_AXIOMS
    ]
    if nonstandard:
        issues.append(f"nonstandard axioms: {nonstandard}")
    if "sorryAx" in log:
        issues.append("captured log mentions sorryAx")
    lean_errors = [line.strip() for line in log.splitlines() if LEAN_ERROR.search(line)]
    if lean_errors:
        issues.append(f"Lean errors: {lean_errors}")

    if issues:
        for issue in issues:
            print(f"FAIL: {issue}", file=sys.stderr)
        return 1

    print(f"verified {len(reports)} axiom report(s); all roots and axioms are allowed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
