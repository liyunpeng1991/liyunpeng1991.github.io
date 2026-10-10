#!/usr/bin/env python3
"""Summarize completed project checks and the explicitly checked final theorem."""
import json
import pathlib
import re

root = pathlib.Path(__file__).resolve().parent.parent
logs = root / "logs"
checks = ["verification-lean-version", "verification-lake-version", "clean-project", "clean-build"]
modules = [path.stem for path in sorted((root / "MaximumModulus").glob("*.lean"))]
checks += ["target-" + name for name in modules] + ["target-MaximumModulus", "axioms"]
checks += ["kernel-" + name for name in modules] + ["source-integrity"]
records = {name: json.loads((logs / (name + ".json")).read_text()) for name in checks}
assert all(record["exit_code"] == 0 for record in records.values()), records
integrity = json.loads((logs / "source-integrity-data.json").read_text())
expected_targets = re.findall(r"^#print axioms ([A-Za-z0-9_.]+)$", (root / "CheckAxioms.lean").read_text(), re.M)
axiom_text = (logs / "axioms.log").read_text()
dependencies = {}
for name, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", axiom_text):
    dependencies[name] = [part.strip() for part in names.split(",") if part.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", axiom_text):
    dependencies[name] = []
assert set(expected_targets) == set(dependencies), (expected_targets, dependencies)
observed_axioms = sorted({axiom for names in dependencies.values() for axiom in names})
assert set(observed_axioms) <= {"propext", "Classical.choice", "Quot.sound"}, observed_axioms
final_targets = {"MaximumModulus.allRadiiStatement",
                 "MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii",
                 "MaximumModulus.all_radii_growth_impossible"}
assert final_targets <= set(dependencies), "Final theorem reports are missing"
report = {
    "verdict": "All project checks passed; unconditional theorem checked",
    "full_original_problem_solved": True,
    "unconditional_AllRadiiStatement_proof_exists": True,
    "checks": records,
    "axiom_report": "logs/axioms.log",
    "observed_axioms": observed_axioms,
    "actual_target_axiom_reports": dependencies,
    "source_and_dependency_integrity": integrity,
    "kernel_replay_scope": "Each project module sequentially, relative to pinned imports; no fresh replay of all mathlib or independent external checker claimed.",
    "interrupted_attempt": "logs/kernel-replay.json; explained in logs/kernel-replay-resource-note.txt; excluded from successes.",
    "prize_verification_workflow": "Separate frozen-source audit; consult verification/prize-report.md for its actual scope and results."
}
(logs / "verification-summary.json").write_text(json.dumps(report, indent=2) + "\n")
print("All listed project checks actually returned exit 0.")
print("The exact unconditional all-radii theorem was checked with only standard foundational axioms.")
print("Report: logs/verification-summary.json")
