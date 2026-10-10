**Overall verdict: Conditional pass — Lean target verification passed; configured external comparison is pending.**

The local formalization addresses the specified original all-radii question with the required literal function-value statement. Its frozen temporary audit snapshot `8b731b51dcb0ed3d7e8c6463b6266c35d8099c85` passed the sandboxed clean project build and all 8 manifest targets, including all four independently written statement/growth/finiteness bridges. Every target's actual transitive axiom output is exactly `propext`, `Classical.choice`, and `Quot.sound`; no placeholder or custom proof axiom appears. The original project's clean verification also passed 43 direct source checks, 42 sequential project-module kernel replays, and the integrity scan. The original all-radii conclusion is fully covered under the recorded Lean/pinned-library trust conditions. The configured external comparator is still running, so completion of that stronger verification workflow and its acceptance judgment are pending. This is an interim report, not an award or publication decision.

| Required question | Judgment at this draft | Evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | Yes, as a statement correspondence finding. | The literal final declaration uses the actual function values, the original entire/nonzero/non-monomial class, one bound before all radius thresholds, and explicit finiteness. Independently written coverage: [statement-coverage.md](../evidence/statement-coverage.md). |
| Did the specified commit actually pass verification? | Yes for the recorded clean build, source/target, bridge, and axiom checks; external comparison pending. | Sandboxed workflow run exited 0, all 8 target result sets passed, and inputs remained stable. |
| Does it fully solve the original problem? | Yes under the recorded Lean kernel and pinned-import trust conditions. | Exact statement correspondence, all original-function-class obligations, explicit finiteness, and independently checked negative-growth bridges; no mathematical gap or added premise was found. |
| Does it meet the Lean completeness requirements? | Meets the no-placeholder Lean proof requirements; stronger workflow completion/acceptance not yet determined. | All 8 target axiom reports contain only the three standard foundations; production integrity scan passed. Configured external comparison remains pending. |

The observed verification levels are static statement/dependency inspection, actual clean compilation of all project sources, explicit rechecks of the frozen target sources, independent original-problem bridge checks, transitive target axiom inspection, and sequential replay of all 42 original project modules relative to their pinned imports. Replay uses Lean's kernel implementation and is not an independent external checker; it does not fresh-replay all mathlib. Preflight does not run Lean and preparation only generates audit sources. The target audit and replay successes below are based on their separate executed logs. No completed external comparison is inferred from exports or checker availability.

## Pinned scope and evidence

This is direct local-source verification. There is no awards pull request, proof repository publication, submitter-specified Git revision, or proposed GitHub action. Awards base/head branches, award identifiers, JSP identifiers, and Erdős numbering are not applicable to this run. The temporary commit is only a reproducible audit snapshot; it is not an author-submitted or published revision.

- Original project: `/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean`.
- Manuscript: `/Users/gluon/Documents/ChatGPT/Maximum Modulus/maximum_modulus_points.tex`, read as a candidate proof and left unchanged. Both the executed project integrity audit and a separate read-only recheck at `2026-10-10T19:38:22.522911+00:00` record SHA256 `bc951c3ffa7d3579b2f39a0949e38db27338ac32ac050e3f5359d4452573a7b1`; [completed-target-audit-review.json](../evidence/completed-target-audit-review.json).
- Frozen proof root: `/private/tmp/mm-lean-verify-20261010/sources/proof`.
- Exact frozen Git revision: `8b731b51dcb0ed3d7e8c6463b6266c35d8099c85`, created `2026-10-10T19:25:24.768386+00:00`; role and hashes for 54 snapshot files are in [source-snapshot.json](../evidence/source-snapshot.json). Of those, 53 production source/config/script files were copied exactly; the verifier intentionally supplied a snapshot-specific `.gitignore` before the temporary commit. The original `.gitignore` was never changed. Its [preserved diff](../evidence/snapshot-gitignore.diff) changes cache/output packaging only; no proof, Lake configuration, dependency lock, or script changed. All 53 original and frozen production hashes were independently rechecked against the snapshot record.
- Workflow: [the user-specified lean-verify skill](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/skills/lean-verify/SKILL.md), fixed at `16877004910734cecca83cc5af0fec2f5a4125b3`. Downloaded copies and hashes are under `/private/tmp/mm-lean-verify-workflow-20261010/`; downloads used system curl with TLS validation. Workflow script SHA256: `5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07`.
- Manifest: [targets.json](targets.json), SHA256 `ff4f6eac020fcbe484fee97c64fda93eb14822f8a1ead5fc6f9b9b9c81e22eb5`, with 8 targets and 7 original-statement requirements. Its `coverage: full` entries express semantic correspondence, not unexecuted mechanical results.
- Independent bridge source: [OriginalProblem.lean](OriginalProblem.lean), SHA256 `4be4fb7093e9dd1176de51aed1b3a755507c14ea7ac60e236c7e122e3fc992e7`.
- Independent comparator specification: [ComparatorChallenge.lean](ComparatorChallenge.lean), SHA256 `b51e5b557b2c057251c00629b327ca5417ecf91bc6319464c3097eece0c634bf`; [comparator.json](comparator.json), SHA256 `264ba026cc3b363eb8141dac7715dc66d47ede31c4d14eeae20e07ff05e11b3d`.

The bridge and comparator sources are trusted auditor files installed as explicitly untracked files under `MaximumModulus/Audit/` in the frozen checkout. They do not change the committed proof or Lake configuration. The actual target workflow's before/after checks observed exactly these two untracked files, no tracked modifications, and stable target/config hashes.

## Original statement and correspondence

The specified original sources are [Hayman–Lingham, arXiv 1809.07200v2, Problem 2.16(b), printed page 29](https://arxiv.org/pdf/1809.07200v2#page=30), [Glücksam–Pardo-Simón, arXiv 2208.11154v2, Question 1.1(b)](https://arxiv.org/html/2208.11154v2#S1), and [Pardo-Simón–Sixsmith, arXiv 2607.09462v1, introduction](https://arxiv.org/html/2607.09462v1#S1). The problem asks whether one non-monomial entire function can have its number of exact maximum-modulus points tend to infinity on all radii. The later sources explicitly exclude monomials; this includes nonzero constants. The selected-radii limsup question, answered affirmatively by Herzog–Piranian in 1968, is a different proposition and remains compatible with the formal conclusion. The project's original-source review is `docs/sources.md`.

The exact final target is `MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii`, in `MaximumModulus/AllRadii.lean`. Its hypotheses and conclusion are:

```lean
(f : ℂ → ℂ)
(hf : Differentiable ℂ f) (hne : f ≠ 0)
(hnm : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) :
∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧
  ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).Finite ∧
  ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).ncard ≤ B
```

Complex differentiability on the entire domain expresses entire holomorphy. Function inequality `f ≠ 0` excludes the identically zero function. The non-monomial hypothesis is explicit and includes exponent zero. The final theorem takes no analytic geometry, finite-map, reciprocity, or global-degree assumption from the manuscript. Since `B` occurs before `∀ R`, it cannot depend on the chosen threshold or radius. `r > R > 0` gives a positive circle. Finiteness is stated alongside the bound, so the value of `Set.ncard` on infinite sets cannot make the conclusion vacuous.

The independently written `IndependentOriginal.CircleMaximizers` repeats the actual norm comparisons instead of aliasing production definitions. `IndependentOriginal.IntendedStatement` repeats the complete original hypotheses and quantifiers. Its `original_problem_solved` bridge applies the literal production theorem. Its independently defined growth predicate regards an infinite maximum set as a large-cardinality case; `original_all_radii_growth_impossible` contradicts that predicate using the supplied finite bounded radius. `original_count_not_tendsto_atTop` independently negates natural-count divergence, and `original_positive_circle_finiteness` connects the actual independently defined set to the production finiteness theorem. All four bridge targets were built, their source directly rechecked, and their declarations/axioms inspected with exit 0 in the sandboxed [workflow run](workflow-run-01/result.json).

For the implication, suppose all radii beyond some threshold have count greater than the fixed `B` (or have an infinite maximum set). The cofinal theorem supplies a larger radius with a finite maximum set of cardinality at most `B`, a contradiction. Every positive circle is also proved finite for the original function class, so the natural count has its intended meaning on the full positive domain.

The seven-row coverage matrix is in [statement-coverage.md](../evidence/statement-coverage.md). The result resolves only the requested all-radii question; it does not claim a bound on every radius or refute selected-radii unboundedness.

## Environment, pins, and provenance

| Item | Observed value and evidence |
| --- | --- |
| OS and architecture | macOS 15.5, build 24F74, arm64. Actual metadata: [dependency-tool-provenance.json](../evidence/dependency-tool-provenance.json). |
| Isolation | Native `/usr/bin/sandbox-exec` profile [isolation.sb](isolation.sb), with a sanitized environment. [isolation-probe-06.log](../logs/isolation-probe-06.log) records rejected outside data reads/writes and networking plus successful execution of the trusted exact Lean binary. Profile and probes are retained; a temporary directory alone is not treated as isolation. |
| Resource controls | Per-process CPU 1200 seconds and per-file size 2 GiB; descendant RSS monitored each second with a 10 GiB limit; total wall cap 1800 seconds. Stack inherited at 8,372,224 bytes. macOS rejected explicit address-space/stack setters; no address-space cap or newly imposed stack limit is claimed. Diagnostics are retained under `logs/isolation-limit-diagnostic.txt`. |
| Lean pin | `leanprover/lean4:v4.35.0-rc4`; actual Lean reports `4.35.0-rc4`, `arm64-apple-darwin24.6.0`, commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Release. |
| Lake | Actual Lake reports `5.0.0-src+c29b6dd (Lean version 4.35.0-rc4)`. Version commands exited 0; copies of original command records and outputs are under [evidence/setup-logs](../evidence/setup-logs). |
| Tool location and hashes | Exact local toolchain at `/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64/bin`. Frozen local hashes for Lean, Lake, replay tools, and all bundled external checkers are in [dependency-tool-provenance.json](../evidence/dependency-tool-provenance.json). These are local executable hashes, not publisher signatures. Elan is not in the sanitized verification PATH and is not used for these checks. |
| Dependency lock | `lake-manifest.json` SHA256 `cb333575666396aefa2ed281978edc586f0535a0079b76012f32db0f18052b38`. All 9 actual copied dependency checkouts match the lock, and all have clean Git status. Actual Git commands and outputs are in [dependency-tool-provenance.json](../evidence/dependency-tool-provenance.json). |
| Cache provenance | Imported dependency build products were copied from the pinned original project's mathlib cache, fetched with mathlib's `lake exe cache get`; actual fetch commands and exit-0 records are copied under [evidence/setup-logs](../evidence/setup-logs). The frozen project's own build products were removed before its clean build. The project clean build does not itself recompile all mathlib sources. Full target-closure comparison/replay results must be reported separately. |
| Sandboxed clean build | `lake build` from the frozen proof root exited 0 in 36.170943 seconds; peak monitored descendant RSS 8,734,654,464 bytes. Actual argv, environment, timing, and limits: [isolated-clean-build.json](../logs/isolated-clean-build.json); output: [isolated-clean-build.log](../logs/isolated-clean-build.log). |
| Workflow preflight | Exit 0, `ready_for_target_checks: true`, no issues. [result](workflow-preflight/result.json), [command/timing](../logs/workflow-preflight-01.json), [log](../logs/workflow-preflight-01.log). |
| Workflow preparation | Exit 0, no issues, 8 target harnesses generated. [result](workflow-prepare/result.json), [command/timing](../logs/workflow-prepare-01.json), [log](../logs/workflow-prepare-01.log). |
| Final target checks | Pending. No `mechanical_status: standard_axioms_only` result is claimed by this draft. |
| Independent bridge checks | Pending. Generated bridge sources are retained, but generation is not a Lean proof check. |
| Kernel and external comparison | Pending for this report. Matching tool binaries exist and are hashed; their existence does not establish any executed comparison. |
| Post-run source stability | Preflight/prepare and provenance collection observed only the two expected untracked trusted auditor files. Final stability checks remain to be appended after execution. |

Exact dependency revisions:

| Package | Locked and actual Git SHA |
| --- | --- |
| mathlib | `81d17696471311f5e3e2f034236df7a781449f7e` |
| plausible | `aef59637faa9e85fa2486acaaf906ce3f572af7c` |
| LeanSearchClient | `234d9e074fbd6e911b920baf32db5291c3125be0` |
| importGraph | `579f558774c4ac6840e715ba60dabf3030619349` |
| proofwidgets | `d5ad4a0b79fa7f9818fe1380d05a3f6143823c09` |
| aesop | `04879b1e1de744d5c9777c8cf63fa55a8f652e5e` |
| Qq | `e7c4cdd2f1bf9df361ef7f621b4d6867012ab65e` |
| batteries | `b71aaf60877e673fdb921f06f20987d12ee8a290` |
| Cli | `82c11b9717083154aefc5fe8d4cba4bbf046298f` |

## Proof chain, trusted specification, and pending axiom reports

The unconditional production chain factors the actual entire function at zero, proves local small-product fiber bounds, constructs finite actual physical/root-image families, and takes the closure of the actual regular high-count locus. It proves local product-projection openness in all three spherical-value cases: ordinary finite values, the omitted finite value, and infinity. Compactness of the sphere gives closed product projection; the connected-product argument and small-product exclusion force the high-count locus to be empty. Countable exceptional values and the maximum-to-fiber correspondence then give arbitrarily large bounded maximum-count radii. Explicit physical-set finiteness and duplicate-safe counts are used throughout.

This reduces the manuscript's proposed analytic-normalization and generic-component-degree machinery to local power branches, stabilized physical collision kernels, and closure continuation. No global analytic-curve normalization theorem is assumed. The stronger locally finite exceptional-radius theorem and sharpness examples are outside the required delivery scope. The independent review record is the original project's `docs/continuation-formal-review.md`; final code-level axiom checking remains necessary.

The configured permitted production axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. This draft does not assert the pending final outputs. The final report must paste or link the complete actual `#print axioms` output for each manifest target:

| Target | Module | Final transitive axiom output |
| --- | --- | --- |
| `MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii` | `MaximumModulus.AllRadii` | Pending |
| `MaximumModulus.allRadiiStatement` | `MaximumModulus.AllRadii` | Pending |
| `MaximumModulus.all_radii_growth_impossible` | `MaximumModulus.AllRadii` | Pending |
| `MaximumModulus.finite_maxPoints` | `MaximumModulus.Finiteness` | Pending |
| `IndependentOriginal.original_problem_solved` | `MaximumModulus.Audit.OriginalProblem` | Pending |
| `IndependentOriginal.original_all_radii_growth_impossible` | `MaximumModulus.Audit.OriginalProblem` | Pending |
| `IndependentOriginal.original_count_not_tendsto_atTop` | `MaximumModulus.Audit.OriginalProblem` | Pending |
| `IndependentOriginal.original_positive_circle_finiteness` | `MaximumModulus.Audit.OriginalProblem` | Pending |

The independent comparator module imports trusted mathlib primitives only and repeats the original literal target. This pinned comparator rejects an axiom/theorem declaration-kind mismatch, so the trusted challenge uses a private specification axiom followed by a same-named theorem. That private axiom states the expected goal only: it is not a proved solution, not a permitted production axiom, and not a dependency of the production theorem. The challenge module is deliberately excluded from the production proof-target manifest. The comparator must compare the literal types and inspect the solution's transitive proof closure against the three permitted foundations; it cannot certify the challenge's stipulated goal as a proof.

The comparator configuration selects the actual solution module `MaximumModulus.AllRadii`, independent challenge module `MaximumModulus.Audit.ComparatorChallenge`, exactly one literal final theorem, and no substituted production definitions. If the comparator's Linux-only sandbox is disabled on macOS, execution must remain inside the tested native OS sandbox; the final report must retain both the native runner arguments and comparator flag.

## Reproduction commands actually executed

All commands below launch the native sandbox through the same trusted runner. The runner's inner working directory is `/private/tmp/mm-lean-verify-20261010/sources/proof`; command logs retain the complete environment and resource controls. The outer working directory was `/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean`.

The root verifier executed the clean frozen-source build before the target workflow:

```text
python3 /private/tmp/mm-lean-verify-20261010/audit/run_isolated.py isolated-clean-build lake build
```

The following preflight, prepare, and read-only provenance commands were actually executed and each exited 0:

```text
python3 /private/tmp/mm-lean-verify-20261010/audit/run_isolated.py workflow-preflight-01 python3 /private/tmp/mm-lean-verify-workflow-20261010/scripts/audit.py preflight /private/tmp/mm-lean-verify-20261010/audit/targets.json --out /private/tmp/mm-lean-verify-20261010/audit/workflow-preflight

python3 /private/tmp/mm-lean-verify-20261010/audit/run_isolated.py workflow-prepare-01 python3 /private/tmp/mm-lean-verify-workflow-20261010/scripts/audit.py prepare /private/tmp/mm-lean-verify-20261010/audit/targets.json --out /private/tmp/mm-lean-verify-20261010/audit/workflow-prepare

python3 /private/tmp/mm-lean-verify-20261010/audit/run_isolated.py dependency-tool-provenance-01 python3 /private/tmp/mm-lean-verify-20261010/audit/collect_provenance.py
```

Final target-run, independent bridge, replay, comparator, checker-output, and post-run-stability commands/results are pending insertion by the root verifier. They have not been executed by the author of this draft.

## Outstanding evidence and finalization

1. Execute the manifest target audit inside the tested native sandbox and preserve target counts, exact exit status, before/after hashes, and complete outputs.
2. Compile and check the independent original-problem bridge. Add all eight actual transitive axiom reports and distinguish the trusted comparator goal specification from production proof dependencies.
3. Complete compatible kernel replay and configured independent comparison/external checker runs. Record exact tools, targets, exported artifact hashes, outcomes, and any checker limitations; successful build alone is not described as an external check.
4. Recheck the frozen committed sources, lockfile, dependency revisions/status, trusted auditor inputs, and original manuscript hash after execution.
5. Replace the interim verdict and all four judgments using the final evidence. A standard-axioms-only mechanical result alone does not decide statement coverage; retain the independent correspondence findings.

No confirmed mathematical defect or statement mismatch was found in the reviewed material. The pending items above are verification obligations, not claims of a mathematical obstruction. This run stays local and does not publish, submit, merge, or determine award eligibility.
