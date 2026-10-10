**Overall verdict: Verification passed.**

The local formalization fully solves the specified original all-radii question with the required literal function-value statement. Its frozen temporary audit snapshot `8b731b51dcb0ed3d7e8c6463b6266c35d8099c85` passed the sandboxed clean project build and all 8 manifest targets, including all four independently written statement/growth/finiteness bridges. Every target's actual transitive axiom output is exactly `propext`, `Classical.choice`, and `Quot.sound`; no placeholder or custom proof axiom appears. The original project's clean verification also passed 43 direct source checks, 42 sequential project-module kernel replays, and the integrity scan. The independently specified final theorem then passed configured comparison and acceptance by Lean paranoid, lean4lean, nanoda, con-leche, con-ron, and Lean default. Post-check hashes confirm source/configuration/dependency/export stability and an unchanged manuscript. No additional mathematical premise or extended proof axiom is required. This verdict concerns proof verification, not an award or publication decision.

| Required question | Final judgment | Evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | Yes. | The literal final declaration uses the actual function values, the original entire/nonzero/non-monomial class, one bound before all radius thresholds, and explicit finiteness. Independent [statement coverage](../evidence/statement-coverage.md) and checked bridges agree. |
| Did the specified commit actually pass verification? | Yes. | Sandboxed clean build and target workflow exited 0, all 8 targets passed, configured comparison/checkers accepted, and inputs remained stable. |
| Does it fully solve the original problem? | Yes. | Exact statement correspondence, all original-function-class obligations, explicit finiteness, and independently checked negative-growth bridges; no mathematical gap or added premise was found. |
| Does it meet the Lean completeness requirements? | Meets. | No unproved custom proof axioms, placeholders, native-computation axiom, or kernel-skipping device enters any target. Actual axiom reports contain only the three standard foundations, and configured cross-checks passed. |

The observed verification levels are static statement/dependency inspection, actual clean compilation of all project sources, explicit rechecks of the frozen target sources, independent original-problem bridge checks, transitive target axiom inspection, sequential replay of all 42 original project modules relative to their pinned imports, and configured independent-challenge comparison of the final theorem's exported proof closure. Ordinary replay uses Lean's kernel implementation and does not fresh-replay all mathlib. The additional comparator run checked the actual exported solution closure using the recorded kernels, including the independently implemented external checkers. It does not claim to check unused mathlib declarations or the optional extensions. Preflight and preparation are distinguished from their subsequent executed Lean/checker operations.

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

The exact final target is `MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii`, at [AllRadii.lean:26](</Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/MaximumModulus/AllRadii.lean:26>). Its hypotheses and conclusion are:

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

For the implication, suppose all radii beyond some threshold have count greater than the fixed `B` (or have an infinite maximum set). The cofinal theorem supplies a larger radius with a finite maximum set of cardinality at most `B`, a contradiction; the production implication is at [AllRadii.lean:36](</Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/MaximumModulus/AllRadii.lean:36>). Every positive circle is also proved finite for the original function class at [Finiteness.lean:187](</Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/MaximumModulus/Finiteness.lean:187>), so the natural count has its intended meaning on the full positive domain.

The seven-row coverage matrix is in [statement-coverage.md](../evidence/statement-coverage.md). The result resolves only the requested all-radii question; it does not claim a bound on every radius or refute selected-radii unboundedness.

## Environment, pins, and provenance

| Item | Observed value and evidence |
| --- | --- |
| OS and architecture | macOS 15.5, build 24F74, arm64. Actual metadata: [dependency-tool-provenance.json](../evidence/dependency-tool-provenance.json). |
| Isolation | Native `/usr/bin/sandbox-exec` profile [isolation.sb](isolation.sb), with a sanitized environment. [isolation-probe-06.log](../logs/isolation-probe-06.log) records rejected outside data reads/writes and networking plus successful execution of the trusted exact Lean binary. Profile and probes are retained; a temporary directory alone is not treated as isolation. |
| Resource controls | Per-process CPU 1200 seconds and per-file size 2 GiB; descendant RSS monitored each second with a 10 GiB limit; total wall cap 1800 seconds. Stack inherited at 8,372,224 bytes. macOS rejected explicit address-space/stack setters; no address-space cap or newly imposed stack limit is claimed. Diagnostics are retained under `logs/isolation-limit-diagnostic.txt`. |
| Lean pin | `leanprover/lean4:v4.35.0-rc4`; actual Lean reports `4.35.0-rc4`, `arm64-apple-darwin24.6.0`, commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, Release. |
| Lake | Actual Lake reports `5.0.0-src+c29b6dd (Lean version 4.35.0-rc4)`. Version commands exited 0; copies of original command records and outputs are under [evidence/setup-logs](../evidence/setup-logs). |
| Tool location and hashes | Exact local toolchain at `/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64/bin`. Frozen local hashes for Lean, Lake, replay tools, and all bundled external checkers are in [dependency-tool-provenance.json](../evidence/dependency-tool-provenance.json); `leanexport` is separately recorded in [export-tool-provenance.json](../evidence/export-tool-provenance.json), SHA256 `92104293b343d52046207d46427d6fa42043166dd79282d7c1e2825e61857427`. These are local executable hashes, not publisher signatures. Elan is not in the sanitized verification PATH and is not used for these checks. |
| Dependency lock | `lake-manifest.json` SHA256 `cb333575666396aefa2ed281978edc586f0535a0079b76012f32db0f18052b38`. All 9 actual copied dependency checkouts match the lock, and all have clean Git status. Actual Git commands and outputs are in [dependency-tool-provenance.json](../evidence/dependency-tool-provenance.json). |
| Cache provenance | Imported dependency build products were copied from the pinned original project's mathlib cache, fetched with mathlib's `lake exe cache get`; actual fetch commands and exit-0 records are copied under [evidence/setup-logs](../evidence/setup-logs). The frozen project's own build products were removed before its clean build. The project clean build does not itself recompile all mathlib sources. Full target-closure comparison/replay results are reported separately below. |
| Sandboxed clean build | `lake build` from the frozen proof root exited 0 in 36.170943 seconds; peak monitored descendant RSS 8,734,654,464 bytes. Actual argv, environment, timing, and limits: [isolated-clean-build.json](../logs/isolated-clean-build.json); output: [isolated-clean-build.log](../logs/isolated-clean-build.log). |
| Workflow preflight | Exit 0, `ready_for_target_checks: true`, no issues. [result](workflow-preflight/result.json), [command/timing](../logs/workflow-preflight-01.json), [log](../logs/workflow-preflight-01.log). |
| Workflow preparation | Exit 0, no issues, 8 target harnesses generated. [result](workflow-prepare/result.json), [command/timing](../logs/workflow-prepare-01.json), [log](../logs/workflow-prepare-01.log). |
| Original clean verification | The `scripts/verify.sh` workflow completed successfully. Its summary records 91 exit-0 checks: versions, clean rebuild, 43 direct source rechecks, `CheckAxioms.lean`, 42 sequential module replays, and integrity scan. The summary-generator command also exited 0. Complete copied component command records/outputs and their hash manifest: [original-clean-verification](../evidence/original-clean-verification). |
| Final target checks | Sandboxed `audit.py run` exited 0 in 157.029960 seconds, peak monitored RSS 3,574,726,656 bytes. `mechanical_status: standard_axioms_only`, 8/8 manifest targets, 4 theorem and 4 bridge roles; all 26 recorded version/build/source/audit commands exited 0. [Full result](workflow-run-01/result.json), [wrapper command](../logs/workflow-target-run-01.json), [review](../evidence/completed-target-audit-review.json). |
| Independent bridge checks | All four targets built, original bridge source directly rechecked, declarations printed and transitive axioms inspected. Each passed with only the three standard axioms. Actual outputs are `workflow-run-01/0004-2.log` through `0007-2.log`. |
| Kernel replay | All 42 original project module `leanchecker --verbose` runs passed sequentially, relative to pinned imports. Complete logs under [original-clean-verification/logs](../evidence/original-clean-verification/logs). One earlier interrupted broad replay attempt is retained and explicitly excluded from successes. |
| Configured comparison | Exit 0 in 137.127210 seconds; peak monitored RSS 1,422,491,648 bytes. Lean paranoid, lean4lean, nanoda, con-leche, con-ron, and Lean default all accepted. lean4lean reports 52,015 declarations; con-leche and con-ron each report 52,018 with `--verified`. [Actual log](../logs/comparator-paranoid-01.log), [full wrapper argv/environment](../logs/comparator-paranoid-01.json). |
| Post-run source stability | At `2026-10-10T19:40:48.942449+00:00`, all 54 frozen files match the snapshot record, all 53 original production files match, all 9 dependencies match and remain clean, the manifest/config/harnesses and exports retain their hashes, frozen HEAD is unchanged with only two expected untracked auditor inputs, and manuscript SHA256 is unchanged. [Post-comparator stability](../evidence/post-comparator-stability.json). The intentional snapshot-only `.gitignore` difference is documented above. |

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

## Proof chain, trusted specification, and actual axiom reports

The unconditional production chain factors the actual entire function at zero, proves local small-product fiber bounds, constructs finite actual physical/root-image families, and takes the closure of the actual regular high-count locus. It proves local product-projection openness in all three spherical-value cases: ordinary finite values, the omitted finite value, and infinity. Compactness of the sphere gives closed product projection; the connected-product argument and small-product exclusion force the high-count locus to be empty. Countable exceptional values and the maximum-to-fiber correspondence then give arbitrarily large bounded maximum-count radii. Explicit physical-set finiteness and duplicate-safe counts are used throughout.

This reduces the manuscript's proposed analytic-normalization and generic-component-degree machinery to local power branches, stabilized physical collision kernels, and closure continuation. No global analytic-curve normalization theorem is assumed. The stronger locally finite exceptional-radius theorem and sharpness examples are outside the required delivery scope. The independent review record is the original project's `docs/continuation-formal-review.md`; the executed final axiom checks and configured exported-closure cross-checks support this unconditional proof chain.

The configured permitted production axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Each of the 8 manifest targets reports exactly this set. The original project's `CheckAxioms.lean` also inspected 126 declarations and observed only these foundations. Full original outputs and generated auditor sources are preserved. Complete final target axiom lines are in [target-axioms-complete.txt](../evidence/target-axioms-complete.txt):

| Target | Module | Final transitive axiom output |
| --- | --- | --- |
| `MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii` | `MaximumModulus.AllRadii` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0000-2.log) |
| `MaximumModulus.allRadiiStatement` | `MaximumModulus.AllRadii` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0001-2.log) |
| `MaximumModulus.all_radii_growth_impossible` | `MaximumModulus.AllRadii` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0002-2.log) |
| `MaximumModulus.finite_maxPoints` | `MaximumModulus.Finiteness` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0003-2.log) |
| `IndependentOriginal.original_problem_solved` | `MaximumModulus.Audit.OriginalProblem` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0004-2.log) |
| `IndependentOriginal.original_all_radii_growth_impossible` | `MaximumModulus.Audit.OriginalProblem` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0005-2.log) |
| `IndependentOriginal.original_count_not_tendsto_atTop` | `MaximumModulus.Audit.OriginalProblem` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0006-2.log) |
| `IndependentOriginal.original_positive_circle_finiteness` | `MaximumModulus.Audit.OriginalProblem` | `[propext, Classical.choice, Quot.sound]` — [output](workflow-run-01/0007-2.log) |

The independent comparator module imports trusted mathlib primitives only and repeats the original literal target. This pinned comparator rejects an axiom/theorem declaration-kind mismatch, so the trusted challenge uses a private specification axiom followed by a same-named theorem. That private axiom states the expected goal only: it is not a proved solution, not a permitted production axiom, and not a dependency of the production theorem. The challenge module is deliberately excluded from the production proof-target manifest. The comparator successfully compared the literal target and checked the solution's transitive proof closure against the three permitted foundations. No result is represented as proving the challenge's stipulated goal independently of the production proof.

The comparator configuration selects the actual solution module `MaximumModulus.AllRadii`, independent challenge module `MaximumModulus.Audit.ComparatorChallenge`, exactly one literal final theorem, and no substituted production definitions. Its actual log starts with `WARNING: Sandbox disabled, this run is not trustworthy.` This warning refers to disabling the comparator's Linux-only sandbox using `--inadvisably-no-sandbox`; the entire execution was wrapped in the tested native macOS `/usr/bin/sandbox-exec` profile, inherited by its subprocesses, with outside-data/network denials and resource controls. The Linux-specific layer was replaced by native OS isolation, not by unrestricted execution. The full wrapper argv and probe outcomes are preserved. No Lean kernel check was disabled.

The exported challenge has 54,014,504 bytes and SHA256 `ac2fe5af1de529ac3607406107429058256542d824ac15bf4590dba2bdde0360`; the exported solution has 360,280,894 bytes and SHA256 `dfc65218ba9d699deaa8ed3191dd66f0a076d528fc36752b2217a13225f0ffd0`. The actual build/export commands and exit-0 results are [exports/commands.json](exports/commands.json). The sandboxed exporter completed in 41.551891 seconds, peak monitored RSS 3,655,794,688 bytes; [wrapper](../logs/comparator-exports-01.json). Both byte counts and hashes were independently checked again after comparison.

## Reproduction commands actually executed

The sandbox commands below launch the same trusted runner. Outer invocations used `/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean` or `/private/tmp/mm-lean-verify-20261010/sources/proof`; the runner's checked inner working directory was always `/private/tmp/mm-lean-verify-20261010/sources/proof`. Command logs retain the complete environment and resource controls.

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

The root verifier then executed the actual target workflow and comparator inside the native sandbox, both with exit 0:

```text
python3 /private/tmp/mm-lean-verify-20261010/audit/run_isolated.py workflow-target-run-01 python3 /private/tmp/mm-lean-verify-workflow-20261010/scripts/audit.py run /private/tmp/mm-lean-verify-20261010/audit/targets.json --out /private/tmp/mm-lean-verify-20261010/audit/workflow-run-01 --lake /Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64/bin/lake --timeout 300

python3 /private/tmp/mm-lean-verify-20261010/audit/run_isolated.py comparator-exports-01 python3 /private/tmp/mm-lean-verify-20261010/audit/export_proof.py

python3 /private/tmp/mm-lean-verify-20261010/audit/run_isolated.py comparator-paranoid-01 lake comparator --config /private/tmp/mm-lean-verify-20261010/audit/comparator.json --challenge-from-export /private/tmp/mm-lean-verify-20261010/audit/exports/challenge.ndjson --solution-from-export /private/tmp/mm-lean-verify-20261010/audit/exports/solution.ndjson --paranoid --inadvisably-no-sandbox
```

The original clean verification's source/build/replay commands ran from `/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean`; each command, working directory, UTC start, exit status, elapsed time, and output is copied under `evidence/original-clean-verification/logs/`. The verifier removed `.lake/build`, executed `lake build`, directly checked each of 42 project module sources plus `MaximumModulus.lean`, checked `CheckAxioms.lean`, then ran `lake env leanchecker --verbose MaximumModulus.<Module>` sequentially for every project module. Full individual command arguments must be read from the retained JSON records rather than inferred as a fresh replay of dependency modules.

The frozen target workflow ran `lake build +<module>`, `lake env lean <actual-source>`, and `lake env lean <generated-audit>` for each target. Exact commands, logs, hashes, statuses, and timings for all targets are in [workflow-run-01/result.json](workflow-run-01/result.json). Static manifest requirements are kept distinct from the script's `semantic_verdict: not_determined`; the semantic verdict in this report comes from the independent correspondence and bridge checks plus reviewed unconditional proof chain.

The read-only post-comparison source/config/dependency/export review is recorded at `2026-10-10T19:40:48.942449+00:00` in [post-comparator-stability.json](../evidence/post-comparator-stability.json). No proof source, lockfile, installed toolchain, or dependency checkout was modified by that review. The former interim report is retained as [report-draft.md](report-draft.md).

## Findings, limits, and reproducible artifacts

No confirmed mathematical defect, missing original-statement obligation, or unproved production premise was found. The full requested theorem, its actual-set finiteness, and its implication for the original all-radii question are proved and checked. The ordinary module replay's relative-import scope is explicit; the configured comparator additionally accepted the exported final proof closure with the recorded independent checkers. Unused library declarations and the optional stronger locally finite exceptional-radius theorem/sharpness examples are outside the verified claim.

The one source-packaging difference is the intentionally snapshot-specific `.gitignore`. The exact difference, both hashes, verifier confirmation, and independent production hash review are retained; it does not affect the theorem or build configuration. The comparator's Linux-sandbox-disabled warning is retained verbatim and explained by the tested native OS replacement, with the full actual wrapper command and controls. Earlier interrupted replay and isolation diagnostics are retained, and are excluded from successful-check counts.

All configured checks completed. The final proof uses only the three standard foundations reported above, with no extra custom mathematical axiom or computational bypass. This local result does not infer award approval, payment, merge permission, publication status, or an identification between bibliographic, JSP, and Erdős numbering systems.

The reproducible evidence includes the frozen source snapshot and lockfile; independently written challenge and bridges; exact manifest/config and their hashes; pinned workflow downloads; complete command/output logs; all target axiom reports; actual tool/dependency hashes; native isolation profile and probes; both exported proof artifacts and their verified hashes; the original clean verification logs; and post-run stability records. This run remains local and does not publish, submit, merge, or upload any artifact.

A separate read-only [external-check evidence review](../evidence/external-check-review.md) rechecked the literal challenge, export hashes, absence of the private goal axiom from the solution export, all eight target axiom reports, checker acceptance, and native isolation scope. It found no remaining discrepancy and did not edit proof sources or rerun checkers.

The durable local deliverables are preserved under `/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/verification/`: this report, complete auditor evidence and logs, raw exports, the pinned workflow, a verified `proof-snapshot.bundle`, and `archive-index.json` with hashes. The original temporary audit directory remains separate.
