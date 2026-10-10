**Overall verdict: Verification passed.**

The all-radii maximum-modulus question is fully resolved negatively by the Lean source at the exact public commit `c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9` of `liyunpeng1991/liyunpeng1991.github.io`. Fresh verification reproduced the unmodified project, checked the independently restated original problem, and rechecked its exported proof with all five bundled additional kernels plus Lean's default kernel. The only permitted proof axioms are `propext`, `Classical.choice`, and `Quot.sound`.

| Required question | Judgment | Decisive evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | **Yes** | Literal actual-value maximum set; entire, nonzero, nonmonomial hypotheses; one bound before all thresholds; explicit finiteness; independently checked negative implication. |
| Did the specified commit actually pass verification? | **Yes** | Fresh clean build, all 43 direct source checks, all 42 project-module kernel replays, all eight target checks, and fresh exported-proof comparator exited 0. |
| Does it fully solve the original problem? | **Yes** | Cofinal bounded cardinality contradicts divergence on every sufficiently large radius, with a separate infinity-aware bridge. No additional mathematical premise occurs in the final theorem. |
| Does it meet the Lean completeness requirements for this verification? | **Meets** | No production `sorry`, `admit`, `sorryAx`, custom placeholder axiom, or kernel bypass; 126 audited production declarations and all eight targets report only the three standard foundations. |

This is a direct public-source audit under the [pinned lean-verify skill](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/skills/lean-verify/SKILL.md). It is not an awards-PR acceptance audit. Awards base/head/catalog pins are **not applicable** to this run. JSP-000928 is a separate catalog identifier associated with the question; no Erdős problem number is substituted. This verdict establishes Lean proof verification, not awards eligibility, editorial acceptance, or payment. Internal semantic review was AI-assisted; it does not assert an independent human referee review.

## Pinned input and traceability

- Public repository: [liyunpeng1991/liyunpeng1991.github.io](https://github.com/liyunpeng1991/liyunpeng1991.github.io).
- Exact source commit A: [`c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/commit/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9); project root `proofs/maximum-modulus/lean`.
- Actual Git tree: `f65b9f1a4865840f9aba4b17f2b2cad9c08dbd43`; parent: `b7ac532823d25f92d7740f2141cc053a8dc2a850`.
- Retrieval: `2026-10-10T20:30:09.155339+00:00` (UTC). Fresh completed-state check: `2026-10-10T20:50:01.581437+00:00`. Local HEAD remained the exact selected public SHA. The initial fetched `origin/main` equaled this SHA and `merge-base --is-ancestor` exited 0; the shallow clone establishes membership at retrieval, without asserting deeper history or an unchanged live branch tip after later publication.
- No temporary or synthetic commit was substituted. [Public input](published-commit/evidence/public-input.json), [fetch argv/log records](published-commit/evidence/public-fetch-commands.json), and [raw Git metadata/membership](published-commit/evidence/public-commit-metadata.json) preserve the actual retrieval.
- All **53 production proof/config/script files**, including the 42 production modules, exactly match the previously verified source and the blobs in this public commit. Editorial README/docs changes and distribution `.gitignore` changes are outside that production baseline. No tracked precompiled Lean/native artifact was supplied. See [complete source hashes](published-commit/evidence/public-source-check.json).
- Preserved parent manuscript SHA256: `bc951c3ffa7d3579b2f39a0949e38db27338ac32ac050e3f5359d4452573a7b1`. It is still the original candidate-proof manuscript, not the revised paper and not an assumed lemma. Fresh checks rehashed it unchanged.
- The revised [paper source](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/papers/maximum-modulus-points-v2.tex) explains the cofinal result. This run's formal statement is the final Lean theorem, rather than optional stronger claims of the earlier manuscript.
- Workflow pin: `16877004910734cecca83cc5af0fec2f5a4125b3`. The retained `scripts/audit.py` was unchanged; SHA256 `5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07`. [Retained workflow files](published-commit/pinned-workflow/SKILL.md) include the routing, reproduction, statement-audit, automation, and reporting references.
- Fresh [targets.json](published-commit/audit/targets.json) SHA256: `cb3524161b84975ea9bde91f4e8948740fbb9cd126971ba3f5c28c1e2cf1f4c0`. It fixes this public repository, nested project root, source SHA, seven requirements, and eight targets.

## Original question and exact formal coverage

Hayman–Lingham [Problem 2.16(b), printed p.29, PDF p.30](https://arxiv.org/pdf/1809.07200v2#page=30), Glücksam–Pardo-Simón [Question 1.1](https://arxiv.org/html/2208.11154v2#S1), and Pardo-Simón–Sixsmith [introduction](https://arxiv.org/html/2607.09462v1#S1) ask whether a single nonmonomial entire function can have the number of its maximum-modulus points tend to infinity as the radius tends to infinity. Herzog–Piranian's 1968 positive selected-radii limsup result concerns a different quantifier. The present theorem permits unbounded counts along selected radii and refutes divergence on all sufficiently large radii.

The final declaration is [`MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii`, AllRadii.lean:26](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/proofs/maximum-modulus/lean/MaximumModulus/AllRadii.lean#L26):

```lean
theorem bounded_maxPoints_at_arbitrarily_large_radii (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) :
    ∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).Finite ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).ncard ≤ B
```

`Differentiable ℂ f` is complex differentiability at every point of ℂ. The nonmonomial exclusion includes exponent zero. The final theorem takes no properness, local-chart, valence, continuation, degree, envelope, or almost-everywhere bound assumption: the project proves those needed consequences internally. The natural bound `B` precedes every threshold `R`; `R > 0` and `r > R` give positive selected radii. The actual set is explicitly finite in the same conjunction as its cardinality bound. Moreover, [`finite_maxPoints`, Finiteness.lean:187](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/proofs/maximum-modulus/lean/MaximumModulus/Finiteness.lean#L187) proves finiteness on every positive circle for the stated class, so `Set.ncard` on infinite sets cannot make the conclusion trivial.

| Original obligation | Formal evidence | Coverage |
| --- | --- | --- |
| Actual function values on the entire circle | Literal set in final theorem; independent `CircleMaximizers` definition | Full |
| Every entire nonzero nonmonomial function | Literal hypotheses, independently restated without extra premises | Full |
| One finite natural bound for each function | `∃ B : ℕ` before `∀ R` | Full |
| Arbitrarily large good radii | `∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧ …` | Full |
| Finite set and true cardinality bound | Explicit `.Finite ∧ .ncard ≤ B`; all-positive-circle finiteness theorem | Full |
| Negative answer to all-radii growth | Production corollary and independent infinity-aware growth bridge | Full |
| Literal filter divergence formulation | Independent `¬Tendsto (fun r => …ncard) atTop atTop` bridge | Full |

The production negative implication is [`all_radii_growth_impossible`, AllRadii.lean:36](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/proofs/maximum-modulus/lean/MaximumModulus/AllRadii.lean#L36). The independent [OriginalProblem.lean](published-commit/audit/OriginalProblem.lean) defines maximizers afresh, applies the production theorem to that literal definition, and proves two separate negative implications. Its infinity-aware growth predicate says that for each `B`, eventually every radius has either an infinite maximum set or cardinality greater than `B`. The cofinal theorem provides a finite set of cardinality at most that same `B` beyond the alleged threshold, contradicting either disjunct.

The current verified scope is the cofinal conclusion. This report does not claim a sharp `2k` almost-everywhere bound, locally finite exceptional **radii**, or sharpness examples have been Lean-verified.

## Fresh execution and environment

All proof execution used the tested native macOS isolation runner. The checked working directory was always `/private/tmp/mm-lean-published-20261011/sources/site/proofs/maximum-modulus/lean`. Fetching and trusted preparation were read-only remote/local operations. Public source and pinned workflow were not patched.

| Item | Observed value and evidence |
| --- | --- |
| OS | macOS 15.5, build 24F74, Darwin 24.5.0, arm64; [observed provenance](published-commit/evidence/dependency-tool-provenance.json) |
| Lean | `leanprover/lean4:v4.35.0-rc4`, release commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`; actual version logs |
| Lake | `5.0.0-src+c29b6dd`; official pinned toolchain binary; no Elan in sanitized PATH |
| Dependencies | Nine exact lock revisions freshly checked, clean checkouts; lock SHA256 `cb333575666396aefa2ed281978edc586f0535a0079b76012f32db0f18052b38` |
| Dependency cache | APFS clone copies, no hardlinks, of prior pinned cache; source revisions freshly rechecked. Dependency cache provenance is historical and [reported separately](published-commit/historical-cache-tool-provenance). A fresh rebuild of all mathlib dependencies is not claimed. |
| Trusted binaries | Lean, Lake, leanchecker, leanchecker-paranoid, lean4lean, nanoda_bin, con-leche, con-ron, leanexport: all nine hashes freshly recorded and rechecked unchanged in [tool provenance](published-commit/evidence/dependency-tool-provenance.json) |
| Isolation | Native `sandbox-exec`, network and outside-data/write denial, sanitized environment. [Profile](published-commit/audit/isolation.sb), [runner](published-commit/audit/run_isolated.py), [successful control probe](published-commit/evidence/isolation-probe.json) |
| Resource limits | CPU 1200 s per process; per-file 2 GiB; monitored total descendant RSS 10 GiB with 1 s sampling; wall 1800 s; inherited stack 8,372,224 bytes. No address-space cap is claimed. |
| Clean project build | `sh scripts/verify.sh` removed project `.lake/build` and ran `lake build`: fresh build 3097 jobs, 38.691 s; all checks exited 0. |
| Direct source checks | 42 production modules plus umbrella `MaximumModulus.lean` freshly elaborated from source, 43 checks total. |
| Module kernel replays | All42 production modules passed sequential `lake env leanchecker --verbose MaximumModulus.<Module>` against pinned imported dependencies. This is project-module replay, not a replay of every mathlib module. |
| Production axiom audit | Actual `CheckAxioms.lean` output contains 126 expected declaration reports, all only standard foundations. [Raw output](published-commit/project-logs/axioms.log); [summary](published-commit/project-logs/verification-summary.json) |
| Fresh target automation | Preflight and prepare exited 0; target-run 26 commands exited 0; 8/8 targets standard_axioms_only; inputs_stable=true. The workflow explicitly leaves semantic_verdict=not_determined; this report makes the separate semantic judgment from the statement and coverage review. |
| Post-run state | HEAD exact A; all 53 production file hashes and parent manuscript unchanged; nine dependencies clean at their exact pins; nine tools unchanged; no tracked source change; only the two trusted auditor modules untracked. Generated logs are ignored by tracked parent `proofs/maximum-modulus/.gitignore` line 3. |

| Fresh phase | Exit | Elapsed | Peak sampled descendant RSS | Evidence |
| --- | --- | --- | --- | --- |
| Unmodified project verification | 0 | 673.397605 s | 7,883,554,816 bytes | [argv, environment, limits, result](published-commit/logs/project-clean-verification.json); [raw log](published-commit/logs/project-clean-verification.log) |
| Eight-target workflow | 0 | 134.033514 s | 3,662,053,376 bytes | [argv, environment, limits, result](published-commit/logs/workflow-target-run.json); [raw log](published-commit/logs/workflow-target-run.log) |
| Fresh exports | 0 | 37.758250 s | 4,141,416,448 bytes | [argv, environment, limits, result](published-commit/logs/comparator-exports.json); [raw log](published-commit/logs/comparator-exports.log) |
| Fresh paranoid comparator | 0 | 137.748479 s | 1,460,092,928 bytes | [argv, environment, limits, result](published-commit/logs/comparator-paranoid.json); [raw log](published-commit/logs/comparator-paranoid.log) |

The first isolation probe was **inconclusive for networking** because DNS resolution failed before a direct socket check. Its exit 1 and diagnostic are retained. Only the trusted probe was changed to connect to a literal IP address; the retry exited 0 with `EPERM` for both outside access and networking. No Lean source, comparator specification, or workflow script changed. See [initial diagnostic](published-commit/evidence/isolation-probe-01-dns-diagnostic.json), [retry result](published-commit/evidence/isolation-probe.json), and [explicit probe update hashes/reason](published-commit/evidence/preparation-updates.json).

Some read-only Git metadata commands emitted macOS `xcrun` cache-write denial diagnostics outside the permitted temporary directory; they still exited 0 and returned the exact SHA/status output retained in the logs. These diagnostics did not change source or dependency checks.

The unchanged project's summary script retains historical explanatory strings referring to `logs/kernel-replay.json` and `verification/prize-report.md`. Those strings are not fresh failed-attempt records or this report. The fresh 91 actual check records and wrapper logs establish this run's scope; historical cache/tool acquisition records are kept under an explicitly historical directory.

### Exact dependency revisions

| Package | Actual revision | Status |
| --- | --- | --- |
| mathlib | `81d17696471311f5e3e2f034236df7a781449f7e` | Clean; equals lock |
| plausible | `aef59637faa9e85fa2486acaaf906ce3f572af7c` | Clean; equals lock |
| LeanSearchClient | `234d9e074fbd6e911b920baf32db5291c3125be0` | Clean; equals lock |
| importGraph | `579f558774c4ac6840e715ba60dabf3030619349` | Clean; equals lock |
| proofwidgets | `d5ad4a0b79fa7f9818fe1380d05a3f6143823c09` | Clean; equals lock |
| aesop | `04879b1e1de744d5c9777c8cf63fa55a8f652e5e` | Clean; equals lock |
| Qq | `e7c4cdd2f1bf9df361ef7f621b4d6867012ab65e` | Clean; equals lock |
| batteries | `b71aaf60877e673fdb921f06f20987d12ee8a290` | Clean; equals lock |
| Cli | `82c11b9717083154aefc5fe8d4cba4bbf046298f` | Clean; equals lock |

## Eight target checks and axiom reports

| Fully qualified declaration | Role | Actual result | Evidence |
| --- | --- | --- | --- |
| `MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii` | literal-cofinal | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0000-2.log) |
| `MaximumModulus.allRadiiStatement` | cofinal-statement | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0001-2.log) |
| `MaximumModulus.all_radii_growth_impossible` | negative-all-radii | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0002-2.log) |
| `MaximumModulus.finite_maxPoints` | positive-finiteness | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0003-2.log) |
| `IndependentOriginal.original_problem_solved` | independent-cofinal | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0004-2.log) |
| `IndependentOriginal.original_all_radii_growth_impossible` | independent-negative | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0005-2.log) |
| `IndependentOriginal.original_count_not_tendsto_atTop` | independent-tendsto | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0006-2.log) |
| `IndependentOriginal.original_positive_circle_finiteness` | independent-finiteness | Passed; standard foundations only | [raw declaration and axioms](published-commit/audit/workflow-target-run/0007-2.log) |

Complete actual `#print axioms` lines for the eight targets:

```text
'MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaximumModulus.allRadiiStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaximumModulus.all_radii_growth_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaximumModulus.finite_maxPoints' depends on axioms: [propext, Classical.choice, Quot.sound]
'IndependentOriginal.original_problem_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
'IndependentOriginal.original_all_radii_growth_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
'IndependentOriginal.original_count_not_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound]
'IndependentOriginal.original_positive_circle_finiteness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The project-wide integrity scan and target axiom audit found no production placeholder or unproved custom axiom in the final dependency chain. The independent challenge harness has a **private specification axiom** so the pinned comparator can compare a theorem against a theorem of the same declaration kind. It imports trusted mathlib primitives only, states the literal original target, and is a separate challenge environment. That axiom is not a permitted solution axiom and is absent from the exported solution proof. The independent original-problem bridges themselves use no such specification axiom.

Trusted [ComparatorChallenge.lean](published-commit/audit/ComparatorChallenge.lean) SHA256 `b51e5b557b2c057251c00629b327ca5417ecf91bc6319464c3097eece0c634bf`; [OriginalProblem.lean](published-commit/audit/OriginalProblem.lean) SHA256 `4be4fb7093e9dd1176de51aed1b3a755507c14ea7ac60e236c7e122e3fc992e7`. Both are retained auditor additions, not production source mutations. The [comparator configuration](published-commit/audit/comparator.json) uses the one literal final theorem, `definition_names=[]`, and exactly the three standard permitted foundations. The manifest retains the original requirements and eight theorem targets, adapts the repository, nested root, public SHA and evidence paths to this run, and the retained harnesses were rebuilt freshly.

## Fresh exported-proof cross-check

Fresh [export commands](published-commit/audit/exports/commands.json) used the trusted pinned `leanexport` and the newly built public source. Both exports equal the earlier audit's raw exports byte-for-byte. This identity is a recorded comparison, **not a substitution of old execution**: every checker below was run freshly against the new exports.

| Export | Raw bytes | SHA256 | Identical to prior export |
| --- | --- | --- | --- |
| challenge | 54,014,504 | `ac2fe5af1de529ac3607406107429058256542d824ac15bf4590dba2bdde0360` | Yes |
| solution | 360,280,894 | `dfc65218ba9d699deaa8ed3191dd66f0a076d528fc36752b2217a13225f0ffd0` | Yes |

The fresh comparator accepted the declaration/type correspondence and solution dependencies, then all bundled additional kernels accepted: Lean paranoid, lean4lean, nanoda, con-leche, and con-ron. Lean default also accepted. Actual declaration counts were 52,015 for lean4lean and 52,018 for each of con-leche and con-ron; the latter two ran with `--verified`. The log ends `Your solution is okay!`. These counts concern the exported target dependency closure; they do not claim a whole-library audit. See [raw checker log](published-commit/logs/comparator-paranoid.log), [actual invocation/result](published-commit/logs/comparator-paranoid.json), and [post-run result/hash review](published-commit/evidence/completed-results-review.json).

The comparator's `--inadvisably-no-sandbox` flag disables its Linux-only inner sandbox and emits a warning. Native macOS isolation remained enforced by the outer tested `sandbox-exec` wrapper and inherited by descendants. This flag did not disable Lean kernel checks; `--paranoid` actually ran all five additional bundled kernels. The fresh outside-access/network controls and exact wrapper argv are retained, so no claim depends on an absent Linux sandbox.

## Reproduction and durable evidence

Each isolated execution’s argv, cwd, sanitized environment, limits, start UTC, elapsed time, exit code, and raw log are retained. The fresh [completed-results review](published-commit/evidence/completed-results-review.json), with the final [stability invocation](published-commit/logs/final-state-review-02.json), rehashed all workflow logs, targets, exports, source files, dependency Git checkouts, trusted tools, and the manuscript after checker completion. The [independent internal review](published-commit/evidence/public-verification-independent-review.md) separately inspects the original-source correspondence and actual fresh outputs.

To reproduce the production project, check out exact A, enter `proofs/maximum-modulus/lean`, use the exact toolchain and locked dependencies, then run `sh scripts/verify.sh`. The retained audited run's actual local path configuration and command order are:

```sh
# Checked cwd: /private/tmp/mm-lean-published-20261011/sources/site/proofs/maximum-modulus/lean
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py workflow-preflight python3 /private/tmp/mm-lean-verify-workflow-20261010/scripts/audit.py preflight /private/tmp/mm-lean-published-20261011/audit/targets.json --out /private/tmp/mm-lean-published-20261011/audit/workflow-preflight
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py workflow-prepare python3 /private/tmp/mm-lean-verify-workflow-20261010/scripts/audit.py prepare /private/tmp/mm-lean-published-20261011/audit/targets.json --out /private/tmp/mm-lean-published-20261011/audit/workflow-prepare
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py project-clean-verification sh scripts/verify.sh
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py workflow-target-run python3 /private/tmp/mm-lean-verify-workflow-20261010/scripts/audit.py run /private/tmp/mm-lean-published-20261011/audit/targets.json --out /private/tmp/mm-lean-published-20261011/audit/workflow-target-run --lake '/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64/bin/lake' --timeout 300
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py comparator-exports python3 /private/tmp/mm-lean-published-20261011/audit/export_proof.py
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py comparator-paranoid lake comparator --config /private/tmp/mm-lean-published-20261011/audit/comparator.json --challenge-from-export /private/tmp/mm-lean-published-20261011/audit/exports/challenge.ndjson --solution-from-export /private/tmp/mm-lean-published-20261011/audit/exports/solution.ndjson --paranoid --inadvisably-no-sandbox
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py completed-results-review python3 /private/tmp/mm-lean-published-20261011/audit/check_completed_results.py
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py final-state-review python3 /private/tmp/mm-lean-published-20261011/audit/check_completed_results.py
python3 /private/tmp/mm-lean-published-20261011/audit/run_isolated.py final-state-review-02 python3 /private/tmp/mm-lean-published-20261011/audit/check_completed_results.py
```

The actual wrapper JSON records preserve the ordered arguments and checked working directory. Preflight and prepare used no `--lake` override; target-run used the explicit trusted Lake path shown above. The runner/profile have this machine's trusted toolchain path and local temporary paths; relocation requires updating auditor path configuration while retaining pinned source, trusted specifications, and allowed foundations. The public source is reproduced from Git rather than from compiled submission artifacts.

The curated public bundle contains textual workflow/harness files, configs, provenance, hashes, actual argv/logs, and project-check outputs. The gigantic raw NDJSON exports are deliberately omitted from that public curated bundle; their exact hashes, sizes, and regeneration commands are retained. Compressed verified copies and a tracked-source archive are preserved in the local durable verification archive. No fresh check is represented solely by the earlier historical logs, and no original manuscript, current Lean production source, or remote repository was mutated by this verifier.

No unresolved mathematical obligation or outstanding configured check remains in this verified cofinal statement. Optional stronger results, award decisions, and independent human referee assessment are outside this verdict.
