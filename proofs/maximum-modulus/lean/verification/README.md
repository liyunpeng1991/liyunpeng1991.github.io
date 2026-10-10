# Verification of published source A and historical audit evidence

The proof source is published in [`https://github.com/liyunpeng1991/liyunpeng1991.github.io`](https://github.com/liyunpeng1991/liyunpeng1991.github.io), branch `main`, under [`proofs/maximum-modulus/lean/`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/tree/main/proofs/maximum-modulus/lean). The exact newly checked input is source publication A, [`c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/tree/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/proofs/maximum-modulus/lean).

## Fresh exact-publication verification

[public-commit-report.md](public-commit-report.md) records the completed fresh run against exactly A: **verification passed**. The actual clean project verification, all 43 source checks and 42 project-module kernel replays, all eight target checks, and the exported-proof comparator with all five bundled additional kernels plus Lean default exited 0. All 126 audited production declarations and all eight targets report only `propext`, `Classical.choice`, and `Quot.sound`. The final state review found all 53 production file hashes, the preserved manuscript, exact HEAD, nine dependency revisions and trusted tools unchanged.

The full selected fresh command records, logs, theorem/axiom reports, source/dependency provenance, trusted harnesses and comparison results are under [published-commit/](published-commit/). The native macOS sandbox and its controls remained active; the report explains the comparator's Linux-layer-disabled warning and the export-closure scope. The workflow automation itself leaves its semantic verdict undetermined; the report states a separate AI-assisted statement review. No independent human review, award acceptance, or whole-mathlib rebuild is implied.

[Public curation](published-commit-public-curation.json) records omissions: tool binaries, Git stores, caches, gigantic raw exports, redundant local source archive, and unnecessary workflow commit metadata containing unrelated email addresses. Export hashes and regeneration commands remain. [The retained local archive index](published-commit-local-archive-index.json) describes the completed local archive including omitted members; it is not a claim that every listed local member is distributed here.

This later evidence publication B is an update of records and READMEs. Source-A checks concern the exact proof input A, not a self-referential assertion that B has already been checked. The immutable revision and actual result must be read from the fresh report.

## Historical verification, kept separate

[prize-report.md](prize-report.md) is preserved verbatim as the completed historical audit of temporary snapshot `8b731b51dcb0ed3d7e8c6463b6266c35d8099c85`. The associated retained files include:

- Original clean-build, direct source-check, integrity and 42 sequential project-module replay logs and command records under [evidence/original-clean-verification](evidence/original-clean-verification/).
- The actual eight-target sandboxed workflow sources/results/commands under [audit/workflow-run-01](audit/workflow-run-01/), with [complete target axioms](evidence/target-axioms-complete.txt).
- Independent [literal statement bridges](audit/OriginalProblem.lean), the separate [expected-goal challenge](audit/ComparatorChallenge.lean), and [comparator configuration](audit/comparator.json).
- The actual [comparison log](logs/comparator-paranoid-01.log), native sandbox profile/probes, resource records, source/dependency/tool provenance, post-run stability, and [read-only external review](evidence/external-check-review.md).
- The pinned public verification workflow and sources under `workflow/`.

Those historical target reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The comparator challenge's private specification axiom expresses the expected goal only; it is not a production proof dependency or a permitted production axiom. Auditor inputs remain here rather than being installed as production modules under `MaximumModulus/`.

The original comparator log retains its Linux-layer-disabled warning. That execution used the documented native macOS sandbox wrapper and probes; no Lean kernel check was disabled. Ordinary module replay was relative to pinned imports; the comparator additionally accepted the exported final proof closure. Unused mathlib declarations were outside that claim. Any fresh-run differences must be read from the fresh report rather than inferred from these historical controls.

## Distribution and manifests

The raw historical challenge and solution exports (54,014,504 and 360,280,894 bytes) are omitted. Their actual hashes, generating commands and successful comparison outputs remain in [audit/exports/commands.json](audit/exports/commands.json) and the historical report. They can be regenerated with the recorded exact pins and auditor inputs; adapt original paths for a new run and record that adaptation.

The historical source bundle/full archive index and a redundant `project-checks/` copy are omitted; production source is supplied directly with [recorded source hashes](evidence/public-source-identity.json). The historical [omissions record](evidence/public-distribution-omissions.json) describes the initial selection.

Root `STAGE-MANIFEST.json`, `SHA256SUMS`, and `PUBLIC-CONTENT-REVIEW.json` describe only the frozen prepublication stage, including its former READMEs. They do not validate this later B extension or README overrides. Root `PUBLICATION-MANIFEST.json`, `PUBLICATION-SHA256SUMS`, and `PUBLICATION-CONTENT-REVIEW.json` give separate roles/hashes/review for the evidence-update payload. Actual recorded paths and timestamps are retained verbatim; they are technical provenance, not claims of execution at a different revision.
