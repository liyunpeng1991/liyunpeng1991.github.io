# Read-only review of final comparison evidence

Reviewed `audit/comparator.json`, both independent auditor sources, the actual
export commands/artifacts, `workflow-run-01/result.json`, complete target axiom
outputs, the comparator command/log, and the native isolation profile/probe.
No proof, build, or checker was rerun for this review.

**Statement and specification.** `OriginalProblem.lean` independently spells out
the actual circle maximizers, entire/nonzero/non-monomial hypotheses, and the
ordered quantifiers `∃ B, ∀ R > 0, ∃ r > R`. Its conclusion includes separate
finiteness and bounded cardinality. The production theorem and
`ComparatorChallenge.lean` have the same literal hypotheses and conclusion.
The four actual independent bridge checks support the original all-radii
implication and positive-circle finiteness. No selected-radii substitution or
infinite-`ncard` loophole was found.

**Private challenge axiom.** The comparator challenge imports only the displayed
mathlib primitives and uses a private goal-specification axiom to give its
same-named goal declaration theorem kind. It is trusted specification code,
not a proved solution. The configuration permits only `propext`,
`Classical.choice`, and `Quot.sound` in the solution. The production and bridge
axiom outputs contain exactly these three. A read-only scan found the private
specification name in the challenge export and no occurrence in the solution
export. The solution was exported separately from `MaximumModulus.AllRadii`;
the production source does not import either auditor module.

**Executed scope.** The manifest result records exit 0, eight checked targets,
and `mechanical_status: standard_axioms_only`. The configured comparator
selects exactly the literal final theorem and no substituted definitions.
`comparator-paranoid-01.json` records exit 0; its log explicitly accepts the
solution with Lean paranoid, lean4lean, nanoda, con-leche, con-ron, and Lean
default. The five additional modes include Lean paranoid; they must not all be
described as distinct independent implementations. Although the static config
has `enable_nanoda: false`, the actual `--paranoid` run did execute nanoda, as
its retained log shows. lean4lean reports 52,015 declarations; con-leche and
con-ron each report 52,018 with `--verified`. This is exported final-proof-closure
comparison, not a claim to recompile or independently check every unused
mathlib declaration.

**Export provenance.** Independent read-only SHA-256 observations match the
recorded export commands and post-run stability evidence:

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `challenge.ndjson` | 54,014,504 | `ac2fe5af1de529ac3607406107429058256542d824ac15bf4590dba2bdde0360` |
| `solution.ndjson` | 360,280,894 | `dfc65218ba9d699deaa8ed3191dd66f0a076d528fc36752b2217a13225f0ffd0` |

The freshly observed challenge/config/bridge hashes also match their retained
records. Both export command records have exit 0 and name their respective
modules explicitly.

**Isolation qualification.** The actual command includes
`--inadvisably-no-sandbox`, and the log retains
`WARNING: Sandbox disabled, this run is not trustworthy.` The comparator's
internal sandbox therefore was disabled. The complete command was nevertheless
launched through `/usr/bin/sandbox-exec -f audit/isolation.sb`, with a sanitized
environment. The retained probe records denial of its tested outside reads,
writes, and networking while the exact pinned Lean binary executed successfully.
The profile restricts named data paths, writes outside the audit run, and all
networking; it is a native macOS restriction, not a Linux container or a claim
of exhaustive adversarial sandbox certification. CPU/file limits, sampled
descendant RSS, and wall limits are recorded; no imposed address-space or new
stack limit is claimed. No Lean kernel check was disabled.

**Finding.** No mismatch in the final goal, permitted production axioms, export
provenance, or recorded acceptance was found. An obsolete pending-finalization
paragraph was reported to the root reviewer and was removed from the current
`audit/report.md`; the earlier draft remains preserved separately. The final
result is local verification evidence, not official prize approval or payment.
