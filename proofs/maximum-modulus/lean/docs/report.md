# Complete all-radii formalization

The unconditional exact theorem is proved in `MaximumModulus/AllRadii.lean:26` as
`MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii`. It uses precisely a
nonzero entire function which is not a nonzero constant times a natural power of z.
It proves a uniform bound B, chosen before R, and arbitrarily large radii with actual
finite maximum-point sets and cardinality at most B. The independent spelling exposes
the function-value definition directly, without a custom maximum-set abstraction.

`allRadiiStatement` proves the named proposition, and `all_radii_growth_impossible`
explicitly rules out both ordinary ncard divergence and the formulation treating an
infinite maximum set as infinite. No theorem assumes its conclusion or a missing
analytic-geometry estimate.

## Proof chain

1. Factor f=z^m*g with g entire and g(0) nonzero. The normalized logarithmic derivative
   has finite positive local order k after subtracting m.
2. Local valence bounds actual small-product spherical correspondence fibers by 2k,
   including finiteness and the infinite common value.
3. Construct finite physical inverse-root families at every permitted finite target
   and genuine pole charts at infinity. Stable finite comparisons count distinct
   physical pairs and make the whole image locally a graph away from each center.
4. Select the branches with high actual fiber counts. At regular finite centers,
   a proved central-cardinality inequality includes any high-count central point.
5. Near the omitted common value, bounded surviving pairs give a finite raw cover.
   Localize closure, stabilize branches, and prove clopen branch membership from
   actual interior analytic subbranches. This continues selected branches across m.
6. Exclude constant nonzero product germs using the proved local reciprocal-symmetry
   contradiction. The closure has locally open product projection in all value cases.
   Compactness of the sphere makes the projection closed; its small-product exclusion
   forces the high-count locus to be empty.
7. Construct the actual locally finite finite singular target set, project its
   countable set to exceptional square radii, and bound every remaining relevant fiber.
8. Actual maximum stationarity and positive derivatives of the locally Lipschitz squared
   envelope supply good radii in every positive interval outside that countable set.

Every use of actual fiber cardinality in the final proof supplies finiteness.
`finite_maxPoints` also proves finiteness on every positive circle independently.

## Differences from the manuscript

The formalization replaces global normalization, irreducible component degree, and
local product-polynomial constructions with finite inverse-root image families and the
closure of the actual regular high-count locus. It expands the closure localization,
central distinct-pair comparison, omitted-value selection, and infinity coordinate.
The target theorem is unchanged. The radius bridge uses positive envelope derivatives
and a countable exceptional set, without claiming the optional stronger locally finite
exceptional-radius theorem or an independent almost-everywhere 2k maximum estimate.

The separate `continuation_expansion.tex` compiled successfully with the built-in LaTeX
compiler. The original manuscript is unchanged. Earlier partial reports remain in
`history/before-complete-continuation/`.

## Versions, sources, and verification

Lean 4.35.0-rc4, commit c29b6dda4f7c20e3eeaa717c4e565663c5cfa364; mathlib
81d17696471311f5e3e2f034236df7a781449f7e. Every transitive dependency is pinned in
`lake-manifest.json`. Build instructions are in the project README.

The original problem sources and all-radii/selected-radii distinction are recorded in
`sources.md`. The theorem, definitions, quantifiers and proof chain received independent
source reviews in `final-proof-review.md` and `continuation-formal-review.md`.

Read `../logs/verification-summary.json` for executed clean build, per-source checks,
axiom reports, sequential project kernel replays, and source/dependency/manuscript hashes.
Read `../verification/prize-report.md` for the separate requested lean-verify workflow,
its frozen local snapshot, independent statement challenge, and actual external-checker
scope. These records are authoritative for completed checks; no pending check is a pass.

Nothing was published, pushed, forked remotely, or submitted. The verification Git commit
is a temporary local audit snapshot, not a published or submitted repository revision.
