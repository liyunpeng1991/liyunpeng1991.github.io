# Final source review

Reviewed the final composition in `MaximumModulus/AllRadii.lean`,
`MaximumModulus/HighCountGlobal.lean`, and the actual omitted-value construction
in `MaximumModulus/OmittedTargetCover.lean`, tracing their counting, local-cover,
continuation, exceptional-set, and radius-selection inputs. The requested source
scope is recorded in `sources.md`; the manuscript's properness, generic-degree,
and omitted-value arguments were reread during this review.

**Finding:** no extra mathematical premise, circular continuation argument,
weakened conclusion, or infinite-set cardinality loophole was found in this
composition. This is a source review, separate from the executed build, axiom,
and kernel-replay logs. The reviewer previously authored the infinity modules;
the final composition and omitted-value construction were reviewed separately
from their authors, but this is not an independent rederivation of every lemma.

## Exact statement

`bounded_maxPoints_at_arbitrarily_large_radii` uses `Differentiable ℂ f`, `f ≠ 0`,
and exclusion of every representation `f z = c * z ^ m` with `c ≠ 0` and
`m : ℕ`, including nonzero constants. Its maximum-point set is defined directly
by the original function values on the circle. The order of quantifiers is
`∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧ ...`.
The conclusion asserts the set is finite separately from its `ncard ≤ B` bound.
No growth assumption, prescribed radius subsequence, or assumed geometric
fiber estimate appears in this theorem.

`all_radii_growth_impossible` explicitly deduces both failure of natural-valued
count divergence and failure of the formulation treating an infinite maximum
set as infinite. The radius supplied after any threshold has a finite maximum
set and count at most the same fixed `B`.

## Global argument and continuation

- `HighCountGlobal.lean` covers every value of `OnePoint ℂ`: infinity, the finite
  omitted value `m`, and every other finite value. The possible zero product is
  excluded for the whole closure using the actual uniform small-product bound.
- Properness and constructed inverse-root charts enumerate complete physical
  fibers away from the omitted value. Physical image cardinalities handle
  duplicate chart indices; central collisions cannot create additional physical
  pairs in a persistent class. Regularity refers to the **entire** actual image
  germ, so intersecting singular branches are not mistaken for regular targets.
- At the omitted value, `BoundaryCharts.lean` constructs only a finite containing
  family from a bounded surviving actual pair. It does not assert that all
  escaping pairs are captured or that the omitted correspondence is proper.
  `OmittedTargetCover.lean` retains the family with central product `s₀`, using
  actual continuity to exclude the other central products.
- The interior analytic subbranches used in omitted-value continuation come
  from `HighCountInterior.lean`, whose finite proper-map construction and local
  selected-count argument do not invoke omitted-value continuation, global
  emptiness, or the final all-radii theorem. `BranchContinuation.lean` then
  derives full-branch membership from closedness, the actual finite branch
  cover, punctured-branch connectedness, and analytic subbranch containment.
- Every selected product germ is proved nonconstant by exclusion of actual
  local reciprocal symmetry. At infinity, simple-pole reciprocal charts and a
  nearby regular parameter supply the same exclusion. Open local product
  projections are consequently conclusions, not assumptions of the final
  global theorem.
- Compactness of `OnePoint ℂ` makes projection of the closed high-count closure
  closed. Its proved open projection is incompatible with avoiding a nonempty
  small-product cylinder in the connected complex plane. Thus the actual
  regular high-count locus is empty.

## Cardinality and radii

`FiniteExceptionalSet.lean` constructs the exceptional set from actual finite
target-image points whose entire image germ is not a single analytic graph.
Each constructed chart neighborhood contains at most its central exceptional
point, proving local finiteness and hence countability. Positive real squaring
is injective, so only countably many positive radii are excluded.

For an image target off these radii, the empty high-count locus supplies the
bound on an explicitly finite actual fiber. A target outside the image has an
empty fiber, with finiteness proved directly. The spherical and ordinary
logarithmic-derivative fibers are proved equal away from `m`.

The maximum-envelope argument selects in every positive interval a radius off
the countable exceptional set at which the actual squared maximum of the
nonconstant factor has a positive derivative. Actual stationarity places all
maximum points in one common fiber at a real value strictly greater than `m`.
An injection into that explicitly finite fiber proves both finiteness and the
maximum-point count bound. This completes the quantified original conclusion.

## Differences from the manuscript

The formalization proves the requested cofinal finite bound using the closure
of the actual regular high-count locus. It avoids global irreducible-component
selection, normalization, and gluing a global generic degree. The local finite
root families and physical collision counts supply what this route needs.
It does not claim the manuscript's stronger locally finite exceptional-radius
theorem, sharpness examples, or a complete formalization of every manuscript
statement. The manuscript was not revised.

The review's direct placeholder scan found only ordinary words in comments,
not proof placeholders or custom axiom declarations. The manuscript SHA-256
remained `bc951c3ffa7d3579b2f39a0949e38db27338ac32ac050e3f5359d4452573a7b1`.
The final verification report is responsible for the executed clean-build,
target, axiom, kernel, and prize-workflow status.
