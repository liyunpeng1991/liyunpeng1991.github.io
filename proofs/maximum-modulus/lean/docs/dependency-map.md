# Completed dependency map

The exact all-radii theorem is now proved. The original library audit below is retained
as historical evidence; its entries marked “remaining” describe that earlier stage.
The final proof uses the following library primitives and project constructions.

| Existing mathlib primitives | Composite lemmas proved in this project |
| --- | --- |
| Analytic order, roots, inverse-function theorem | Local valence and genuine inverse-root physical pair families |
| Meromorphic logarithmic-derivative order | Simple pole charts and the actual spherical logarithmic derivative |
| Isolated zeros, finite roots of unity | Stable product/physical collisions and duplicate-safe actual counts |
| Proper/closed maps, compactness | Finite actual fibers, full finite target covers, bounded omitted-value survivors |
| Open mapping and local inverses | Total-image graph regularity and nonconstant actual product germs |
| Connectedness and closure localization | Full selected high-count branches, including omitted and infinite values |
| Second countability and local finiteness | Actual countable singular targets and exceptional square radii |
| Maximum modulus, real derivatives, absolute continuity | Actual stationarity, positive derivative radius selection, cofinal finite bounds |
| Compact-factor closed projection | High-count closure emptiness from its proved open projection |

No analytic normalization, irreducible component degree, or local product-polynomial
construction is assumed. `AllRadii.lean` supplies the requested theorem through the
proved high-count-locus route. See `final-proof-review.md` for its hypothesis audit.

---

# Dependency map and pinned mathlib audit

The local source audit used mathlib commit `81d17696471311f5e3e2f034236df7a781449f7e`, whose `lean-toolchain` is `leanprover/lean4:v4.35.0-rc4`. The checkout is `lean/.lake/packages/mathlib`. Paths below are relative to that checkout. Searches cover the entire `Mathlib` tree where stated; identified files were also read directly. The reproducible search commands and their actual output are preserved in `logs/mathlib-audit.log`.

**Status distinction:** an existing library primitive is a proved mathlib declaration. A required composite lemma still needs a Lean proof in this project. The absence findings below mean no matching public API was found in the pinned source; they are not mathematical assertions of impossibility. This document itself supplies no axioms and no proof of the final theorem.

## Existing primitives and the work they support

| Mathematical task | Existing source and declaration | Remaining composite work |
| --- | --- | --- |
| Entire functions are analytic | `Analysis/Complex/CauchyIntegral.lean`: `Differentiable.analyticAt`, `DifferentiableOn.analyticAt` | Apply to the actual function and its reflected/inverted compositions. |
| Isolated zeros and identity theorem | `Analysis/Analytic/IsolatedZeros.lean`: `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, `AnalyticOnNhd.eq_of_frequently_eq` | Finiteness of the specific maximum-point set requires a reflection identity plus exclusion of a circle of constant modulus. |
| Order and local analytic factor | `Analysis/Analytic/Order.lean`: `analyticOrderAt`, `analyticOrderNatAt`, `AnalyticAt.analyticOrderAt_eq_natCast`, `AnalyticAt.analyticOrderAt_ne_top`, `AnalyticAt.analyticOrderAt_deriv_add_one`, `analyticOrderAt_mul`, `AnalyticAt.analyticOrderAt_comp` | Obtain `f=z^m g` and the first-gap order `k`; construct the removable value of `q` at zero and prove its exact local order. |
| Local logarithms | `Analysis/SpecialFunctions/Complex/Analytic.lean`: `analyticAt_clog`; `Analysis/SpecialFunctions/Complex/LogDeriv.lean`: `Complex.hasDerivAt_log`, `Complex.differentiableAt_log` | Normalize a nonvanishing factor by its central value so its ratio is near `1` and in the principal-log slit plane. |
| Local analytic roots | `Analysis/SpecialFunctions/Pow/Complex.lean`: `Complex.cpow_nat_inv_pow`; `Analysis/SpecialFunctions/Pow/Deriv.lean`: `Complex.hasStrictDerivAt_cpow_const`; `Analysis/Complex/BranchLogRoot.lean`: `Complex.exists_continuousOn_pow_eq` | A generic local analytic root can be constructed using normalized factors and `analyticAt_clog`; the global branch theorem only asserts continuity. |
| Local inverse/injectivity | `Analysis/Calculus/InverseFunctionTheorem/Analytic.lean`: `AnalyticAt.analyticAt_localInverse`; `Analysis/Calculus/InverseFunctionTheorem/Deriv.lean`: `HasStrictDerivAt.localInverse`, `HasStrictDerivAt.map_nhds_eq` | Construct an injective power coordinate `A-c=τ^k` on one common neighborhood. This normal-form statement is not already the local-valence theorem. |
| At most `k` roots of a `k`th power | `Algebra/Polynomial/Roots.lean`: `Polynomial.mem_nthRoots`, `Polynomial.card_nthRoots`, `Polynomial.mem_nthRootsFinset`, `Polynomial.nthRootsFinset_toSet` | Pull the finite root set back through the injective local coordinate and count distinct solutions. |
| Log-derivative arithmetic | `Analysis/Calculus/LogDeriv.lean`: `logDeriv`, `logDeriv_mul`, `logDeriv_comp`, `logDeriv_pow`, `logDeriv_eqOn_iff` | Define and handle `q=z*logDeriv f`, distinguishing actual point values from removable/pole values. |
| Meromorphicity and order | `Analysis/Meromorphic/Basic.lean`: `MeromorphicAt.logDeriv`, `MeromorphicOn.logDeriv`, `Meromorphic.logDeriv`; `Analysis/Meromorphic/Order.lean`: `MeromorphicAt.analyticAt`, `meromorphicOrderAt_eq_int_iff`, `tendsto_cobounded_of_meromorphicOrderAt_neg` | The manuscript views functions as maps into the Riemann sphere. mathlib's scalar-valued meromorphic API permits arbitrary pole-point values, so a continuous sphere-valued representation and its charts still need construction. |
| Codiscrete log-derivative arithmetic | `Analysis/Meromorphic/LogDeriv.lean`: `MeromorphicOn.logDeriv_mul_eventuallyEq`, `MeromorphicOn.logDeriv_prod_eventuallyEq`, `MeromorphicOn.logDeriv_zpow_eventuallyEq`, `MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq` | Useful for factorization arguments; these do not assert the argument principle or a contour root count. |
| Compact sets meet discrete zeros finitely | `Analysis/Analytic/Order.lean`: `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`; `Topology/DiscreteSubset.lean`: `IsCompact.finite_sdiff_of_mem_codiscreteWithin` | Apply to roots in the annuli controlling correspondence fibers. |
| Compactness/proper maps | `Topology/Maps/Proper/Basic.lean`: `IsProperMap`, `IsProperMap.isCompact_preimage`, `IsProperMap.isClosed_range`, `isProperMap_fst_of_compactSpace`, `IsProperMap.restrict` | Prove the annulus bounds and build the correspondence as a topological subspace. Properness alone does not imply an analytic image. |
| Local holomorphic power sums | `Analysis/Complex/CauchyIntegral.lean`: `DiffContOnCl.circleIntegral_eq_zero`, `DiffContOnCl.circleIntegral_sub_inv_smul`, `DifferentiableOn.circleIntegral_sub_inv_smul`; `Analysis/Calculus/ParametricIntervalIntegral.lean` provides differentiation under a fixed integral | Prove root multiplicities and the identity relating the contour integral of `z^n A'/(A-p)` to the root power sum; prove holomorphic dependence on `p`. No ready-made family version was found. |
| Newton coefficient recursion | `RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`: `MvPolynomial.mul_esymm_eq_sum`, `MvPolynomial.psum_eq_mul_esymm_sub_sum` | Evaluate the symmetric identities on the finite root collection and transfer holomorphicity of power sums to coefficients. The algebraic identity is available; analytic root-family construction is not. |
| Maximum modulus principle | `Analysis/Complex/AbsMax.lean`: `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`, `Complex.exists_mem_frontier_isMaxOn_norm`, `Complex.norm_le_of_forall_mem_frontier_norm_le`, `Complex.eq_const_of_exists_le` | Establish strict increase of the normalized maximum function; prove the constant-circle-modulus implication gives a monomial. |
| Liouville and behavior at infinity | `Analysis/Complex/Liouville.lean`: `Differentiable.exists_eq_const_of_bounded`, `Differentiable.eq_const_of_tendsto_cocompact`, `Differentiable.apply_eq_of_tendsto_cocompact` | Supports the simplified reciprocal-symmetry exclusion below. |
| Three-circle convexity | `Analysis/Complex/Hadamard.lean`: `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` | Apply the three-lines theorem to `w ↦ f(exp w)`, identify strip suprema with circle maxima, and take logarithms to obtain convexity of `x ↦ log M_f(exp x)`. A direct three-circle declaration was not found. |
| Convex slopes and continuity | `Analysis/Convex/Deriv.lean`: `ConvexOn.slope_le_deriv`, `ConvexOn.deriv_le_slope`, `ConvexOn.monotoneOn_rightDeriv`; `Analysis/Convex/Continuous.lean`: `ConvexOn.locallyLipschitz`, `ConvexOn.continuousOn` | Prove the actual normalized logarithmic maximum is strictly increasing and its derivative is positive at differentiability points. |
| Almost-everywhere differentiability | `Analysis/Calculus/Monotone.lean`: `Monotone.ae_differentiableAt`; `Analysis/Calculus/Rademacher.lean`: `LipschitzWith.ae_differentiableAt`, `LipschitzOnWith.ae_differentiableWithinAt_of_mem` | The monotonicity of the actual logarithmic maximum can supply AE differentiability directly; alternatively use local Lipschitz bounds. |
| Singular-set countability, once discreteness is proved | `Topology/Compactness/Lindelof.lean`: `IsLindelof.countable_of_isDiscrete` | Prove discreteness of singular points of the actual analytic image; that analytic-geometry fact is missing. |

## New analytic geometry required by the manuscript route

### Prerequisites now proved in this local project

After this library audit, `MaximumModulus/Finiteness.lean` proved global entire factorization
at zero and circle-finiteness from actual values. `MaximumModulus/LocalValence.lean` proved
analytic local roots and the finite local-valence bound using a power coordinate and a local
inverse. `MaximumModulus/SmallFibers.lean` proved the resulting small-coordinate and small-product
fiber bookkeeping under explicit valence inputs. These are new checked project proofs rather
than existing mathlib declarations. The all-radii uniform bound remains unproved.

The following are not replaced by the primitives above:

1. A local product polynomial for two inverse-root families, with holomorphic coefficients through branch collisions, and an exact zero-set description.
2. A reduced analytic-image curve constructed from those polynomials, including pure dimension one and local finiteness of branches/components.
3. Local disk parametrization/normalization of irreducible curve germs; connected regular locus of an irreducible curve; discreteness of the singular locus.
4. Generic degree for a proper finite holomorphic map to an irreducible image component, including the cardinal bound at points smooth in the **total** image and density of generic fibers.
5. The high-degree-component continuation theorem across `p=c`, using bounded surviving inverse pairs and the local product polynomial.
6. Extension of the product coordinate to a nonconstant holomorphic map on the normalization of that closure, so open mapping plus properness forces the projection onto all of `ℂ*`.
7. The exclusion of vertical image components for the specific logarithmic derivative, and the complete maximum-point-to-fiber correspondence.

The central unresolved assertion is the manuscript's generic-degree bound: every nonvertical irreducible image component has degree at most `k_A+k_B`. Its proof depends on items 1–6. Local valence and set-cardinality bookkeeping alone do not establish this assertion.

## What Jensen and canonical decomposition do—and do not—supply

`Analysis/Complex/JensenFormula.lean` proves `MeromorphicOn.circleAverage_log_norm`, `AnalyticOnNhd.circleAverage_log_norm`, and `AnalyticOnNhd.sum_divisor_le`. These are logarithmic circle-average identities and zero-count bounds for one function. They do not provide parameter-stable root counts or holomorphic power sums of moving roots.

`Analysis/Complex/CanonicalDecomposition.lean` proves `MeromorphicOn.exists_canonicalDecomp`, `MeromorphicOn.exists_ecanonicalDecomp`, and the `Complex.CanonicalDecomp`/`Complex.ECanonicalDecomp` structures. They extract divisors from a single meromorphic function on a disk. Their equalities are formulated on codiscrete sets. They are useful building blocks for a contour root-count proof, but neither is the manuscript's local product-polynomial theorem.

`Analysis/Meromorphic/FactorizedRational.lean` proves `MeromorphicOn.extract_zeros_poles` and related trailing-coefficient/log identities. Combined with a holomorphic logarithm of the zero-free factor and Cauchy's theorem, this suggests a direct derivation of the needed disk argument-principle identity. That derivation remains additional proof work.

## Search findings and similarly named results

The audit searched the complete `Mathlib` tree for case-insensitive variants of Rouché, argument principle, residue theorem, local valence, Puiseux, analytic curve, holomorphic normalization, generic degree, and proper holomorphic maps. It also searched for contour-integral/log-derivative combinations and root-count formulas. No public result providing these composite analytic-geometry prerequisites was found.

Two similarly named developments must not be mistaken for the missing results:

- `MeasureTheory/Constructions/Polish/Basic.lean` defines **descriptive-set-theoretic** analytic sets. Its source explicitly distinguishes them from the analytic subsets used in several-complex-variable geometry.
- `RingTheory/PowerSeries/WeierstrassPreparation.lean` proves `PowerSeries.exists_isWeierstrassFactorization` over complete local rings for formal power series. It does not directly give convergent complex analytic preparation or curve normalization. `Geometry/Manifold/Complex.lean` still lists the analytic local-ring/Weierstrass theory as future work.

`Analysis/Complex/RiemannMapping.lean` contains partial results toward the Riemann mapping theorem. Its module has no public section and describes the lemmas as private. In the pinned version it contains two construction steps, not an available argument principle.

## Route reductions that retain the exact conclusion

### Stop at the almost-everywhere bound

If `MaxPoints(f,r)` is finite for every `r>0` and its `ncard` is at most a fixed `B` for almost every positive radius, every interval `(R,R+1)` contains a good radius. This proves the requested arbitrarily-large-good-radius theorem. There is no need to formalize one-sided constancy of the count, a locally finite exceptional-radius set, or the sharpness examples.

### Replace the residue argument for reciprocal symmetry

Suppose `q(z)=q*(s₀/z)` on `ℂ*`. Define `H(z)=f(z)f*(s₀/z)`. It is holomorphic on `ℂ*`, and away from zeros,

```text
z H'(z)/H(z) = q(z) − q*(s₀/z) = 0.
```

Analytic continuation gives `H'=0` throughout `ℂ*`, so `H` is a nonzero constant. Thus `f` has no nonzero zeros. Factoring its zero at the origin makes `q` entire, while the reciprocal identity gives `q(z)→m` at infinity. `Differentiable.eq_const_of_tendsto_cocompact` then makes `q=m`, and `g'=0` yields a monomial. This avoids rational functions on the sphere and the residue theorem. The argument must still be fully proved; it is not an assumption.

### Replace compact slope bounds by countability

Once the analytic image's singular locus is discrete, second countability makes it countable. Its first coordinates exclude only countably many positive radii. Together with AE differentiability and positivity of the normalized logarithmic-maximum slope, this is enough for the AE bound. It avoids the manuscript's compact target sets and two-sided uniform slope estimates. Proving image singular discreteness remains essential.

### Use a local power coordinate instead of a general Rouché theorem

Near each central zero, `A-p₀=τ^a` with `τ` injective supplies the local count for nearby values. Compactness excludes additional roots outside the chosen coordinate neighborhoods. This can establish the local constant root count without a general-purpose Rouché theorem. Holomorphic dependence of symmetric product coefficients still needs the contour identity, power-series descent, or equivalent argument.

These are reductions of prerequisites, not completed substitutes for the central degree/continuation argument.
