# Independent statement correspondence

The original target is Hayman–Lingham Problem 2.16(b), read with the explicit
non-monomial restriction in Glücksam–Pardo-Simón Question 1.1(b) and
Pardo-Simón–Sixsmith's introduction. These are the user-specified arXiv
versions, respectively `1809.07200v2`, `2208.11154v2`, and `2607.09462v1`.
The question asks whether one non-monomial entire function can have its
number of exact maximum-modulus points tend to infinity on all radii.
Selected-radius unboundedness (the limsup variant, Herzog–Piranian 1968)
is a different proposition. No JSP or Erdős identifier is assigned to
this direct local-source verification.

The independent challenge defines `CircleMaximizers` directly from norms
and actual function values. It does not alias a production definition of
the maximum set, the entire-function class, monomials, or the intended
statement. It independently declares the complete quantifier pattern and
connects that declaration to the production theorem whose conclusion is
spelled out as a literal set expression.

| Requirement | Independent formulation | Production declaration | Correspondence |
| --- | --- | --- | --- |
| Exact circle maximizers | `IndependentOriginal.CircleMaximizers` | Literal set in `bounded_maxPoints_at_arbitrarily_large_radii` | Every circle point is compared by actual norms of function values. |
| Entire nonzero non-monomial class | `Differentiable ℂ f`, `f ≠ 0`, and negated explicit nonzero-monomial existential | Same hypotheses on the literal theorem | Nonzero constants are included among excluded monomials by exponent zero. |
| A bound uniform in radius threshold | `∃ B : ℕ, ∀ R : ℝ, ...` | Same ordered quantifiers | The bound can depend on f but cannot depend on R or r. |
| Arbitrarily large positive good radii | `0 < R → ∃ r, R < r ∧ ...` | Same ordered quantifiers | r is positive because R is positive. No selected finite interval or subsequence is assumed. |
| Explicit finite maximum sets | `.Finite` before the cardinality conclusion | Literal theorem plus `finite_maxPoints` | Infinite-set ncard cannot make a selected-radius conclusion trivial. |
| Cardinality bounded by B | `.ncard ≤ B` for the actual selected finite set | Literal theorem | Counts distinct actual maximum points, not multiplicity, stationary points, or approximate maxima. |
| Negative all-radii conclusion | `original_all_radii_growth_impossible` and `original_count_not_tendsto_atTop` | `all_radii_growth_impossible` | At the threshold B, the cofinal finite bounded radius contradicts either all-large-radii growth formulation. |

The infinity-aware challenge growth predicate permits an infinite maximum set
as a large-cardinality case. Its negation is proved using explicit finiteness
at the supplied radius. Separately, every positive-circle maximum set is
proved finite for the original function class. Thus the ordinary natural
count has the intended interpretation and the filter formulation cannot
exploit infinite-set `ncard`.

These are mathematical correspondence findings. They do not assert that the
challenge source, source snapshot, or audit script has been executed yet.
The final report must cite the actual snapshot and execution results.
