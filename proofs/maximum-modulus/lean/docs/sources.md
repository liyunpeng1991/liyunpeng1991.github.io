# Original problem and source checks

Checked on 2026-10-11 against the three primary sources requested by the user. The manuscript is a candidate proof, not an assumed theorem. It was read at `/Users/gluon/Documents/ChatGPT/Maximum Modulus/maximum_modulus_points.tex` without modification.

## The exact question

For a nonzero entire function `f`, define the maximum-point set on a positive-radius circle by its actual values:

```text
MaxPoints(f,r) = {z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}.
```

A monomial `f(z)=c*z^m`, including nonzero constants (`m=0`), has every point of each circle as a maximum point. The intended question excludes this case. For a non-monomial entire function, finiteness on every positive-radius circle must be proved before interpreting a natural-valued cardinality as the number of maximum points.

| Source | Exact location and scope |
| --- | --- |
| [Hayman–Lingham, *Research Problems in Function Theory*, arXiv v2](https://arxiv.org/pdf/1809.07200v2#page=30) | Printed page 29, PDF page index 29, Problem 2.16: (a) asks whether `limsup ν(r) = ∞`; (b) asks whether `liminf ν(r) = ∞`. Update 2.16 attributes the affirmative answer to (a) to Herzog–Piranian and says (b) remains unknown. The wording of this item does not explicitly repeat the monomial exclusion, which the later sources make explicit. |
| [Glücksam–Pardo-Simón, Question 1.1](https://arxiv.org/html/2208.11154v2#S1) | The question explicitly concerns a non-monomial entire function. Part (a) is selected-radius unboundedness; part (b) asks whether the count tends to infinity on all radii. The introduction states that Herzog–Piranian constructed `ν(n)=n` for every positive integer `n`, but that the construction supplies no useful control between those radii. |
| [Pardo-Simón–Sixsmith, introduction](https://arxiv.org/html/2607.09462v1#S1) | Repeats the two distinct questions and states that the second remains open. Its affirmative theorem concerns unbounded selected-radius counts for a finite-order function in the Eremenko–Lyubich class `𝓑`. It supplies no all-radii divergence conclusion. |

The source versions carry arXiv dates 2018-09-21, 2023-09-26, and 2026-07-10 respectively. The source check concerns those specified versions; it does not infer a newer result from the manuscript.

## Why the required theorem answers part (b)

The requested statement is:

```text
∀ f : ℂ → ℂ,
  Entire(f) → Nonzero(f) → ¬IsMonomial(f) →
  ∃ B : ℕ, ∀ R : ℝ, 0 < R →
    ∃ r : ℝ, R < r ∧ (MaxPoints(f,r)).Finite ∧
      (MaxPoints(f,r)).ncard ≤ B.
```

All-radii divergence means that for each natural threshold `N`, there is a positive `R` such that every `r>R` has finite maximum-point set with cardinality at least `N`. Setting `N=B+1` contradicts the radius supplied by the required statement. Equivalently, its count cannot tend to `atTop` as `r` tends to `atTop`. Finiteness is included explicitly so that `Set.ncard`'s value on infinite sets cannot make the conclusion vacuous.

Part (a) is compatible with this conclusion: a fixed function can have unbounded counts on selected radii and retain a bounded count on arbitrarily large intervening radii.

`JSP-000928` is an award identifier mentioned in the task. Hayman–Lingham's `2.16(b)` is the bibliographic numbering used above. Erdős problem database numbers are another numbering system. No identification between these numbers is inferred here.

## Approximate maxima do not replace exact maxima

Glücksam–Pardo-Simón prove that, for one entire function and every fixed positive tolerance, the number of circle components where `|f(z)|` is within that tolerance of the maximum tends to infinity. Their introduction explicitly explains that the exact maximum may occur in only uniformly many of these arcs. This is why the formal maximum set uses comparisons of actual function values and does not use near-maximal arcs as a substitute.

## Manuscript proof route being checked

The manuscript claims an almost-everywhere bound `ν_f(r) ≤ 2k`, where `k` is the first positive coefficient exponent after factoring the order at zero. The route is:

1. Local valence at zero for `q(z)=z f'(z)/f(z)` and its reflection.
2. A proper finite correspondence over `(s,p)=(zw,q(z))`, away from `p=q(0)`.
3. Local product-polynomial equations for its analytic image.
4. Generic fiber degree on irreducible analytic-image components.
5. Continuation of a component with degree greater than `2k` across the omitted value.
6. Proper, nonconstant product projection forces such a component to meet small products, contradicting local valence.
7. Reciprocal-symmetry exclusion, and the correspondence between maxima and a single fiber at differentiability radii.
8. Almost-everywhere good radii yield arbitrarily large good radii.

The manuscript's locally finite exceptional-radius theorem and sharpness examples strengthen the requested conclusion. They are optional for this project. None of the unformalized steps listed here is imported as an axiom or used as an established Lean result.
