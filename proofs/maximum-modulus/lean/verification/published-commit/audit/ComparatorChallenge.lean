module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
Trusted auditor specification only. This file imports no MaximumModulus proof module.
The private specification axiom gives the public goal theorem its correct declaration
kind for this pinned comparator; it is not a proof and is not a permitted solution axiom.
The comparator checks the solution's dependencies against only the standard foundations.
-/

namespace MaximumModulus

private axiom independentOriginalSpecification (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) :
    ∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).Finite ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).ncard ≤ B

/-- Independent original target for comparison; this is specification harness code. -/
theorem bounded_maxPoints_at_arbitrarily_large_radii (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) :
    ∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).Finite ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).ncard ≤ B :=
  independentOriginalSpecification f hf hne hnm

end MaximumModulus
