module

public import MaximumModulus.HighCountGlobal
public import MaximumModulus.FiniteExceptionalSet
public import MaximumModulus.Reductions

@[expose] public section

noncomputable section

namespace MaximumModulus

/-- The requested all-radii theorem: a single uniform finite bound occurs
at arbitrarily large positive radii for every nonzero nonmonomial entire function. -/
theorem allRadiiStatement : AllRadiiStatement := by
  intro f hf hne hnm
  obtain ⟨m, g, hg, hg0, hfactor⟩ := entire_factor_at_zero hf hne
  let B := 2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0
  have hempty := regularLogDerivativeHighCount_empty hg hg0 hnm hfactor
  have hbound : PositiveProductFiberBound (normalizedLogDerivative m g) m B :=
    positiveProductFiberBound_of_regular_high_count_empty hg hg0 hnm hfactor hempty
  exact ⟨B, cofinalBound_of_positiveProductFiberBound hg hg0 hnm hfactor hbound⟩

/-- The final result with the original function-value definition and all
quantifiers and hypotheses spelled out explicitly. -/
theorem bounded_maxPoints_at_arbitrarily_large_radii (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) :
    ∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).Finite ∧
      ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).ncard ≤ B :=
  allRadiiStatement f hf hne hnm

/-- Both the counting formulation and the formulation treating an infinite
maximum set as infinite are ruled out for the original entire-function class. -/
theorem all_radii_growth_impossible (f : ℂ → ℂ)
    (hf : Entire f) (hne : f ≠ 0) (hnm : ¬IsMonomial f) :
    ¬CountTendsToInfinity f ∧ ¬MaximaGrowOnAllRadii f := by
  obtain ⟨B, hB⟩ := allRadiiStatement f hf hne hnm
  exact ⟨cofinalBound_not_tendsto hB, cofinalBound_not_growth hB⟩

end MaximumModulus
