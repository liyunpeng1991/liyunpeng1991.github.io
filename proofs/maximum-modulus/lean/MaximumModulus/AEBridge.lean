module

public import MaximumModulus.Finiteness
public import MaximumModulus.Reductions

@[expose] public section

open MeasureTheory

namespace MaximumModulus

/-- The unresolved analytic estimate is recorded as a proposition, not an axiom. -/
def AlmostEverywhereBoundStatement : Prop :=
  ∀ f : ℂ → ℂ, Entire f → f ≠ 0 → ¬IsMonomial f →
    ∃ B : ℕ, ∀ᵐ r : ℝ ∂volume, 0 < r → (MaxPoints f r).ncard ≤ B

/-- Circle finiteness makes an a.e. `ncard` estimate an honest finite bound. -/
theorem cofinalBound_of_ae_ncard {f : ℂ → ℂ} (hf : Entire f) (hne : f ≠ 0)
    (hnm : ¬IsMonomial f) {B : ℕ}
    (hbound : ∀ᵐ r : ℝ ∂volume, 0 < r → (MaxPoints f r).ncard ≤ B) :
    CofinalBound f B := by
  apply cofinalBound_of_ae
  filter_upwards [hbound] with r hrbound
  intro hr
  exact ⟨finite_maxPoints hf hne hnm hr, hrbound hr⟩

/-- This bridge has an explicit unresolved premise and is not the final theorem. -/
theorem almostEverywhereStatement_implies_allRadiiStatement
    (hae : AlmostEverywhereBoundStatement) : AllRadiiStatement := by
  intro f hf hne hnm
  obtain ⟨B, hB⟩ := hae f hf hne hnm
  exact ⟨B, cofinalBound_of_ae_ncard hf hne hnm hB⟩

end MaximumModulus
