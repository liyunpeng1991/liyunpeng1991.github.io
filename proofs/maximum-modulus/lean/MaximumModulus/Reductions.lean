module

public import MaximumModulus.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Fully proved reductions. These results do not assert the manuscript's
almost-everywhere estimate: that estimate is an explicit input.
-/

open Set Filter MeasureTheory

namespace MaximumModulus

theorem cofinalBound_not_growth {f : ℂ → ℂ} {B : ℕ}
    (h : CofinalBound f B) : ¬MaximaGrowOnAllRadii f := by
  intro hg
  obtain ⟨R, hR, hgR⟩ := hg B
  obtain ⟨r, hRr, hf, hb⟩ := h R hR
  rcases hgR r hRr with hi | hi
  · exact hi hf
  · exact (Nat.not_lt_of_ge hb) hi

theorem cofinalBound_not_tendsto {f : ℂ → ℂ} {B : ℕ}
    (h : CofinalBound f B) : ¬CountTendsToInfinity f := by
  intro ht
  obtain ⟨R, hR⟩ := eventually_atTop.1 (ht.eventually_gt_atTop B)
  obtain ⟨r, hRr, _, hb⟩ := h (max R 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  exact (Nat.not_lt_of_ge hb) (hR r (le_trans (le_max_left _ _) hRr.le))

/-- An a.e. bound includes finiteness explicitly and yields arbitrarily large good radii. -/
theorem cofinalBound_of_ae {f : ℂ → ℂ} {B : ℕ}
    (h : ∀ᵐ r : ℝ ∂volume, 0 < r → GoodRadius f B r) : CofinalBound f B := by
  intro R hR
  have hvol : volume (Ioo R (R + 1)) ≠ 0 := by simp
  obtain ⟨r, hr, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae h)
  exact ⟨r, hr.1, hgood (hR.trans hr.1)⟩

/-- The simpler exceptional-set route needs only finiteness on each positive interval. -/
theorem cofinalBound_of_locallyFinite_exceptions {f : ℂ → ℂ} {B : ℕ}
    {E : Set ℝ}
    (hE : ∀ R : ℝ, 0 < R → (E ∩ Ioo R (R + 1)).Finite)
    (hgood : ∀ r : ℝ, 0 < r → r ∉ E → GoodRadius f B r) : CofinalBound f B := by
  intro R hR
  obtain ⟨r, hr, hnot⟩ := (Ioo_infinite (by linarith : R < R + 1)).exists_notMem_finite
    (hE R hR)
  exact ⟨r, hr.1, hgood r (hR.trans hr.1) (fun he => hnot ⟨he, hr⟩)⟩

/-- This implication proves that the requested theorem really rules out all-radii growth. -/
theorem allRadiiStatement_implies_negative (h : AllRadiiStatement) :
    ∀ f : ℂ → ℂ, Entire f → f ≠ 0 → ¬IsMonomial f → ¬MaximaGrowOnAllRadii f := by
  intro f hf hn hm
  obtain ⟨B, hb⟩ := h f hf hn hm
  exact cofinalBound_not_growth hb

end MaximumModulus
