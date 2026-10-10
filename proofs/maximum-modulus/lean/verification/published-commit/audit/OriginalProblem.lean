module

public import MaximumModulus.AllRadii

@[expose] public section

open Set Filter

namespace IndependentOriginal

/-- Defined afresh from the actual function values and the complete circle. -/
def CircleMaximizers (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}

/-- Independent literal spelling of the user-requested sufficient negative answer. -/
def IntendedStatement : Prop :=
  ∀ f : ℂ → ℂ,
    Differentiable ℂ f → f ≠ 0 →
    (¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) →
    ∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ,
      R < r ∧ (CircleMaximizers f r).Finite ∧ (CircleMaximizers f r).ncard ≤ B

/-- The explicit production theorem proves the independently written statement. -/
theorem original_problem_solved : IntendedStatement := by
  intro f hf hnonzero hnonmonomial
  simpa only [CircleMaximizers] using
    MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii f hf hnonzero hnonmonomial

/-- Growth formulation which treats an infinite maximum set as infinite. -/
def CardinalityGrowsOnAllRadii (f : ℂ → ℂ) : Prop :=
  ∀ B : ℕ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R < r →
    ¬(CircleMaximizers f r).Finite ∨ B < (CircleMaximizers f r).ncard

/-- The independent cofinal theorem contradicts growth on every sufficiently large radius. -/
theorem original_all_radii_growth_impossible (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hnonzero : f ≠ 0)
    (hnonmonomial : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) :
    ¬CardinalityGrowsOnAllRadii f := by
  obtain ⟨B, hB⟩ := original_problem_solved f hf hnonzero hnonmonomial
  intro hgrowth
  obtain ⟨R, hRpositive, hgR⟩ := hgrowth B
  obtain ⟨r, hRr, hfinite, hbound⟩ := hB R hRpositive
  rcases hgR r hRr with hinfinite | hlarge
  · exact hinfinite hfinite
  · exact (Nat.not_lt_of_ge hbound) hlarge

/-- Direct filter formulation of the original all-radii divergence question. -/
theorem original_count_not_tendsto_atTop (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hnonzero : f ≠ 0)
    (hnonmonomial : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) :
    ¬Tendsto (fun r : ℝ => (CircleMaximizers f r).ncard) atTop atTop := by
  obtain ⟨B, hB⟩ := original_problem_solved f hf hnonzero hnonmonomial
  intro hgrowth
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hgrowth.eventually_gt_atTop B)
  obtain ⟨r, hRr, _, hbound⟩ := hB (max R 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hr : R ≤ r := (le_max_left R 1).trans hRr.le
  exact (Nat.not_lt_of_ge hbound) (hR r hr)

/-- Every positive-circle maximum set is finite for the original function class. -/
theorem original_positive_circle_finiteness (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hnonzero : f ≠ 0)
    (hnonmonomial : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m)
    (r : ℝ) (hr : 0 < r) : (CircleMaximizers f r).Finite := by
  exact MaximumModulus.finite_maxPoints hf hnonzero hnonmonomial hr

end IndependentOriginal
