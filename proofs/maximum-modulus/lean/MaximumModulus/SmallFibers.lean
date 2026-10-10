module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
The combinatorial part of manuscript Lemma 2.1.

The theorems below assume finite local valence bounds for `A` and `B`.
They do not establish those analytic bounds and do not prove the all-radii
maximum-modulus theorem. Every `ncard` estimate is accompanied by an
explicit finiteness proof.
-/

namespace MaximumModulus

variable {β : Type*}

/-- Ordered inverse pairs with prescribed product and common value. -/
def InversePairs (A B : ℂ → β) (s : ℂ) (p : β) : Set (ℂ × ℂ) :=
  {zw | zw.1 * zw.2 = s ∧ A zw.1 = p ∧ B zw.2 = p}

/-- The part of a fiber with at least one coordinate in the small disk. -/
def SmallInversePairs (A B : ℂ → β) (ε : ℝ) (s : ℂ) (p : β) : Set (ℂ × ℂ) :=
  {zw | zw ∈ InversePairs A B s p ∧ (‖zw.1‖ < ε ∨ ‖zw.2‖ < ε)}

/-- Small-coordinate inverse pairs are finite and bounded by the sum of
the two assumed local valence bounds. -/
theorem small_inverse_pairs_finite_ncard_le
    (A B : ℂ → β) (ε : ℝ) (s : ℂ) (p : β) (hs : s ≠ 0)
    (kA kB : ℕ)
    (hAfinite : ({z : ℂ | ‖z‖ < ε ∧ A z = p} : Set ℂ).Finite)
    (hBfinite : ({w : ℂ | ‖w‖ < ε ∧ B w = p} : Set ℂ).Finite)
    (hAcard : ({z : ℂ | ‖z‖ < ε ∧ A z = p} : Set ℂ).ncard ≤ kA)
    (hBcard : ({w : ℂ | ‖w‖ < ε ∧ B w = p} : Set ℂ).ncard ≤ kB) :
    (SmallInversePairs A B ε s p).Finite ∧
      (SmallInversePairs A B ε s p).ncard ≤ kA + kB := by
  let U : Set ℂ := {z | ‖z‖ < ε ∧ A z = p}
  let V : Set ℂ := {w | ‖w‖ < ε ∧ B w = p}
  let left : ℂ → ℂ × ℂ := fun z => (z, s / z)
  let right : ℂ → ℂ × ℂ := fun w => (s / w, w)
  have hUfinite : U.Finite := hAfinite
  have hVfinite : V.Finite := hBfinite
  have hcontainer : (left '' U ∪ right '' V).Finite :=
    (hUfinite.image left).union (hVfinite.image right)
  have hsubset : SmallInversePairs A B ε s p ⊆ left '' U ∪ right '' V := by
    rintro ⟨z, w⟩ ⟨⟨hprod, hAz, hBw⟩, hsmall⟩
    have hz : z ≠ 0 := by
      intro hz
      exact hs (by simpa [hz] using hprod.symm)
    have hw : w ≠ 0 := by
      intro hw
      exact hs (by simpa [hw] using hprod.symm)
    rcases hsmall with hzsmall | hwsmall
    · apply Set.mem_union_left
      refine ⟨z, ⟨hzsmall, hAz⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact (div_eq_iff hz).2 (by simpa [mul_comm] using hprod.symm)
    · apply Set.mem_union_right
      refine ⟨w, ⟨hwsmall, hBw⟩, ?_⟩
      apply Prod.ext
      · exact (div_eq_iff hw).2 hprod.symm
      · rfl
  refine ⟨hcontainer.subset hsubset, ?_⟩
  calc
    (SmallInversePairs A B ε s p).ncard ≤ (left '' U ∪ right '' V).ncard :=
      Set.ncard_le_ncard hsubset hcontainer
    _ ≤ (left '' U).ncard + (right '' V).ncard := Set.ncard_union_le _ _
    _ ≤ U.ncard + V.ncard :=
      Nat.add_le_add (Set.ncard_image_le hUfinite) (Set.ncard_image_le hVfinite)
    _ ≤ kA + kB := Nat.add_le_add hAcard hBcard

/-- A sufficiently small nonzero product forces one coordinate to be small. -/
theorem inverse_pairs_eq_small_of_norm_lt_sq
    (A B : ℂ → β) (ε : ℝ) (s : ℂ) (p : β)
    (hε : 0 < ε) (hsmall : ‖s‖ < ε ^ 2) :
    InversePairs A B s p = SmallInversePairs A B ε s p := by
  apply Set.Subset.antisymm
  · intro zw hzw
    refine ⟨hzw, ?_⟩
    by_contra hneither
    have hz : ε ≤ ‖zw.1‖ := le_of_not_gt (fun hz => hneither (Or.inl hz))
    have hw : ε ≤ ‖zw.2‖ := le_of_not_gt (fun hw => hneither (Or.inr hw))
    have hprod : ε * ε ≤ ‖zw.1‖ * ‖zw.2‖ :=
      mul_le_mul hz hw (le_of_lt hε) (norm_nonneg _)
    have heq : ‖zw.1‖ * ‖zw.2‖ = ‖s‖ := by
      rw [← norm_mul, hzw.1]
    exact (not_le_of_gt hsmall) (by simpa [pow_two, heq] using hprod)
  · intro zw hzw
    exact hzw.1

/-- The complete small-product fiber is finite, with an explicit bound,
under the two local valence hypotheses. -/
theorem inverse_pairs_finite_ncard_le_of_norm_lt_sq
    (A B : ℂ → β) (ε : ℝ) (s : ℂ) (p : β) (hs : s ≠ 0)
    (hε : 0 < ε) (hsmall : ‖s‖ < ε ^ 2) (kA kB : ℕ)
    (hAfinite : ({z : ℂ | ‖z‖ < ε ∧ A z = p} : Set ℂ).Finite)
    (hBfinite : ({w : ℂ | ‖w‖ < ε ∧ B w = p} : Set ℂ).Finite)
    (hAcard : ({z : ℂ | ‖z‖ < ε ∧ A z = p} : Set ℂ).ncard ≤ kA)
    (hBcard : ({w : ℂ | ‖w‖ < ε ∧ B w = p} : Set ℂ).ncard ≤ kB) :
    (InversePairs A B s p).Finite ∧ (InversePairs A B s p).ncard ≤ kA + kB := by
  rw [inverse_pairs_eq_small_of_norm_lt_sq A B ε s p hε hsmall]
  exact small_inverse_pairs_finite_ncard_le
    A B ε s p hs kA kB hAfinite hBfinite hAcard hBcard

end MaximumModulus
