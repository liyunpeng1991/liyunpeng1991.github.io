module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Local valence of a complex analytic function

The finite order hypothesis expresses that the germ is not constant. The proof constructs a
local injective coordinate in which the function is a power; no argument principle or
normalization theorem is assumed.
-/

open Filter
open scoped Topology

namespace MaximumModulus

noncomputable section

/-- A positive power equation has finitely many solutions and at most its exponent many. -/
theorem power_fiber_finite_ncard_le (k : ℕ) (hk : 0 < k) (p : ℂ) :
    {z : ℂ | z ^ k = p}.Finite ∧ {z : ℂ | z ^ k = p}.ncard ≤ k := by
  classical
  have heq : {z : ℂ | z ^ k = p} = (Polynomial.nthRootsFinset k p : Set ℂ) := by
    ext z
    exact (Polynomial.mem_nthRootsFinset hk p).symm
  rw [heq]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset, Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots k p)

/-- A nonvanishing analytic germ has an analytic `k`th root near the base point. -/
theorem analytic_germ_root {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 ≠ 0 ∧ ∀ z, (h z) ^ k = g z := by
  let h : ℂ → ℂ := fun z => (g 0) ^ ((k : ℂ)⁻¹) * (g z / g 0) ^ ((k : ℂ)⁻¹)
  have hratio : AnalyticAt ℂ (fun z => g z / g 0) 0 := hg.div_const
  have hratio0 : g 0 / g 0 ∈ Complex.slitPlane := by
    simp [div_self hg0]
  have hh : AnalyticAt ℂ h 0 :=
    analyticAt_const.mul (hratio.cpow analyticAt_const hratio0)
  have hh0 : h 0 ≠ 0 := by
    dsimp [h]
    simp only [div_self hg0, Complex.one_cpow, mul_one]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hg0)
  refine ⟨h, hh, hh0, ?_⟩
  intro z
  dsimp [h]
  rw [mul_pow, Complex.cpow_nat_inv_pow _ hk.ne', Complex.cpow_nat_inv_pow _ hk.ne']
  exact mul_div_cancel₀ (g z) hg0

/-- Finite fibers in a power coordinate with a local left inverse. -/
theorem local_power_coordinate_valence {A τ ψ : ℂ → ℂ} {k : ℕ} (hk : 0 < k)
    (hpow : ∀ᶠ z in 𝓝 (0 : ℂ), A z - A 0 = (τ z) ^ k)
    (hleft : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (τ z) = z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : ℂ,
      {z : ℂ | ‖z‖ < ε ∧ A z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ A z = p}.ncard ≤ k := by
  obtain ⟨ε, hε, hcoord⟩ := Metric.eventually_nhds_iff.mp (hpow.and hleft)
  refine ⟨ε, hε, ?_⟩
  intro p
  let s : Set ℂ := {z | ‖z‖ < ε ∧ A z = p}
  let t : Set ℂ := {u | u ^ k = p - A 0}
  have hmaps : Set.MapsTo τ s t := by
    intro z hz
    have hc := hcoord (by simpa only [dist_zero_right] using hz.1)
    dsimp [t]
    rw [← hc.1, hz.2]
  have hinj : Set.InjOn τ s := by
    intro z hz w hw hzw
    have hcz := hcoord (by simpa only [dist_zero_right] using hz.1)
    have hcw := hcoord (by simpa only [dist_zero_right] using hw.1)
    rw [← hcz.2, ← hcw.2, hzw]
  obtain ⟨ht, htcard⟩ := power_fiber_finite_ncard_le k hk (p - A 0)
  exact ⟨Set.Finite.of_injOn hmaps hinj ht,
    (Set.ncard_le_ncard_of_injOn τ hmaps hinj ht).trans htcard⟩

/-- A nonconstant analytic germ has bounded local valence. The bound is its order of
vanishing after subtracting its value at the base point, and every fiber is proved finite. -/
theorem analytic_local_valence {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0)
    (hfinite : analyticOrderAt (fun z => A z - A 0) 0 ≠ ⊤) :
    0 < analyticOrderNatAt (fun z => A z - A 0) 0 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : ℂ,
      {z : ℂ | ‖z‖ < ε ∧ A z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ A z = p}.ncard ≤
        analyticOrderNatAt (fun z => A z - A 0) 0 := by
  have hF : AnalyticAt ℂ (fun z => A z - A 0) 0 := hA.sub analyticAt_const
  have hnonzero : analyticOrderAt (fun z => A z - A 0) 0 ≠ 0 :=
    hF.analyticOrderAt_ne_zero.mpr (sub_self _)
  have hk : 0 < analyticOrderNatAt (fun z => A z - A 0) 0 := by
    apply Nat.pos_of_ne_zero
    intro heq
    apply hnonzero
    rw [← Nat.cast_analyticOrderNatAt hfinite, heq]
    rfl
  obtain ⟨g, hg, hg0, hFg⟩ := hF.analyticOrderAt_ne_top.mp hfinite
  obtain ⟨h, hh, hh0, hroot⟩ :=
    analytic_germ_root hg hg0 (analyticOrderNatAt (fun z => A z - A 0) 0) hk
  let τ : ℂ → ℂ := fun z => z * h z
  have hd : HasStrictDerivAt τ (h 0) 0 := by
    convert! (hasStrictDerivAt_id (𝕜 := ℂ) (x := 0)).mul hh.hasStrictDerivAt using 1
    simp
  let ψ : ℂ → ℂ := hd.localInverse τ (h 0) 0 hh0
  have hleft : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (τ z) = z := hd.eventually_left_inverse hh0
  have hpow : ∀ᶠ z in 𝓝 (0 : ℂ),
      A z - A 0 = (τ z) ^ analyticOrderNatAt (fun z => A z - A 0) 0 := by
    filter_upwards [hFg] with z hz
    calc
      A z - A 0 = z ^ analyticOrderNatAt (fun z => A z - A 0) 0 * g z := by
        simpa only [sub_zero, smul_eq_mul] using hz
      _ = (τ z) ^ analyticOrderNatAt (fun z => A z - A 0) 0 := by
        dsimp [τ]
        rw [mul_pow, hroot]
  exact ⟨hk, local_power_coordinate_valence hk hpow hleft⟩

end

end MaximumModulus
