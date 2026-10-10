module

public import MaximumModulus.Definitions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
Analytic finiteness prerequisites for the maximum-point set. The reflection is
formed from actual values of the given function, rather than an auxiliary count.
-/

open Set Filter Metric
open scoped Topology ComplexConjugate

noncomputable section

namespace MaximumModulus

def reflection (f : ℂ → ℂ) : ℂ → ℂ := fun z => conj (f (conj z))

def reflectionProduct (f : ℂ → ℂ) (r : ℝ) : ℂ → ℂ :=
  fun z => f z * reflection f ((r : ℂ) ^ 2 / z)

theorem entire_reflection {f : ℂ → ℂ} (hf : Entire f) : Entire (reflection f) := by
  intro z
  convert! (hf (conj z)).star_star using 1
  simp

theorem analyticOnNhd_reflectionProduct {f : ℂ → ℂ} (hf : Entire f) (r : ℝ) :
    AnalyticOnNhd ℂ (reflectionProduct f r) ({0}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact ((hf z).mul ((entire_reflection hf ((r : ℂ) ^ 2 / z)).comp z
    ((differentiableAt_const ((r : ℂ) ^ 2)).div differentiableAt_id hz0))).differentiableWithinAt

theorem reflectionProduct_eq_sq_norm {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : ‖z‖ = r) :
    reflectionProduct f r z = (‖f z‖ : ℂ) ^ 2 := by
  have hz0 : z ≠ 0 := by
    intro h
    exact hr.ne' (by simpa [h] using hz.symm)
  have hmul : z * conj z = (r : ℂ) ^ 2 := by
    simpa [hz] using Complex.mul_conj' z
  have hdiv : (r : ℂ) ^ 2 / z = conj z := by
    rw [div_eq_iff hz0, ← hmul]
    ring
  simpa [reflectionProduct, reflection, hdiv] using Complex.mul_conj' (f z)

theorem punctured_plane_preconnected : IsPreconnected ({0}ᶜ : Set ℂ) := by
  exact (isConnected_compl_singleton_of_one_lt_rank
    (by simp [Complex.rank_real_complex]) (0 : ℂ)).isPreconnected

/-- An infinite maximum set forces the reflected product to be constant on the
punctured plane. This is the identity-theorem part of the manuscript's
finiteness lemma, expressed without a separately defined maximum value. -/
theorem reflectionProduct_constant_of_infinite_maxPoints {f : ℂ → ℂ}
    (hf : Entire f) {r : ℝ} (hr : 0 < r) (hinf : (MaxPoints f r).Infinite) :
    ∃ C : ℂ, ∀ z : ℂ, z ≠ 0 → reflectionProduct f r z = C := by
  obtain ⟨z₀, hz₀⟩ := hinf.nonempty
  have hsub : MaxPoints f r ⊆ sphere (0 : ℂ) r := by
    intro z hz
    simpa [mem_sphere_iff_norm] using hz.1
  obtain ⟨a, ha, hacc⟩ := hinf.exists_accPt_of_subset_isCompact
    (isCompact_sphere (0 : ℂ) r) hsub
  have ha0 : a ≠ 0 := by
    have han : ‖a‖ = r := by simpa [mem_sphere_iff_norm] using ha
    intro h
    exact hr.ne' (by simpa [h] using han.symm)
  refine ⟨(‖f z₀‖ : ℂ) ^ 2, ?_⟩
  have heq : Set.EqOn (reflectionProduct f r) (fun _ => (‖f z₀‖ : ℂ) ^ 2) {0}ᶜ := by
    apply (analyticOnNhd_reflectionProduct hf r).eqOn_of_preconnected_of_frequently_eq
      analyticOnNhd_const punctured_plane_preconnected (by simpa using ha0)
    apply (accPt_iff_frequently_nhdsNE.mp hacc).mono
    intro z hz
    have hv : ‖f z‖ = ‖f z₀‖ := le_antisymm (hz₀.2 z hz.1) (hz.2 z₀ hz₀.1)
    rw [reflectionProduct_eq_sq_norm hr hz.1, hv]
  intro z hz
  exact heq (by simpa using hz)

/-- Conditional finiteness reduction: the remaining analytic task is precisely
to exclude constant reflected products for non-monomial entire functions. -/
theorem finite_maxPoints_of_reflectionProduct_not_constant {f : ℂ → ℂ}
    (hf : Entire f) {r : ℝ} (hr : 0 < r)
    (hnot : ¬∃ C : ℂ, ∀ z : ℂ, z ≠ 0 → reflectionProduct f r z = C) :
    (MaxPoints f r).Finite := by
  by_contra h
  exact hnot (reflectionProduct_constant_of_infinite_maxPoints hf hr h)

/-- Removing the order of vanishing at zero preserves entire differentiability.
The factorization is global, using iterated divided differences. -/
theorem entire_factor_at_zero {f : ℂ → ℂ} (hf : Entire f) (hne : f ≠ 0) :
    ∃ (m : ℕ) (g : ℂ → ℂ), Entire g ∧ g 0 ≠ 0 ∧ ∀ z, f z = z ^ m * g z := by
  obtain ⟨p, hp⟩ := hf.analyticAt 0
  have hpne : p ≠ 0 := by
    intro hpzero
    have hevent : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
      exact hp.locally_zero_iff.mpr hpzero
    exact hne ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      analyticOnNhd_const hevent)
  have hiter : ∀ n : ℕ, Entire ((Function.swap dslope (0 : ℂ))^[n] f) := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact differentiableOn_univ.mp ((Complex.differentiableOn_dslope (by simp)).mpr
        ih.differentiableOn)
  refine ⟨p.order, (Function.swap dslope (0 : ℂ))^[p.order] f, hiter p.order,
    hp.iterate_dslope_fslope_ne_zero hpne, ?_⟩
  intro z
  simpa using hp.eq_pow_order_mul_iterate_dslope z

/-- A function analytic at zero with a nonzero value there cannot have a
nonconstant entire reflected product. The proof uses a finite limit at infinity
and Liouville's theorem. -/
theorem eq_zero_value_of_reflectionProduct_constant {g : ℂ → ℂ}
    (hg : Entire g) (hgzero : g 0 ≠ 0) (r : ℝ) (C : ℂ)
    (hprod : ∀ z : ℂ, z ≠ 0 → reflectionProduct g r z = C) :
    ∀ z : ℂ, g z = g 0 := by
  have harg : Tendsto (fun z : ℂ => (r : ℂ) ^ 2 / z)
      (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    simpa [div_eq_mul_inv] using
      (tendsto_inv₀_cobounded (α := ℂ)).const_mul ((r : ℂ) ^ 2)
  have hstar := entire_reflection hg
  have hden : Tendsto (fun z : ℂ => reflection g ((r : ℂ) ^ 2 / z))
      (cocompact ℂ) (𝓝 (reflection g 0)) :=
    (hstar 0).continuousAt.tendsto.comp harg
  have hdenzero : reflection g 0 ≠ 0 := by simpa [reflection] using hgzero
  have hquot : Tendsto (fun z : ℂ => C / reflection g ((r : ℂ) ^ 2 / z))
      (cocompact ℂ) (𝓝 (C / reflection g 0)) :=
    tendsto_const_nhds.div hden hdenzero
  have heq : g =ᶠ[cocompact ℂ]
      (fun z : ℂ => C / reflection g ((r : ℂ) ^ 2 / z)) := by
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact,
      hden.eventually (isOpen_ne.mem_nhds hdenzero)] with z hz hd
    apply (eq_div_iff hd).mpr
    exact hprod z (by simpa using hz)
  have hlim : Tendsto g (cocompact ℂ) (𝓝 (C / reflection g 0)) :=
    hquot.congr' heq.symm
  intro z
  exact (hg.apply_eq_of_tendsto_cocompact z hlim).trans
    (hg.apply_eq_of_tendsto_cocompact 0 hlim).symm

/-- Constant reflected products characterize the obstruction needed for
finiteness: a nonzero entire function with such a product is a monomial. -/
theorem isMonomial_of_reflectionProduct_constant {f : ℂ → ℂ}
    (hf : Entire f) (hne : f ≠ 0) {r : ℝ} (hr : 0 < r) (C : ℂ)
    (hprod : ∀ z : ℂ, z ≠ 0 → reflectionProduct f r z = C) : IsMonomial f := by
  obtain ⟨m, g, hg, hgzero, hfactor⟩ := entire_factor_at_zero hf hne
  have hrzero : (r : ℂ) ≠ 0 := by simpa using hr.ne'
  have hscale : (r : ℂ) ^ (2 * m) ≠ 0 := pow_ne_zero _ hrzero
  have hprodg : ∀ z : ℂ, z ≠ 0 →
      reflectionProduct g r z = C / (r : ℂ) ^ (2 * m) := by
    intro z hz
    apply (eq_div_iff hscale).mpr
    have hh := hprod z hz
    dsimp [reflectionProduct, reflection] at hh ⊢
    rw [hfactor z, hfactor (conj ((r : ℂ) ^ 2 / z)), map_mul, map_pow,
      Complex.conj_conj] at hh
    calc
      g z * conj (g (conj ((r : ℂ) ^ 2 / z))) * (r : ℂ) ^ (2 * m)
          = (z ^ m * g z) * (((r : ℂ) ^ 2 / z) ^ m *
            conj (g (conj ((r : ℂ) ^ 2 / z)))) := by
        rw [div_pow, pow_mul]
        field_simp [hz]
      _ = C := hh
  have hgconst := eq_zero_value_of_reflectionProduct_constant hg hgzero r
    (C / (r : ℂ) ^ (2 * m)) hprodg
  refine ⟨g 0, m, hgzero, ?_⟩
  intro z
  rw [hfactor z, hgconst z]
  ring

/-- Every positive circle has finitely many actual maximum-modulus points for
a nonzero non-monomial entire function. -/
theorem finite_maxPoints {f : ℂ → ℂ} (hf : Entire f) (hne : f ≠ 0)
    (hnm : ¬IsMonomial f) {r : ℝ} (hr : 0 < r) : (MaxPoints f r).Finite := by
  apply finite_maxPoints_of_reflectionProduct_not_constant hf hr
  rintro ⟨C, hC⟩
  exact hnm (isMonomial_of_reflectionProduct_constant hf hne hr C hC)

end MaximumModulus
