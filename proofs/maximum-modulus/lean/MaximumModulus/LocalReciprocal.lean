module

public import MaximumModulus.LogDerivative

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- A reciprocal identity on one regular open germ already forces the factor
to be constant; no global meromorphic identity is assumed. -/
theorem constant_of_local_normalized_reciprocity {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) {s a : ℂ} (ha : a ≠ 0)
    (hga : g a ≠ 0) (hrga : reflection g (s / a) ≠ 0)
    (hsym : ∀ᶠ z in 𝓝 a, normalizedLogDerivative m g z =
      reflection (normalizedLogDerivative m g) (s / z)) :
    ∀ z : ℂ, g z = g 0 := by
  have hPa := analyticOnNhd_reciprocalProduct hg s
  have hRcont : ContinuousAt (fun z => reflection g (s / z)) a :=
    (analyticOnNhd_reciprocalReflection hg s a (by simpa using ha)).continuousAt
  have hder : ∀ᶠ z in 𝓝 a, deriv (reciprocalProduct g s) z = 0 := by
    filter_upwards [hsym, (hg a).continuousAt.eventually (isOpen_ne.mem_nhds hga),
      hRcont.eventually (isOpen_ne.mem_nhds hrga), isOpen_ne.mem_nhds ha]
      with z hq hgz hrgz hz0
    have hqw : weightedLogDerivative g z = reflection (weightedLogDerivative g) (s / z) := by
      simpa [reflection, normalizedLogDerivative] using hq
    rw [reflection_weightedLogDerivative] at hqw
    unfold weightedLogDerivative at hqw
    field_simp [hz0, hgz, hrgz] at hqw
    rw [deriv_reciprocalProduct hg s hz0]
    field_simp [hz0]
    linear_combination hqw
  have heq : EqOn (deriv (reciprocalProduct g s)) (fun _ => 0) ({0}ᶜ : Set ℂ) :=
    hPa.deriv.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      punctured_plane_preconnected (by simpa using ha)
      (hder.filter_mono nhdsWithin_le_nhds).frequently
  obtain ⟨C, hC⟩ := isOpen_compl_singleton.exists_is_const_of_deriv_eq_zero
    punctured_plane_preconnected hPa.differentiableOn heq
  exact eq_zero_value_of_reciprocalProduct_constant hg hg0 s C
    (fun z hz => hC z (by simpa using hz))

/-- Non-monomiality excludes every regular local reciprocal germ. This is
the local form needed to exclude constant-product image branches. -/
theorem no_local_normalized_reciprocity {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) {s a : ℂ} (ha : a ≠ 0)
    (hga : g a ≠ 0) (hrga : reflection g (s / a) ≠ 0) :
    ¬∀ᶠ z in 𝓝 a, normalizedLogDerivative m g z =
      reflection (normalizedLogDerivative m g) (s / z) := by
  intro hsym
  have hconst := constant_of_local_normalized_reciprocity hg hg0 ha hga hrga hsym
  apply hnm
  refine ⟨g 0, m, hg0, ?_⟩
  intro z
  rw [hfactor z, hconst z]
  ring

end MaximumModulus
