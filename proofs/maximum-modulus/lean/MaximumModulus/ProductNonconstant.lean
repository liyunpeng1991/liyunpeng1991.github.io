module

public import MaximumModulus.PairNonvertical

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- A finite-valued actual inverse-pair power germ has a nonconstant product.
First-coordinate nonconstancy is derived from the actual common values. -/
theorem logarithmic_pair_product_germ_nonconstant {f g Z W S : ℂ → ℂ} {m N : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) (hN : 0 < N) (p₀ : ℂ)
    (hZ : AnalyticAt ℂ Z 0) (hW : ContinuousAt W 0)
    (hproduct : ∀ t, Z t * W t = S t) (hS0 : S 0 ≠ 0)
    (hvalues : ∀ᶠ t in 𝓝 (0 : ℂ),
      sphereLogDerivative m g (Z t) = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      sphereLogDerivative m (reflection g) (W t) = ((p₀ + t ^ N : ℂ) : OnePoint ℂ)) :
    ¬∀ᶠ t in 𝓝 (0 : ℂ), S t = S 0 := by
  have hcenter := hvalues.self_of_nhds
  have hzvalue : sphereLogDerivative m g (Z 0) = (p₀ : OnePoint ℂ) := by
    simpa [hN.ne'] using hcenter.1
  have hwvalue : sphereLogDerivative m (reflection g) (W 0) = (p₀ : OnePoint ℂ) := by
    simpa [hN.ne'] using hcenter.2
  have hgz : g (Z 0) ≠ 0 := ((sphereLogDerivative_eq_coe m g (Z 0) p₀).mp hzvalue).1
  have hgw : reflection g (W 0) ≠ 0 :=
    ((sphereLogDerivative_eq_coe m (reflection g) (W 0) p₀).mp hwvalue).1
  have hzw0 : Z 0 * W 0 ≠ 0 := by rw [hproduct]; exact hS0
  have hz0 : Z 0 ≠ 0 := left_ne_zero_of_mul hzw0
  have hne : ¬∀ᶠ t in 𝓝 (0 : ℂ), Z t = Z 0 := by
    intro hconst
    apply power_value_germ_nonconstant hN p₀
    filter_upwards [hconst, hvalues] with t hc hv
    apply OnePoint.coe_injective
    rw [← hv.1, hc]
    simpa [hN.ne'] using hzvalue
  intro hconst
  apply no_constant_product_spherical_regular_pair_germ hg hg0 hnm hfactor hZ hW
    hne hz0 hgz hgw (hvalues.mono fun _ h => h.1.trans h.2.symm) (hproduct 0)
  exact hconst.mono fun t ht => (hproduct t).trans ht

end MaximumModulus
