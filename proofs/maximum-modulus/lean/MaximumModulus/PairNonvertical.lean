module

public import MaximumModulus.LocalReciprocal
public import MaximumModulus.MeromorphicCorrespondence
public import MaximumModulus.LocalImageTopology

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- The inverse-root coordinate is nonconstant as a germ. This follows from
the actual inverse identity on the chart target and a positive power. -/
theorem inverseRoot_branch_germ_nonconstant
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} (ha : a ∈ e.source) (hea : e a = 0)
    {l : ℕ} (hl : 0 < l) {η : ℂ} (hη : η ≠ 0) :
    ¬∀ᶠ t in 𝓝 (0 : ℂ), e.symm (η * t ^ l) = e.symm 0 := by
  intro hconst
  have htarget0 : (0 : ℂ) ∈ e.target := by
    simpa [hea] using e.map_source ha
  have htarget : ∀ᶠ t in 𝓝 (0 : ℂ), η * t ^ l ∈ e.target := by
    have htend : Tendsto (fun t : ℂ => η * t ^ l) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℂ => η * t ^ l) 0 := by fun_prop
      change Tendsto (fun t : ℂ => η * t ^ l) (𝓝 0) (𝓝 (η * (0 : ℂ) ^ l)) at hc
      simpa only [zero_pow hl.ne', mul_zero] using hc
    exact htend.eventually (e.open_target.mem_nhds htarget0)
  apply power_value_germ_nonconstant hl (0 : ℂ)
  filter_upwards [hconst, htarget] with t hc ht
  have heq : η * t ^ l = 0 := by
    simpa [e.right_inv ht, e.right_inv htarget0] using congrArg e hc
  have hp : t ^ l = 0 := (mul_eq_zero.mp heq).resolve_left hη
  simp [hp, hl.ne']

/-- A nonconstant analytic first coordinate opens the parameter germ into an
actual neighborhood of the first physical coordinate. A constant product and
common logarithmic-derivative values there would force forbidden reciprocity. -/
theorem no_constant_product_regular_pair_germ {f g Z W : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) {t₀ : ℂ}
    (hZ : AnalyticAt ℂ Z t₀)
    (hne : ¬∀ᶠ t in 𝓝 t₀, Z t = Z t₀)
    (hz0 : Z t₀ ≠ 0) (hgz : g (Z t₀) ≠ 0)
    (hgw : reflection g (W t₀) ≠ 0)
    (hvalue : ∀ᶠ t in 𝓝 t₀,
      normalizedLogDerivative m g (Z t) = normalizedLogDerivative m (reflection g) (W t))
    {s : ℂ} (hcenter : Z t₀ * W t₀ = s) :
    ¬∀ᶠ t in 𝓝 t₀, Z t * W t = s := by
  intro hprod
  have hmap : 𝓝 (Z t₀) ≤ Filter.map Z (𝓝 t₀) :=
    hZ.eventually_constant_or_nhds_le_map_nhds.resolve_left hne
  have hw : W t₀ = s / Z t₀ := by
    apply (eq_div_iff hz0).mpr
    simpa [mul_comm] using hcenter
  apply no_local_normalized_reciprocity hg hg0 hnm hfactor (s := s) hz0 hgz
    (by simpa [← hw] using hgw)
  apply hmap
  apply Filter.eventually_map.mpr
  filter_upwards [hvalue, hprod,
    hZ.continuousAt.eventually (isOpen_ne.mem_nhds hz0)] with t hq hp hz
  have hwt : W t = s / Z t := by
    apply (eq_div_iff hz).mpr
    simpa [mul_comm] using hp
  rw [reflection_normalizedLogDerivative, ← hwt]
  exact hq

/-- The same exclusion applies directly to the actual spherical functions
on every pair germ whose central common value is finite. -/
theorem no_constant_product_spherical_regular_pair_germ
    {f g Z W : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) {t₀ : ℂ}
    (hZ : AnalyticAt ℂ Z t₀) (hW : ContinuousAt W t₀)
    (hne : ¬∀ᶠ t in 𝓝 t₀, Z t = Z t₀)
    (hz0 : Z t₀ ≠ 0) (hgz : g (Z t₀) ≠ 0)
    (hgw : reflection g (W t₀) ≠ 0)
    (hvalue : ∀ᶠ t in 𝓝 t₀,
      sphereLogDerivative m g (Z t) = sphereLogDerivative m (reflection g) (W t))
    {s : ℂ} (hcenter : Z t₀ * W t₀ = s) :
    ¬∀ᶠ t in 𝓝 t₀, Z t * W t = s := by
  apply no_constant_product_regular_pair_germ hg hg0 hnm hfactor hZ hne hz0 hgz hgw
    (s := s) (hcenter := hcenter)
  filter_upwards [hvalue,
    (hg.continuous.continuousAt.comp hZ.continuousAt).eventually (isOpen_ne.mem_nhds hgz),
    ((entire_reflection hg).continuous.continuousAt.comp hW).eventually
      (isOpen_ne.mem_nhds hgw)] with t hq hzt hwt
  apply OnePoint.coe_injective
  change g (Z t) ≠ 0 at hzt
  change reflection g (W t) ≠ 0 at hwt
  simpa [sphereLogDerivative, hzt, hwt] using hq

end MaximumModulus
