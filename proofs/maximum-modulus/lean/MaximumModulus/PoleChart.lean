module

public import MaximumModulus.MeromorphicCorrespondence
public import MaximumModulus.InverseRootChart

@[expose] public section

/-!
# Regular value germs and reciprocal charts at actual logarithmic poles

The reciprocal chart is constructed from the proved simple meromorphic pole. Its value at
the pole is zero; away from the pole its values equal the actual reciprocal logarithmic
derivative. No analyticity of that reciprocal extension is assumed.
-/

open Filter Set
open scoped Topology

namespace MaximumModulus

noncomputable section

theorem analyticAt_normalizedLogDerivative_regular {g : ℂ → ℂ} (hg : Entire g)
    (m : ℕ) {a : ℂ} (hga : g a ≠ 0) :
    AnalyticAt ℂ (normalizedLogDerivative m g) a :=
  analyticAt_const.add ((analyticAt_id.mul (hg.analyticAt a).deriv).div (hg.analyticAt a) hga)

/-- Non-monomiality excludes an identically zero entire numerator for every finite value. -/
theorem logDerivativeNumerator_ne_zero {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) (p : ℂ) :
    logDerivativeNumerator m g p ≠ 0 := by
  intro hzero
  by_cases hp : p = (m : ℂ)
  · have hprod : ∀ z : ℂ, z * deriv g z = 0 := by
      intro z
      simpa [logDerivativeNumerator, hp] using congrFun hzero z
    apply normalizedLogDerivative_finite_order hg hg0 hnm hfactor
    apply analyticOrderAt_eq_top.mpr
    exact Eventually.of_forall fun z => by
      simp [normalizedLogDerivative, weightedLogDerivative, hprod z]
  · exact logDerivativeNumerator_zero_ne hg0 m hp (congrFun hzero 0)

/-- At every regular point and every finite target value, the actual logarithmic
derivative has finite analytic order. -/
theorem normalizedLogDerivative_finite_order_regular {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {a : ℂ} (hga : g a ≠ 0) (p : ℂ) :
    analyticOrderAt (fun z => normalizedLogDerivative m g z - p) a ≠ ⊤ := by
  intro htop
  have hvalue : ∀ᶠ z in 𝓝 a, normalizedLogDerivative m g z = p := by
    simpa only [sub_eq_zero] using analyticOrderAt_eq_top.mp htop
  have hgn : ∀ᶠ z in 𝓝 a, g z ≠ 0 :=
    (hg a).continuousAt.eventually (isOpen_ne.mem_nhds hga)
  have hN : ∀ᶠ z in 𝓝 a, logDerivativeNumerator m g p z = 0 := by
    filter_upwards [hvalue, hgn] with z hz hgz
    have hdiv : z * deriv g z / g z = p - (m : ℂ) := by
      exact eq_sub_iff_add_eq.mpr (by
        simpa only [normalizedLogDerivative, weightedLogDerivative, add_comm] using hz)
    exact sub_eq_zero.mpr ((div_eq_iff hgz).mp hdiv)
  have hNanalytic := (entire_logDerivativeNumerator hg m p).differentiableOn.analyticOnNhd isOpen_univ
  have hNglobal : logDerivativeNumerator m g p = 0 :=
    hNanalytic.eq_of_eventuallyEq analyticOnNhd_const hN
  exact logDerivativeNumerator_ne_zero hg hg0 hnm hfactor p hNglobal

/-- Near each point, a nonzero entire function has no punctured zeros. -/
theorem entire_eventually_ne_zero_punctured {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (a : ℂ) : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 := by
  rcases (hg.analyticAt a).eventually_eq_zero_or_eventually_ne_zero with hz | hne
  · exact False.elim (analyticOrderAt_entire_ne_top hg hg0 a (analyticOrderAt_eq_top.mpr hz))
  · exact hne

/-- A proved simple pole supplies an analytic reciprocal coordinate of order exactly one.
Its punctured values are the reciprocals of the actual normalized logarithmic derivative. -/
theorem normalizedLogDerivative_reciprocal_pole_chart {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (ha : a ≠ 0) (hga : g a = 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧ H a = 0 ∧ analyticOrderAt H a = 1 ∧
      (∀ᶠ z in 𝓝[≠] a, g z ≠ 0 ∧ H z = (normalizedLogDerivative m g z)⁻¹) := by
  have hq : MeromorphicAt (normalizedLogDerivative m g) a :=
    meromorphic_normalizedLogDerivative hg m a (mem_univ a)
  have horder : meromorphicOrderAt (normalizedLogDerivative m g) a = (-1 : ℤ) :=
    meromorphicOrderAt_normalizedLogDerivative_at_zero hg hg0 m ha hga
  obtain ⟨u, hu, hua, hqu⟩ := (meromorphicOrderAt_eq_int_iff hq).mp horder
  let H : ℂ → ℂ := fun z => (z - a) / u z
  have hH : AnalyticAt ℂ H a := (analyticAt_id.sub analyticAt_const).div hu hua
  have hHa : H a = 0 := by simp [H]
  have hHorder : analyticOrderAt H a = 1 := by
    rw [← ENat.natCast_one, hH.analyticOrderAt_eq_natCast]
    refine ⟨fun z => (u z)⁻¹, hu.inv hua, inv_ne_zero hua, ?_⟩
    exact Eventually.of_forall fun z => by simp [H, div_eq_mul_inv, smul_eq_mul]
  refine ⟨H, hH, hHa, hHorder, ?_⟩
  filter_upwards [hqu, entire_eventually_ne_zero_punctured hg hg0 a] with z hz hgz
  refine ⟨hgz, ?_⟩
  have hinv := congrArg (fun w : ℂ => w⁻¹) hz
  simpa [H, zpow_neg_one, smul_eq_mul, mul_inv_rev, div_eq_mul_inv, mul_comm] using hinv.symm

/-- The actual reciprocal value coordinate: a spherical pole is assigned the value zero. -/
def reciprocalSphereLogDerivative (m : ℕ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if g z = 0 then 0 else (normalizedLogDerivative m g z)⁻¹

/-- The actual reciprocal sphere coordinate is analytic at every pole, with order one. -/
theorem reciprocalSphereLogDerivative_pole_germ {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (ha : a ≠ 0) (hga : g a = 0) :
    AnalyticAt ℂ (reciprocalSphereLogDerivative m g) a ∧
      reciprocalSphereLogDerivative m g a = 0 ∧
      analyticOrderAt (reciprocalSphereLogDerivative m g) a = 1 := by
  obtain ⟨H, hH, hHa, horder, hnear⟩ :=
    normalizedLogDerivative_reciprocal_pole_chart hg hg0 m ha hga
  have heq : H =ᶠ[𝓝 a] reciprocalSphereLogDerivative m g := by
    filter_upwards [eventually_nhdsWithin_iff.mp hnear] with z hz
    by_cases hza : z = a
    · simp [hza, hHa, reciprocalSphereLogDerivative, hga]
    · have hregular := hz hza
      simpa only [reciprocalSphereLogDerivative, hregular.1, ↓reduceIte] using hregular.2
  exact ⟨hH.congr heq, by simp [reciprocalSphereLogDerivative, hga],
    (analyticOrderAt_congr heq).symm.trans horder⟩

/-- A nonzero reciprocal coordinate is exactly a nonzero finite spherical value. -/
theorem reciprocalSphereLogDerivative_eq_nonzero_iff (m : ℕ) (g : ℂ → ℂ)
    (z : ℂ) {u : ℂ} (hu : u ≠ 0) :
    reciprocalSphereLogDerivative m g z = u ↔
      sphereLogDerivative m g z = ((u⁻¹ : ℂ) : OnePoint ℂ) := by
  by_cases hgz : g z = 0
  · simp [reciprocalSphereLogDerivative, sphereLogDerivative, hgz, Ne.symm hu]
  · simp only [reciprocalSphereLogDerivative, sphereLogDerivative, hgz, ↓reduceIte,
      OnePoint.coe_eq_coe]
    exact ⟨fun h => by rw [← h, inv_inv], fun h => by rw [h, inv_inv]⟩

/-- The reciprocal pole germ supplies an inverse-root chart with exponent exactly one. -/
theorem reciprocalSphereLogDerivative_inverse_chart {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (ha : a ≠ 0) (hga : g a = 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧ e.symm 0 = a ∧ AnalyticAt ℂ e.symm 0 ∧
      ∀ z : ℂ, z ∈ e.source → reciprocalSphereLogDerivative m g z = e z := by
  obtain ⟨hR, hRa, horder⟩ := reciprocalSphereLogDerivative_pole_germ hg hg0 m ha hga
  have hfinite : analyticOrderAt (fun z => reciprocalSphereLogDerivative m g z -
      reciprocalSphereLogDerivative m g a) a ≠ ⊤ := by
    simpa only [hRa, sub_zero, horder] using (by decide : (1 : ℕ∞) ≠ ⊤)
  obtain ⟨k, _, hnat, e, ha', hzero, _, hψ, hpower⟩ := analytic_inverseRoot_chart hR hfinite
  have hk : k = 1 := by
    rw [hnat, analyticOrderNatAt]
    simp only [hRa, sub_zero, horder, ENat.toNat_one]
  refine ⟨e, ha', hzero, ?_, hψ, fun z hz => ?_⟩
  · simpa only [hzero] using e.left_inv ha'
  · simpa only [hRa, hk, pow_one, zero_add] using hpower z hz

/-- The constructed pole coordinate describes the actual spherical value at every point
of its source, including the center where the value is infinity. -/
theorem sphereLogDerivative_pole_inverse_chart {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (ha : a ≠ 0) (hga : g a = 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧ e.symm 0 = a ∧ AnalyticAt ℂ e.symm 0 ∧
      ∀ z : ℂ, z ∈ e.source → sphereLogDerivative m g z =
        if e z = 0 then OnePoint.infty else (((e z)⁻¹ : ℂ) : OnePoint ℂ) := by
  obtain ⟨e, ha', hzero, hcenter, hψ, hcoord⟩ :=
    reciprocalSphereLogDerivative_inverse_chart hg hg0 m ha hga
  refine ⟨e, ha', hzero, hcenter, hψ, fun z hz => ?_⟩
  by_cases hez : e z = 0
  · have hza : z = a := e.injOn hz ha' (hez.trans hzero.symm)
    simp [hza, hzero, sphereLogDerivative, hga]
  · simpa only [hez, ↓reduceIte] using
      (reciprocalSphereLogDerivative_eq_nonzero_iff m g z hez).mp (hcoord z hz)

/-- At a regular point, the genuine local power chart can be shrunk so that every
spherical value on its source is the actual finite quotient value. -/
theorem sphereLogDerivative_regular_inverse_chart {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {a : ℂ} (hga : g a ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧ e.symm 0 = a ∧ AnalyticAt ℂ e.symm 0 ∧
      ∀ z : ℂ, z ∈ e.source → sphereLogDerivative m g z =
        ((normalizedLogDerivative m g a + (e z) ^ k : ℂ) : OnePoint ℂ) := by
  have hq := analyticAt_normalizedLogDerivative_regular hg m hga
  have hfinite := normalizedLogDerivative_finite_order_regular hg hg0 hnm hfactor hga
    (normalizedLogDerivative m g a)
  obtain ⟨k, hk, _, E, ha, hzero, _, hψ, hpower⟩ := analytic_inverseRoot_chart hq hfinite
  have hnonzeroOpen : IsOpen {z : ℂ | g z ≠ 0} := isOpen_ne_fun hg.continuous continuous_const
  let e := E.restrOpen {z : ℂ | g z ≠ 0} hnonzeroOpen
  have hecenter : e a = 0 := hzero
  refine ⟨k, hk, e, ⟨ha, hga⟩, hecenter, ?_, ?_, fun z hz => ?_⟩
  · simpa only [e, OpenPartialHomeomorph.coe_restrOpen_symm, hzero] using E.left_inv ha
  · simpa only [e, OpenPartialHomeomorph.coe_restrOpen_symm] using hψ
  · have hgz : g z ≠ 0 := hz.2
    simp only [sphereLogDerivative, hgz, ↓reduceIte]
    simpa only [e, OpenPartialHomeomorph.coe_restrOpen] using
      congrArg (fun v : ℂ => (v : OnePoint ℂ)) (hpower z hz.1)

end

end MaximumModulus
