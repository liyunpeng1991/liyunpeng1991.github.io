module

public import MaximumModulus.LocalValence
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

@[expose] public section

/-!
# Analytic inverse-root charts and capture of local fibers

This constructs the local power coordinate and its analytic inverse from the order of an
analytic germ. The resulting open partial homeomorphism describes every preimage in its
source, so the inverse-root enumeration does not assume an unproved chart-existence lemma.
-/

open Filter
open scoped Topology

namespace MaximumModulus

noncomputable section

/-- A root germ centered at an arbitrary point. The root identity holds at every input;
analyticity is required only near the chosen base point. -/
theorem analytic_germ_root_at {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a)
    (hga : g a ≠ 0) (k : ℕ) (hk : 0 < k) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ h a ≠ 0 ∧ ∀ z, (h z) ^ k = g z := by
  let h : ℂ → ℂ := fun z => (g a) ^ ((k : ℂ)⁻¹) * (g z / g a) ^ ((k : ℂ)⁻¹)
  have hratio : AnalyticAt ℂ (fun z => g z / g a) a := hg.div_const
  have hratio0 : g a / g a ∈ Complex.slitPlane := by simp [div_self hga]
  have hh : AnalyticAt ℂ h a :=
    analyticAt_const.mul (hratio.cpow analyticAt_const hratio0)
  have hha : h a ≠ 0 := by
    dsimp [h]
    simp only [div_self hga, Complex.one_cpow, mul_one]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hga)
  refine ⟨h, hh, hha, fun z => ?_⟩
  dsimp [h]
  rw [mul_pow, Complex.cpow_nat_inv_pow _ hk.ne', Complex.cpow_nat_inv_pow _ hk.ne']
  exact mul_div_cancel₀ (g z) hga

/-- A nonconstant analytic germ admits a genuine analytic local power chart. Both
directions of the coordinate are analytic at their centers, and the power identity holds
on the entire chart source. -/
theorem analytic_inverseRoot_chart {A : ℂ → ℂ} {a : ℂ} (hA : AnalyticAt ℂ A a)
    (hfinite : analyticOrderAt (fun z => A z - A a) a ≠ ⊤) :
    ∃ k : ℕ, 0 < k ∧ k = analyticOrderNatAt (fun z => A z - A a) a ∧
      ∃ e : OpenPartialHomeomorph ℂ ℂ,
        a ∈ e.source ∧ e a = 0 ∧ AnalyticAt ℂ e a ∧ AnalyticAt ℂ e.symm 0 ∧
        ∀ z : ℂ, z ∈ e.source → A z = A a + (e z) ^ k := by
  have hF : AnalyticAt ℂ (fun z => A z - A a) a := hA.sub analyticAt_const
  have hnonzero : analyticOrderAt (fun z => A z - A a) a ≠ 0 :=
    hF.analyticOrderAt_ne_zero.mpr (sub_self _)
  let k := analyticOrderNatAt (fun z => A z - A a) a
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro heq
    apply hnonzero
    rw [← Nat.cast_analyticOrderNatAt hfinite]
    change (k : ℕ∞) = 0
    rw [heq]
    rfl
  obtain ⟨g, hg, hga, hFg⟩ := hF.analyticOrderAt_ne_top.mp hfinite
  obtain ⟨h, hh, hha, hroot⟩ := analytic_germ_root_at hg hga k hk
  let τ : ℂ → ℂ := fun z => (z - a) * h z
  have hτ : AnalyticAt ℂ τ a := (analyticAt_id.sub analyticAt_const).mul hh
  have hτa : τ a = 0 := by simp [τ]
  have hsub : HasStrictDerivAt (fun z : ℂ => z - a) (1 : ℂ) a := by
    convert! (hasStrictDerivAt_id (𝕜 := ℂ) (x := a)).sub_const a using 1
  have hd : HasStrictDerivAt τ (h a) a := by
    convert! hsub.mul hh.hasStrictDerivAt using 1
    simp
  have hder : deriv τ a ≠ 0 := by rw [hd.hasDerivAt.deriv]; exact hha
  let D := hτ.hasStrictDerivAt.hasStrictFDerivAt_equiv hder
  let E := D.toOpenPartialHomeomorph τ
  have hEa : a ∈ E.source := D.mem_toOpenPartialHomeomorph_source
  have hEτ : (E : ℂ → ℂ) = τ := rfl
  have hEana : AnalyticAt ℂ E a := by simpa only [hEτ] using hτ
  have hEinvana : AnalyticAt ℂ E.symm 0 := by
    convert! hτ.analyticAt_localInverse hder using 1
    exact hτa.symm
  have hpow : ∀ᶠ z in 𝓝 a, A z = A a + (τ z) ^ k := by
    filter_upwards [hFg] with z hz
    have heq : A z - A a = (z - a) ^ k * g z := by
      simpa only [smul_eq_mul] using hz
    rw [← hroot z, ← mul_pow] at heq
    exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hpow
  let e := E.restrOpen (Metric.ball a ε) Metric.isOpen_ball
  refine ⟨k, hk, rfl, e, ⟨hEa, Metric.mem_ball_self hε⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [e, OpenPartialHomeomorph.coe_restrOpen, hEτ] using hτa
  · simpa only [e, OpenPartialHomeomorph.coe_restrOpen] using hEana
  · simpa only [e, OpenPartialHomeomorph.coe_restrOpen_symm] using hEinvana
  · intro z hz
    exact hlocal hz.2

/-- Exact capture of the local fiber by all roots lying in the chart target. -/
theorem inverseRoot_chart_fiber {A : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hpower : ∀ z : ℂ, z ∈ e.source → A z = A a + (e z) ^ k) (p : ℂ) :
    {z : ℂ | z ∈ e.source ∧ A z = p} =
      e.symm '' {t : ℂ | t ∈ e.target ∧ t ^ k = p - A a} := by
  ext z
  constructor
  · intro hz
    refine ⟨e z, ⟨e.map_source hz.1, ?_⟩, e.left_inv hz.1⟩
    have heq := hpower z hz.1
    rw [hz.2] at heq
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using heq.symm)
  · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
    refine ⟨e.map_target ht, ?_⟩
    rw [hpower _ (e.map_target ht), e.right_inv ht, hp]
    exact add_sub_cancel _ _

/-- Every root of a sufficiently small target value lies in the target chart. Hence the
local fiber is precisely the image of the full power-equation root set. -/
theorem inverseRoot_chart_fiber_small {A : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hpower : ∀ z : ℂ, z ∈ e.source → A z = A a + (e z) ^ k)
    {δ : ℝ} (hδ : 0 < δ) (hball : Metric.ball (0 : ℂ) δ ⊆ e.target)
    {p : ℂ} (hp : ‖p - A a‖ < δ ^ k) :
    {z : ℂ | z ∈ e.source ∧ A z = p} = e.symm '' {t : ℂ | t ^ k = p - A a} := by
  rw [inverseRoot_chart_fiber e hpower p]
  congr 1
  ext t
  constructor
  · exact And.right
  · intro ht
    refine ⟨hball ?_, ht⟩
    have hnorm : ‖t‖ ^ k < δ ^ k := by rw [← norm_pow, ht]; exact hp
    simpa only [Metric.mem_ball, dist_zero_right] using
      lt_of_pow_lt_pow_left₀ k hδ.le hnorm

/-- A chart with a positive target disk, an analytic inverse, and complete capture of every
sufficiently small-value fiber in an open neighborhood of the original source point. -/
theorem analytic_inverseRoot_capture {A : ℂ → ℂ} {a : ℂ} (hA : AnalyticAt ℂ A a)
    (hfinite : analyticOrderAt (fun z => A z - A a) a ≠ ⊤) :
    ∃ k : ℕ, 0 < k ∧ k = analyticOrderNatAt (fun z => A z - A a) a ∧
      ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ δ : ℝ,
        a ∈ e.source ∧ e a = 0 ∧ e.symm 0 = a ∧
        AnalyticAt ℂ e a ∧ AnalyticAt ℂ e.symm 0 ∧ 0 < δ ∧
        Metric.ball (0 : ℂ) δ ⊆ e.target ∧
        Set.InjOn e.symm (Metric.ball (0 : ℂ) δ) ∧
        (∀ t : ℂ, ‖t‖ < δ → A (e.symm t) = A a + t ^ k) ∧
        ∀ p : ℂ, ‖p - A a‖ < δ ^ k →
          {z : ℂ | z ∈ e.source ∧ A z = p} =
            e.symm '' {t : ℂ | t ^ k = p - A a} := by
  obtain ⟨k, hk, horder, e, ha, hzero, heana, hinvana, hpower⟩ :=
    analytic_inverseRoot_chart hA hfinite
  have htarget : (0 : ℂ) ∈ e.target := hzero ▸ e.map_source ha
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds htarget)
  refine ⟨k, hk, horder, e, δ, ha, hzero, ?_, heana, hinvana, hδ, hball, ?_, ?_, ?_⟩
  · simpa only [hzero] using e.left_inv ha
  · exact e.symm.injOn.mono hball
  · intro t ht
    have htarget := hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)
    rw [hpower _ (e.map_target htarget), e.right_inv htarget]
  · intro p hp
    exact inverseRoot_chart_fiber_small e hpower hδ hball hp

/-- All roots over a common power parameter are the rotations of one fixed power. -/
theorem power_roots_eq_scaled_unity {k l : ℕ} {t : ℂ} (ht : t ≠ 0) :
    {u : ℂ | u ^ k = t ^ (k * l)} =
      (fun ω : ℂ => ω * t ^ l) '' {ω : ℂ | ω ^ k = 1} := by
  have hpow : (t ^ l) ^ k = t ^ (k * l) := by rw [← pow_mul, Nat.mul_comm]
  ext u
  constructor
  · intro hu
    refine ⟨u / t ^ l, ?_, div_mul_cancel₀ _ (pow_ne_zero _ ht)⟩
    change (u / t ^ l) ^ k = 1
    rw [div_pow, hu, ← hpow, div_self (pow_ne_zero _ (pow_ne_zero _ ht))]
  · rintro ⟨ω, hω, rfl⟩
    change (ω * t ^ l) ^ k = t ^ (k * l)
    rw [mul_pow, hω, one_mul, hpow]

/-- Every inverse-root branch is analytic at the common parameter origin. -/
theorem analytic_inverseRoot_branch {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ 0)
    {l : ℕ} (hl : 0 < l) (ω : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => ψ (ω * t ^ l)) 0 := by
  have hinner : AnalyticAt ℂ (fun t : ℂ => ω * t ^ l) 0 :=
    analyticAt_const.mul (analyticAt_id.pow l)
  exact hψ.fun_comp_of_eq hinner (by simp [hl.ne'])

/-- Exact enumeration of all physical roots in the chart source over `A(a)+t^(k*l)`.
For a small nonzero parameter, distinct `k`th roots of unity give distinct physical roots. -/
theorem inverseRoot_chart_common_power {A : ℂ → ℂ} {a : ℂ} {k l : ℕ}
    (hk : 0 < k) (hl : 0 < l) (e : OpenPartialHomeomorph ℂ ℂ)
    (hpower : ∀ z : ℂ, z ∈ e.source → A z = A a + (e z) ^ k)
    {δ : ℝ} (hδ : 0 < δ) (hball : Metric.ball (0 : ℂ) δ ⊆ e.target) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
      {z : ℂ | z ∈ e.source ∧ A z = A a + t ^ (k * l)} =
        (fun ω : ℂ => e.symm (ω * t ^ l)) '' {ω : ℂ | ω ^ k = 1} ∧
      Set.InjOn (fun ω : ℂ => e.symm (ω * t ^ l)) {ω : ℂ | ω ^ k = 1} := by
  have htend : Tendsto (fun t : ℂ => t ^ l) (𝓝 0) (𝓝 0) := by
    convert! (continuous_id.pow l).continuousAt.tendsto (x := (0 : ℂ)) using 1
    simp [hl.ne']
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℂ), ‖t ^ l‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      htend.eventually (Metric.ball_mem_nhds (0 : ℂ) hδ)
  obtain ⟨ε, hε, hnorm⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨ε, hε, fun t ht hne => ?_⟩
  have htl : ‖t ^ l‖ < δ := hnorm (by simpa only [dist_zero_right] using ht)
  have hvalue : ‖(A a + t ^ (k * l)) - A a‖ < δ ^ k := by
    rw [add_sub_cancel_left, Nat.mul_comm k l, pow_mul, norm_pow]
    exact pow_lt_pow_left₀ htl (norm_nonneg _) hk.ne'
  constructor
  · rw [inverseRoot_chart_fiber_small e hpower hδ hball hvalue,
      add_sub_cancel_left, power_roots_eq_scaled_unity hne, Set.image_image]
  · intro ω hω ξ hξ heq
    have htarget : ∀ η : ℂ, η ^ k = 1 → η * t ^ l ∈ e.target := by
      intro η hη
      apply hball
      have hηnorm := Complex.norm_eq_one_of_pow_eq_one hη hk.ne'
      simpa only [Metric.mem_ball, dist_zero_right, norm_mul, hηnorm, one_mul] using htl
    have hmul := e.symm.injOn (htarget ω hω) (htarget ξ hξ) heq
    exact mul_right_cancel₀ (pow_ne_zero _ hne) hmul

/-- Construction and complete enumeration of an inverse-root family from an analytic germ.
The chart, its inverse, and capture of all nearby physical roots are all conclusions. -/
theorem analytic_inverseRoot_family {A : ℂ → ℂ} {a : ℂ} (hA : AnalyticAt ℂ A a)
    (hfinite : analyticOrderAt (fun z => A z - A a) a ≠ ⊤) :
    ∃ k : ℕ, 0 < k ∧ k = analyticOrderNatAt (fun z => A z - A a) a ∧
      ∃ e : OpenPartialHomeomorph ℂ ℂ,
        a ∈ e.source ∧ e a = 0 ∧ e.symm 0 = a ∧ AnalyticAt ℂ e.symm 0 ∧
        ∀ l : ℕ, 0 < l →
          (∀ ω : ℂ, AnalyticAt ℂ (fun t : ℂ => e.symm (ω * t ^ l)) 0) ∧
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
            {z : ℂ | z ∈ e.source ∧ A z = A a + t ^ (k * l)} =
              (fun ω : ℂ => e.symm (ω * t ^ l)) '' {ω : ℂ | ω ^ k = 1} ∧
            Set.InjOn (fun ω : ℂ => e.symm (ω * t ^ l)) {ω : ℂ | ω ^ k = 1} := by
  obtain ⟨k, hk, horder, e, ha, hzero, _, hinvana, hpower⟩ :=
    analytic_inverseRoot_chart hA hfinite
  have htarget : (0 : ℂ) ∈ e.target := hzero ▸ e.map_source ha
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds htarget)
  refine ⟨k, hk, horder, e, ha, hzero, ?_, hinvana, fun l hl => ?_⟩
  · simpa only [hzero] using e.left_inv ha
  · exact ⟨fun ω => analytic_inverseRoot_branch hinvana hl ω,
      inverseRoot_chart_common_power hk hl e hpower hδ hball⟩

end

end MaximumModulus
