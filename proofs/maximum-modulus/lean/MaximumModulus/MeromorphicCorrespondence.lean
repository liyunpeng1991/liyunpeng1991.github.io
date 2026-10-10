module

public import MaximumModulus.LogDerivative
public import MaximumModulus.SmallFibers
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

@[expose] public section

open Set Filter Metric
open scoped Topology ComplexConjugate OnePoint

noncomputable section

namespace MaximumModulus

/-- The normalized logarithmic derivative is a genuine meromorphic function. -/
theorem meromorphic_normalizedLogDerivative {g : ℂ → ℂ} (hg : Entire g) (m : ℕ) :
    MeromorphicOn (normalizedLogDerivative m g) univ := by
  intro z _
  exact MeromorphicAt.const (m : ℂ) z |>.add
    ((analyticAt_id.meromorphicAt.mul (hg.analyticAt z).deriv.meromorphicAt).div
      (hg.analyticAt z).meromorphicAt)

/-- Continuity at the origin prevents coordinates of an inverse pair from
approaching zero while the common value stays separated from the origin value. -/
theorem inverse_pairs_coordinates_bounded_below {A B : ℂ → ℂ} {c : ℂ}
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hAc : A 0 = c) (hBc : B 0 = c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s p : ℂ, δ ≤ dist p c →
      ∀ zw ∈ InversePairs A B s p, ε ≤ ‖zw.1‖ ∧ ε ≤ ‖zw.2‖ := by
  obtain ⟨εA, hεA, hnearA⟩ := Metric.continuousAt_iff.mp hA δ hδ
  obtain ⟨εB, hεB, hnearB⟩ := Metric.continuousAt_iff.mp hB δ hδ
  refine ⟨min εA εB, lt_min hεA hεB, ?_⟩
  intro s p hp zw hzw
  constructor
  · apply le_of_not_gt
    intro hz
    have hd := hnearA (by simpa only [dist_zero_right] using hz.trans_le (min_le_left _ _))
    rw [hzw.2.1, hAc] at hd
    exact (not_lt_of_ge hp) hd
  · apply le_of_not_gt
    intro hw
    have hd := hnearB (by simpa only [dist_zero_right] using hw.trans_le (min_le_right _ _))
    rw [hzw.2.2, hBc] at hd
    exact (not_lt_of_ge hp) hd

/-- Bounded product coordinate and a common value separated from `c` place
all inverse pairs in a fixed compact annulus product. -/
theorem inverse_pairs_annulus_bounds {A B : ℂ → ℂ} {c : ℂ}
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hAc : A 0 = c) (hBc : B 0 = c) {δ : ℝ} (hδ : 0 < δ) (S : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s p : ℂ, ‖s‖ ≤ S → δ ≤ dist p c →
      ∀ zw ∈ InversePairs A B s p,
        ε ≤ ‖zw.1‖ ∧ ε ≤ ‖zw.2‖ ∧ ‖zw.1‖ ≤ S / ε ∧ ‖zw.2‖ ≤ S / ε := by
  obtain ⟨ε, hε, hcoord⟩ := inverse_pairs_coordinates_bounded_below hA hB hAc hBc hδ
  refine ⟨ε, hε, ?_⟩
  intro s p hs hp zw hzw
  obtain ⟨hz, hw⟩ := hcoord s p hp zw hzw
  have hprod : ‖zw.1‖ * ‖zw.2‖ ≤ S := by rw [← norm_mul, hzw.1]; exact hs
  refine ⟨hz, hw, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans hprod
  · exact (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans (by simpa [mul_comm] using hprod)

/-- Zeros of a nonzero entire function are finite in every compact set. -/
theorem finite_entire_zeros_in_compact {F : ℂ → ℂ} (hF : Entire F)
    (hF0 : F 0 ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ F z = 0}.Finite := by
  by_contra hinf
  have hInf : {z : ℂ | z ∈ K ∧ F z = 0}.Infinite := hinf
  obtain ⟨a, _, hacc⟩ := hInf.exists_accPt_of_subset_isCompact hK (fun _ hz => hz.1)
  have heq : F = fun _ => (0 : ℂ) :=
    (hF.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
      analyticOnNhd_const ((accPt_iff_frequently_nhdsNE.mp hacc).mono (fun _ hz => hz.2))
  exact hF0 (congrFun heq 0)

/-- The entire numerator for a finite logarithmic value. -/
def logDerivativeNumerator (m : ℕ) (g : ℂ → ℂ) (p z : ℂ) : ℂ :=
  z * deriv g z - (p - (m : ℂ)) * g z

theorem entire_logDerivativeNumerator {g : ℂ → ℂ} (hg : Entire g) (m : ℕ) (p : ℂ) :
    Entire (logDerivativeNumerator m g p) := by
  intro z
  exact ((differentiableAt_id.mul (hg.analyticAt z).deriv.differentiableAt).sub
    ((differentiableAt_const (p - (m : ℂ))).mul (hg z)))

theorem logDerivativeNumerator_zero_ne {g : ℂ → ℂ} (hg0 : g 0 ≠ 0)
    (m : ℕ) {p : ℂ} (hp : p ≠ (m : ℂ)) : logDerivativeNumerator m g p 0 ≠ 0 := by
  simpa [logDerivativeNumerator] using mul_ne_zero (sub_ne_zero.mpr hp) hg0

theorem logDerivativeNumerator_eq_zero_of_value {g : ℂ → ℂ} (m : ℕ) {p z : ℂ}
    (hp : p ≠ (m : ℂ)) (hz : normalizedLogDerivative m g z = p) :
    logDerivativeNumerator m g p z = 0 := by
  have hg : g z ≠ 0 := by
    intro hgz
    apply hp
    simpa [normalizedLogDerivative, weightedLogDerivative, hgz] using hz.symm
  have hdiv : z * deriv g z / g z = p - (m : ℂ) := by
    exact (eq_sub_iff_add_eq.mpr (by simpa [normalizedLogDerivative, weightedLogDerivative,
      add_comm] using hz))
  exact sub_eq_zero.mpr ((div_eq_iff hg).mp hdiv)

theorem reflection_normalizedLogDerivative (g : ℂ → ℂ) (m : ℕ) :
    reflection (normalizedLogDerivative m g) = normalizedLogDerivative m (reflection g) := by
  ext z
  simp [reflection, normalizedLogDerivative, weightedLogDerivative, deriv_reflection]

/-- For a nonzero fixed product, either coordinate uniquely determines the inverse pair. -/
theorem inverse_pairs_first_injective {β : Type*} {A B : ℂ → β} {s : ℂ} {p : β} (hs : s ≠ 0) :
    Set.InjOn Prod.fst (InversePairs A B s p) := by
  intro zw hzw zw' hzw' hfirst
  have hz0 : zw.1 ≠ 0 := by
    intro hz
    exact hs (by simpa [hz] using hzw.1.symm)
  have hprod : zw.1 * zw.2 = zw.1 * zw'.2 := by
    rw [hzw.1, hfirst, hzw'.1]
  exact Prod.ext hfirst (mul_left_cancel₀ hz0 hprod)

/-- Every finite value different from the removable value has a finite actual
inverse-pair fiber. The proof confines pairs to a compact annulus and embeds
the first coordinates in zeros of a nonzero entire numerator. -/
theorem normalizedLogDerivative_finite_inverse_pairs {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {s p : ℂ}
    (hs : s ≠ 0) (hp : p ≠ (m : ℂ)) :
    (InversePairs (normalizedLogDerivative m g)
      (reflection (normalizedLogDerivative m g)) s p).Finite := by
  have hA : ContinuousAt (normalizedLogDerivative m g) 0 :=
    (analyticAt_normalizedLogDerivative hg hg0 m).continuousAt
  have hB : ContinuousAt (reflection (normalizedLogDerivative m g)) 0 := by
    rw [reflection_normalizedLogDerivative]
    exact (analyticAt_normalizedLogDerivative (entire_reflection hg)
      (by simpa [reflection] using hg0) m).continuousAt
  have hAc : normalizedLogDerivative m g 0 = (m : ℂ) := by simp
  have hBc : reflection (normalizedLogDerivative m g) 0 = (m : ℂ) := by
    simp [reflection]
  obtain ⟨ε, _, hbound⟩ := inverse_pairs_annulus_bounds hA hB hAc hBc
    (dist_pos.mpr hp) ‖s‖
  have hfinite : {z : ℂ | z ∈ closedBall (0 : ℂ) (‖s‖ / ε) ∧
      logDerivativeNumerator m g p z = 0}.Finite :=
    finite_entire_zeros_in_compact (entire_logDerivativeNumerator hg m p)
      (logDerivativeNumerator_zero_ne hg0 m hp) (isCompact_closedBall 0 (‖s‖ / ε))
  have hmaps : Set.MapsTo Prod.fst
      (InversePairs (normalizedLogDerivative m g)
        (reflection (normalizedLogDerivative m g)) s p)
      {z : ℂ | z ∈ closedBall (0 : ℂ) (‖s‖ / ε) ∧ logDerivativeNumerator m g p z = 0} := by
    intro zw hzw
    refine ⟨?_, logDerivativeNumerator_eq_zero_of_value m hp hzw.2.1⟩
    simpa only [mem_closedBall, dist_zero_right] using
      (hbound s p le_rfl le_rfl zw hzw).2.2.1
  exact Set.Finite.of_injOn hmaps (inverse_pairs_first_injective hs) hfinite

/-- A nonzero entire function has a nonzero germ at every point. -/
theorem analyticOrderAt_entire_ne_top {g : ℂ → ℂ} (hg : Entire g) (hg0 : g 0 ≠ 0)
    (a : ℂ) : analyticOrderAt g a ≠ ⊤ := by
  intro htop
  have heq : g = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero a hg.analyticAt).mp htop
  exact hg0 (congrFun heq 0)

/-- The normalized logarithmic derivative has a genuine simple pole at each
nonzero zero of the entire factor. -/
theorem meromorphicOrderAt_normalizedLogDerivative_at_zero {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (ha : a ≠ 0) (hga : g a = 0) :
    meromorphicOrderAt (normalizedLogDerivative m g) a = -1 := by
  have hAna := hg.analyticAt a
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_entire_ne_top hg hg0 a)
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hAna.analyticOrderAt_ne_zero.mpr hga
    rw [← hn, hn0]
    rfl
  have horder : meromorphicOrderAt g a = (n : WithTop ℤ) := by
    rw [hAna.meromorphicOrderAt_eq, ← hn]
    simp
  have hlog : meromorphicOrderAt (logDeriv g) a = -1 :=
    meromorphicOrderAt_logDeriv_eq_neg_one hAna.meromorphicAt
      (by simpa [horder] using hn0) (by simp [horder])
  have hmul : meromorphicOrderAt ((fun z : ℂ => z) * logDeriv g) a = -1 := by
    convert! (meromorphicOrderAt_mul_of_ne_zero
      (f := logDeriv g) (g := fun z : ℂ => z) analyticAt_id ha).trans hlog using 1
  have heq : normalizedLogDerivative m g =
      (fun _ : ℂ => (m : ℂ)) + (fun z : ℂ => z) * logDeriv g := by
    ext z
    simp only [normalizedLogDerivative, weightedLogDerivative, Pi.add_apply,
      Pi.mul_apply, logDeriv_apply]
    ring
  rw [heq, meromorphicOrderAt_add_eq_right_of_lt (MeromorphicAt.const (m : ℂ) a)]
  · exact hmul
  · rw [hmul]
    exact lt_of_lt_of_le (show (-1 : WithTop ℤ) < 0 from WithTop.coe_lt_coe.mpr (by norm_num))
      analyticAt_const.meromorphicOrderAt_nonneg

/-- Approaching any nonzero zero of the factor sends the actual normalized
logarithmic derivative to infinity. -/
theorem normalizedLogDerivative_tendsto_cobounded_at_zero {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (ha : a ≠ 0) (hga : g a = 0) :
    Tendsto (normalizedLogDerivative m g) (𝓝[≠] a) (Bornology.cobounded ℂ) := by
  apply tendsto_cobounded_of_meromorphicOrderAt_neg
  rw [meromorphicOrderAt_normalizedLogDerivative_at_zero hg hg0 m ha hga]
  exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- The actual spherical logarithmic derivative: zeros of the factor are sent
to infinity, while all other points retain their actual derivative quotient. -/
def sphereLogDerivative (m : ℕ) (g : ℂ → ℂ) (z : ℂ) : OnePoint ℂ :=
  if g z = 0 then ∞ else (normalizedLogDerivative m g z : OnePoint ℂ)

theorem sphereLogDerivative_zero {g : ℂ → ℂ} (hg0 : g 0 ≠ 0) (m : ℕ) :
    sphereLogDerivative m g 0 = ((m : ℂ) : OnePoint ℂ) := by
  simp [sphereLogDerivative, hg0]

/-- The spherical representative of the actual logarithmic derivative is
continuous across all poles, using the proved simple-pole behavior. -/
theorem continuous_sphereLogDerivative {g : ℂ → ℂ} (hg : Entire g) (hg0 : g 0 ≠ 0)
    (m : ℕ) : Continuous (sphereLogDerivative m g) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases hga : g a = 0
  · have ha : a ≠ 0 := by
      intro ha
      exact hg0 (by simpa [ha] using hga)
    have hnear : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 := by
      rcases (hg.analyticAt a).eventually_eq_zero_or_eventually_ne_zero with heq | hne
      · exact False.elim (analyticOrderAt_entire_ne_top hg hg0 a
          (analyticOrderAt_eq_top.mpr heq))
      · exact hne
    have hq := normalizedLogDerivative_tendsto_cobounded_at_zero hg hg0 m ha hga
    have hq' : Tendsto (normalizedLogDerivative m g) (𝓝[≠] a) (coclosedCompact ℂ) := by
      simpa only [coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using hq
    have hlim : Tendsto (fun z => (normalizedLogDerivative m g z : OnePoint ℂ))
        (𝓝[≠] a) (𝓝 (∞ : OnePoint ℂ)) := OnePoint.tendsto_coe_infty.comp hq'
    apply continuousAt_iff_punctured_nhds.mpr
    have heq : (fun z => (normalizedLogDerivative m g z : OnePoint ℂ)) =ᶠ[𝓝[≠] a]
        sphereLogDerivative m g := by
      filter_upwards [hnear] with z hz
      simp [sphereLogDerivative, hz]
    simpa [sphereLogDerivative, hga] using hlim.congr' heq
  · have hnear : ∀ᶠ z in 𝓝 a, g z ≠ 0 :=
      (hg a).continuousAt.eventually (isOpen_ne.mem_nhds hga)
    have hAnaq : AnalyticAt ℂ (normalizedLogDerivative m g) a :=
      analyticAt_const.add ((analyticAt_id.mul (hg.analyticAt a).deriv).div
        (hg.analyticAt a) hga)
    have hcontinuous : ContinuousAt (fun z => (normalizedLogDerivative m g z : OnePoint ℂ)) a :=
      OnePoint.continuous_coe.continuousAt.comp hAnaq.continuousAt
    apply hcontinuous.congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    simp [sphereLogDerivative, hz]

/-- A closed set of common values avoiding the origin value gives a uniform
positive lower bound on both coordinates. This also applies to spherical values. -/
theorem inverse_pairs_coordinates_bounded_below_of_closed_values
    {β : Type*} [TopologicalSpace β] {A B : ℂ → β} {c : β}
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hAc : A 0 = c) (hBc : B 0 = c) {P : Set β} (hP : IsClosed P) (hc : c ∉ P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, ∀ p ∈ P,
      ∀ zw ∈ InversePairs A B s p, ε ≤ ‖zw.1‖ ∧ ε ≤ ‖zw.2‖ := by
  have hnearA : ∀ᶠ z in 𝓝 (0 : ℂ), A z ∉ P :=
    hA.eventually (hP.isOpen_compl.mem_nhds (by simpa [hAc] using hc))
  have hnearB : ∀ᶠ z in 𝓝 (0 : ℂ), B z ∉ P :=
    hB.eventually (hP.isOpen_compl.mem_nhds (by simpa [hBc] using hc))
  obtain ⟨εA, hεA, hAeps⟩ := Metric.eventually_nhds_iff.mp hnearA
  obtain ⟨εB, hεB, hBeps⟩ := Metric.eventually_nhds_iff.mp hnearB
  refine ⟨min εA εB, lt_min hεA hεB, ?_⟩
  intro s p hp zw hzw
  constructor
  · apply le_of_not_gt
    intro hz
    have hnot := hAeps (by simpa only [dist_zero_right] using hz.trans_le (min_le_left _ _))
    exact hnot (by simpa [hzw.2.1] using hp)
  · apply le_of_not_gt
    intro hw
    have hnot := hBeps (by simpa only [dist_zero_right] using hw.trans_le (min_le_right _ _))
    exact hnot (by simpa [hzw.2.2] using hp)

/-- The complete inverse image of a compact target set is compact when the common
value avoids the value at the origin. This is the properness mechanism of the
multiplicative correspondence and includes spherical target values. -/
theorem compact_correspondence_inverse_image
    {β : Type*} [TopologicalSpace β] [T2Space β] {A B : ℂ → β} {c : β}
    (hA : Continuous A) (hB : Continuous B) (hAc : A 0 = c) (hBc : B 0 = c)
    {K : Set (ℂ × β)} (hK : IsCompact K) (havoid : ∀ y ∈ K, y.2 ≠ c) :
    IsCompact {zw : ℂ × ℂ | A zw.1 = B zw.2 ∧ (zw.1 * zw.2, A zw.1) ∈ K} := by
  let P : Set β := Prod.snd '' K
  have hP : IsCompact P := hK.image continuous_snd
  have hc : c ∉ P := by
    rintro ⟨y, hy, heq⟩
    exact havoid y hy heq
  obtain ⟨ε, hε, hcoord⟩ := inverse_pairs_coordinates_bounded_below_of_closed_values
    hA.continuousAt hB.continuousAt hAc hBc hP.isClosed hc
  obtain ⟨S, hS⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  have hmap : Continuous (fun zw : ℂ × ℂ => (zw.1 * zw.2, A zw.1)) :=
    (continuous_fst.mul continuous_snd).prodMk (hA.comp continuous_fst)
  have hclosed : IsClosed {zw : ℂ × ℂ | A zw.1 = B zw.2 ∧ (zw.1 * zw.2, A zw.1) ∈ K} :=
    (isClosed_eq (hA.comp continuous_fst) (hB.comp continuous_snd)).inter
      (hK.isClosed.preimage hmap)
  apply ((isCompact_closedBall (0 : ℂ) (S / ε)).prod
    (isCompact_closedBall (0 : ℂ) (S / ε))).of_isClosed_subset hclosed
  intro zw hzw
  have hp : A zw.1 ∈ P := ⟨(zw.1 * zw.2, A zw.1), hzw.2, rfl⟩
  have hfiber : zw ∈ InversePairs A B (zw.1 * zw.2) (A zw.1) :=
    ⟨rfl, rfl, hzw.1.symm⟩
  obtain ⟨hz, hw⟩ := hcoord (zw.1 * zw.2) (A zw.1) hp zw hfiber
  have hprod : ‖zw.1‖ * ‖zw.2‖ ≤ S := by
    rw [← norm_mul]
    exact hS _ ⟨(zw.1 * zw.2, A zw.1), hzw.2, rfl⟩
  constructor
  · simp only [mem_closedBall, dist_zero_right]
    exact (le_div_iff₀ hε).mpr ((mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans hprod)
  · simp only [mem_closedBall, dist_zero_right]
    exact (le_div_iff₀ hε).mpr ((mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans
      (by simpa [mul_comm] using hprod))

/-- The actual spherical logarithmic correspondence has compact inverse images
for every compact target set avoiding the removable value. -/
theorem compact_sphereLogDerivative_inverse_image {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {K : Set (ℂ × OnePoint ℂ)}
    (hK : IsCompact K) (havoid : ∀ y ∈ K, y.2 ≠ ((m : ℂ) : OnePoint ℂ)) :
    IsCompact {zw : ℂ × ℂ |
      sphereLogDerivative m g zw.1 = sphereLogDerivative m (reflection g) zw.2 ∧
      (zw.1 * zw.2, sphereLogDerivative m g zw.1) ∈ K} := by
  exact compact_correspondence_inverse_image (continuous_sphereLogDerivative hg hg0 m)
    (continuous_sphereLogDerivative (entire_reflection hg) (by simpa [reflection] using hg0) m)
    (sphereLogDerivative_zero hg0 m)
    (sphereLogDerivative_zero (by simpa [reflection] using hg0) m) hK havoid

@[simp] theorem sphereLogDerivative_eq_infty (m : ℕ) (g : ℂ → ℂ) (z : ℂ) :
    sphereLogDerivative m g z = ∞ ↔ g z = 0 := by
  by_cases hz : g z = 0 <;> simp [sphereLogDerivative, hz]

theorem sphereLogDerivative_eq_coe (m : ℕ) (g : ℂ → ℂ) (z p : ℂ) :
    sphereLogDerivative m g z = (p : OnePoint ℂ) ↔
      g z ≠ 0 ∧ normalizedLogDerivative m g z = p := by
  by_cases hz : g z = 0 <;> simp [sphereLogDerivative, hz]

theorem compact_sphereLogDerivative_fiber {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) (s : ℂ) {p : OnePoint ℂ}
    (hp : p ≠ ((m : ℂ) : OnePoint ℂ)) :
    IsCompact (InversePairs (sphereLogDerivative m g)
      (sphereLogDerivative m (reflection g)) s p) := by
  have hcompact := compact_sphereLogDerivative_inverse_image hg hg0 m
    (K := {(s, p)}) isCompact_singleton (by
      intro y hy
      have heq : y = (s, p) := mem_singleton_iff.mp hy
      simpa [heq] using hp)
  convert! hcompact using 1
  ext zw
  simp only [InversePairs, mem_ofPred_eq, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hprod, hA, hB⟩
    exact ⟨hA.trans hB.symm, hprod, hA⟩
  · rintro ⟨heq, hprod, hA⟩
    exact ⟨hprod, hA, heq.symm.trans hA⟩

/-- The actual spherical inverse fibers are finite at every value other than
the common value at zero, including the value infinity. -/
theorem sphereLogDerivative_finite_inverse_pairs {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) {s : ℂ} (hs : s ≠ 0)
    {p : OnePoint ℂ} (hp : p ≠ ((m : ℂ) : OnePoint ℂ)) :
    (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) s p).Finite := by
  induction p using OnePoint.rec with
  | infty =>
    have hcompact := compact_sphereLogDerivative_fiber hg hg0 m s hp
    have hfinite := finite_entire_zeros_in_compact hg hg0 (hcompact.image continuous_fst)
    have hmaps : Set.MapsTo Prod.fst
        (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) s ∞)
        {z : ℂ | z ∈ Prod.fst '' InversePairs (sphereLogDerivative m g)
          (sphereLogDerivative m (reflection g)) s ∞ ∧ g z = 0} := by
      intro zw hzw
      exact ⟨⟨zw, hzw, rfl⟩, (sphereLogDerivative_eq_infty m g zw.1).mp hzw.2.1⟩
    exact Set.Finite.of_injOn hmaps (inverse_pairs_first_injective hs) hfinite
  | coe p =>
    have hpm : p ≠ (m : ℂ) := by
      intro hpm
      exact hp (by rw [hpm])
    apply (normalizedLogDerivative_finite_inverse_pairs hg hg0 m hs hpm).subset
    intro zw hzw
    refine ⟨hzw.1, (sphereLogDerivative_eq_coe m g zw.1 p).mp hzw.2.1 |>.2, ?_⟩
    rw [reflection_normalizedLogDerivative]
    exact (sphereLogDerivative_eq_coe m (reflection g) zw.2 p).mp hzw.2.2 |>.2

/-- Target of the spherical correspondence away from zero products and the
common value at the origin. -/
abbrev SphereCorrespondenceTarget (m : ℕ) :=
  {y : ℂ × OnePoint ℂ // y.1 ≠ 0 ∧ y.2 ≠ ((m : ℂ) : OnePoint ℂ)}

/-- Actual source of the spherical correspondence over the restricted target. -/
abbrev SphereCorrespondenceSource (m : ℕ) (g : ℂ → ℂ) :=
  {zw : ℂ × ℂ // sphereLogDerivative m g zw.1 = sphereLogDerivative m (reflection g) zw.2 ∧
    zw.1 * zw.2 ≠ 0 ∧ sphereLogDerivative m g zw.1 ≠ ((m : ℂ) : OnePoint ℂ)}

/-- The map uses actual values of the spherical logarithmic derivative. -/
def sphereCorrespondenceMap (m : ℕ) (g : ℂ → ℂ) :
    SphereCorrespondenceSource m g → SphereCorrespondenceTarget m :=
  fun zw => ⟨(zw.val.1 * zw.val.2, sphereLogDerivative m g zw.val.1),
    zw.property.2.1, zw.property.2.2⟩

theorem continuous_sphereCorrespondenceMap {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) : Continuous (sphereCorrespondenceMap m g) := by
  apply Continuous.subtype_mk
  exact ((continuous_fst.mul continuous_snd).prodMk
    ((continuous_sphereLogDerivative hg hg0 m).comp continuous_fst)).comp continuous_subtype_val

/-- The actual spherical correspondence is a proper map over the target
omitting the common value and zero product coordinate. -/
theorem isProperMap_sphereCorrespondenceMap {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) : IsProperMap (sphereCorrespondenceMap m g) := by
  have hopen : IsOpen {y : ℂ × OnePoint ℂ | y.1 ≠ 0 ∧ y.2 ≠ ((m : ℂ) : OnePoint ℂ)} :=
    (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)
  have : LocallyCompactSpace (SphereCorrespondenceTarget m) := hopen.locallyCompactSpace
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_sphereCorrespondenceMap hg hg0 m, ?_⟩
  intro K hK
  have hK' : IsCompact (Subtype.val '' K : Set (ℂ × OnePoint ℂ)) :=
    hK.image continuous_subtype_val
  have havoid : ∀ y ∈ (Subtype.val '' K : Set (ℂ × OnePoint ℂ)),
      y.2 ≠ ((m : ℂ) : OnePoint ℂ) := by
    rintro y ⟨x, _, rfl⟩
    exact x.property.2
  have hfull := compact_sphereLogDerivative_inverse_image hg hg0 m hK' havoid
  apply Subtype.isCompact_iff.mpr
  convert! hfull using 1
  ext zw
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property.1, ⟨sphereCorrespondenceMap m g x, hx, rfl⟩⟩
  · rintro ⟨hcor, y, hy, hyeq⟩
    have hprod : zw.1 * zw.2 ≠ 0 := by
      change (zw.1 * zw.2, sphereLogDerivative m g zw.1).1 ≠ 0
      rw [← hyeq]
      exact y.property.1
    have hval : sphereLogDerivative m g zw.1 ≠ ((m : ℂ) : OnePoint ℂ) := by
      change (zw.1 * zw.2, sphereLogDerivative m g zw.1).2 ≠ ((m : ℂ) : OnePoint ℂ)
      rw [← hyeq]
      exact y.property.2
    let x : SphereCorrespondenceSource m g := ⟨zw, hcor, hprod, hval⟩
    refine ⟨x, ?_, rfl⟩
    change sphereCorrespondenceMap m g x ∈ K
    have hmap : sphereCorrespondenceMap m g x = y := Subtype.ext hyeq.symm
    rw [hmap]
    exact hy

/-- Every fiber of the proper spherical correspondence map is finite. -/
theorem sphereCorrespondenceMap_finite_fiber {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) (y : SphereCorrespondenceTarget m) :
    (sphereCorrespondenceMap m g ⁻¹' {y}).Finite := by
  have hfinite := sphereLogDerivative_finite_inverse_pairs hg hg0 m y.property.1 y.property.2
  have hmaps : Set.MapsTo Subtype.val (sphereCorrespondenceMap m g ⁻¹' {y})
      (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) y.val.1 y.val.2) := by
    intro x hx
    have hxeq : sphereCorrespondenceMap m g x = y := mem_singleton_iff.mp hx
    have heq := congrArg Subtype.val hxeq
    have hp : x.val.1 * x.val.2 = y.val.1 := congrArg Prod.fst heq
    have hA : sphereLogDerivative m g x.val.1 = y.val.2 := congrArg Prod.snd heq
    exact ⟨hp, hA, x.property.1.symm.trans hA⟩
  exact Set.Finite.of_injOn hmaps Subtype.val_injective.injOn hfinite

end MaximumModulus
