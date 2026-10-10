module

public import MaximumModulus.MaximumStationarity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

noncomputable section

namespace MaximumModulus

theorem norm_le_maxPoint_on_closedBall {f : ℂ → ℂ} (hf : Entire f)
    {r : ℝ} {z : ℂ} (hz : z ∈ MaxPoints f r) {w : ℂ}
    (hw : ‖w‖ ≤ r) : ‖f w‖ ≤ ‖f z‖ := by
  by_cases hr : r = 0
  · have hw0 : w = 0 := norm_eq_zero.mp (by simpa [hr] using hw)
    have hz0 : z = 0 := norm_eq_zero.mp (by simpa [hr] using hz.1)
    simp [hw0, hz0]
  have hrpos : 0 < r := lt_of_le_of_ne (hz.1 ▸ norm_nonneg z) (Ne.symm hr)
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r)
    isBounded_ball hf.diffContOnCl
  · intro v hv
    exact hz.2 v (by simpa [mem_sphere_iff_norm] using frontier_ball_subset_sphere hv)
  · rw [closure_ball (0 : ℂ) hrpos.ne']
    simpa [mem_closedBall_iff_norm] using hw

/-- The actual squared maximum strictly increases for a nonconstant entire function. -/
theorem squaredMaximum_strictMonoOn {f : ℂ → ℂ} (hf : Entire f)
    (hnc : ¬∃ c : ℂ, ∀ z : ℂ, f z = c) :
    StrictMonoOn (squaredMaximum f) (Ioi 0) := by
  intro a ha b hb hab
  obtain ⟨z, hz⟩ := maxPoints_nonempty hf.continuous ha.le
  obtain ⟨w, hw⟩ := maxPoints_nonempty hf.continuous hb.le
  have hle : ‖f z‖ ≤ ‖f w‖ := norm_le_maxPoint_on_closedBall hf hw (hz.1 ▸ hab.le)
  have hlt : ‖f z‖ < ‖f w‖ := by
    apply lt_of_le_of_ne hle
    intro heq
    have hlocal : IsLocalMax (norm ∘ f) z := by
      have hzb : z ∈ ball (0 : ℂ) b := by
        simpa [mem_ball_iff_norm, hz.1] using hab
      apply Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb)
      intro v hv
      have hvn : ‖v‖ < b := by simpa [mem_ball_iff_norm] using hv
      exact (norm_le_maxPoint_on_closedBall hf hw hvn.le).trans_eq heq.symm
    have hevent := Complex.eventually_eq_of_isLocalMax_norm
      (Filter.Eventually.of_forall hf) hlocal
    have heqglobal : f = fun _ => f z :=
      (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
        analyticOnNhd_const hevent
    exact hnc ⟨f z, fun v => congrFun heqglobal v⟩
  rw [squaredMaximum_eq_of_maxPoint hf.continuous hz,
    squaredMaximum_eq_of_maxPoint hf.continuous hw, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by decide : 2 ≠ 0)

/-- Entire functions have a uniform Lipschitz bound for their squared values on
each compact disk. -/
theorem normSq_entire_lipschitz_closedBall {f : ℂ → ℂ} (hf : Entire f) (b : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun z => Complex.normSq (f z))
      (closedBall (0 : ℂ) b) := by
  have hc : ContDiff ℝ 1 f := (hf.contDiff : ContDiff ℂ 1 f).restrict_scalars ℝ
  have hre := Complex.reCLM.contDiff.comp hc
  have him := Complex.imCLM.contDiff.comp hc
  have hsq : ContDiff ℝ 1 (fun z => Complex.normSq (f z)) := by
    convert! (hre.mul hre).add (him.mul him) using 1
  exact hsq.contDiffOn.exists_lipschitzOnWith (by decide) (convex_closedBall _ _)
    (isCompact_closedBall _ _)

theorem squaredMaximum_sub_le_of_normSq_lipschitz_closedBall {f : ℂ → ℂ}
    (hf : Continuous f) {b r s : ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K (fun z => Complex.normSq (f z)) (closedBall (0 : ℂ) b))
    (hr : 0 < r) (hs : 0 < s) (hrb : r ≤ b) (hsb : s ≤ b) :
    squaredMaximum f r - squaredMaximum f s ≤ (K : ℝ) * |r - s| := by
  obtain ⟨z, hz⟩ := maxPoints_nonempty hf hr.le
  let w : ℂ := (s : ℂ) / (r : ℂ) * z
  have hwn : ‖w‖ = s := by
    simp [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hs,
      hz.1, hr.ne']
  have hzball : z ∈ closedBall (0 : ℂ) b := by
    simpa [mem_closedBall_iff_norm, hz.1] using hrb
  have hwball : w ∈ closedBall (0 : ℂ) b := by
    simpa [mem_closedBall_iff_norm, hwn] using hsb
  have hdist : dist z w = |r - s| := by
    rw [dist_eq_norm]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [show z - w = ((r - s : ℝ) : ℂ) / (r : ℂ) * z by
      dsimp [w]
      push_cast
      field_simp]
    simp [-Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      hz.1, hr.ne']
  have hdistle := hK.dist_le_mul z hzball w hwball
  rw [Real.dist_eq, hdist] at hdistle
  rw [squaredMaximum_eq_of_maxPoint hf hz]
  calc
    Complex.normSq (f z) - squaredMaximum f s ≤
        Complex.normSq (f z) - Complex.normSq (f w) :=
      sub_le_sub_left (normSq_le_squaredMaximum hf hwn) _
    _ ≤ |Complex.normSq (f z) - Complex.normSq (f w)| := le_abs_self _
    _ ≤ (K : ℝ) * |r - s| := hdistle

/-- The actual maximum envelope is Lipschitz on every compact positive radius interval. -/
theorem squaredMaximum_lipschitzOn_Icc {f : ℂ → ℂ} (hf : Entire f)
    {a b : ℝ} (ha : 0 < a) :
    ∃ K : ℝ≥0, LipschitzOnWith K (squaredMaximum f) (Icc a b) := by
  obtain ⟨K, hK⟩ := normSq_entire_lipschitz_closedBall hf b
  refine ⟨K, lipschitzOnWith_iff_dist_le_mul.mpr ?_⟩
  intro r hr s hs
  rw [Real.dist_eq, Real.dist_eq]
  have h₁ := squaredMaximum_sub_le_of_normSq_lipschitz_closedBall hf.continuous hK
    (ha.trans_le hr.1) (ha.trans_le hs.1) hr.2 hs.2
  have h₂ := squaredMaximum_sub_le_of_normSq_lipschitz_closedBall hf.continuous hK
    (ha.trans_le hs.1) (ha.trans_le hr.1) hs.2 hr.2
  rw [abs_sub_comm s r] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

/-- Every positive radius interval contains a positive first variation outside
any specified countable exceptional set. -/
theorem exists_positive_envelope_derivative_off_countable {f : ℂ → ℂ}
    (hf : Entire f) (hnc : ¬∃ c : ℂ, ∀ z : ℂ, f z = c)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {S : Set ℝ} (hS : S.Countable) :
    ∃ r ∈ Ioo a b, r ∉ S ∧ DifferentiableAt ℝ (squaredMaximum f) r ∧
      0 < deriv (squaredMaximum f) r := by
  obtain ⟨K, hK⟩ := squaredMaximum_lipschitzOn_Icc hf ha (b := b)
  have hAC : AbsolutelyContinuousOnInterval (squaredMaximum f) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := K)
    simpa [uIcc_of_le hab.le] using hK
  have hmono := squaredMaximum_strictMonoOn hf hnc
  by_contra hnone
  have hno : ∀ r ∈ Ioo a b, r ∉ S → DifferentiableAt ℝ (squaredMaximum f) r →
      deriv (squaredMaximum f) r ≤ 0 := by
    intro r hr hrS hd
    by_contra hn
    exact hnone ⟨r, hr, hrS, hd, lt_of_not_ge hn⟩
  have hae : ∀ᵐ r : ℝ, r ∈ uIcc a b → HasDerivAt (squaredMaximum f) 0 r := by
    filter_upwards [hAC.ae_differentiableAt, hS.ae_notMem MeasureTheory.volume,
      (countable_singleton a).ae_notMem MeasureTheory.volume,
      (countable_singleton b).ae_notMem MeasureTheory.volume] with r hd hrS hra hrb
    intro hr
    have hrcc : r ∈ Icc a b := by simpa [uIcc_of_le hab.le] using hr
    have hra' : r ≠ a := by simpa using hra
    have hrb' : r ≠ b := by simpa using hrb
    have hroo : r ∈ Ioo a b := ⟨lt_of_le_of_ne hrcc.1 (Ne.symm hra'),
      lt_of_le_of_ne hrcc.2 hrb'⟩
    have hrpos : 0 < r := ha.trans hroo.1
    have hnonneg : 0 ≤ derivWithin (squaredMaximum f) (Ioi 0) r :=
      hmono.monotoneOn.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds (Ioi_mem_nhds hrpos)] at hnonneg
    have hzero := le_antisymm (hno r hroo hrS (hd hr)) hnonneg
    simpa [hzero] using (hd hr).hasDerivAt
  obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hae
  have habvalues := hmono ha (ha.trans hab) hab
  have hCa : squaredMaximum f a = C := hC a (by simp)
  have hCb : squaredMaximum f b = C := hC b (by simp)
  exact (ne_of_lt habvalues) (hCa.trans hCb.symm)

end MaximumModulus
