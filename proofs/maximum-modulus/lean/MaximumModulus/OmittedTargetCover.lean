module

public import MaximumModulus.BoundaryCharts
public import MaximumModulus.FiniteValueCoordinates
public import MaximumModulus.ProductNonconstant
public import MaximumModulus.BranchContinuation
public import MaximumModulus.HighCountInterior

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace MaximumModulus

noncomputable section

/-- Finite continuous germs cannot supply a nearby value from a different central value. -/
theorem finite_germ_central_value_capture {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} (hS : ∀ i, ContinuousAt (S i) 0) (s₀ : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t s : ℂ), ‖t‖ < r → ‖s - s₀‖ < r →
      ∀ i, S i t = s → S i 0 = s₀ := by
  have hevent : ∀ᶠ x : ℂ × ℂ in 𝓝 (0, s₀), ∀ i, S i x.1 = x.2 → S i 0 = s₀ := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : S i 0 = s₀
    · exact Filter.Eventually.of_forall fun _ _ => hi
    · have hsc : ContinuousAt (fun x : ℂ × ℂ => S i x.1) (0, s₀) :=
        (hS i).tendsto.comp (continuous_fst.tendsto (0, s₀))
      have hc : ContinuousAt (fun x : ℂ × ℂ => S i x.1 - x.2) (0, s₀) :=
        hsc.sub continuousAt_snd
      filter_upwards [hc.eventually_ne (sub_ne_zero.mpr hi)] with x hx heq
      exact False.elim (hx (sub_eq_zero.mpr heq))
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r, hr, fun t s ht hs => hlocal (y := (t, s)) ?_⟩
  simpa [Prod.dist_eq, dist_eq_norm, Prod.norm_def] using max_lt ht hs

theorem finite_analytic_germs_closed_radius {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} (hS : ∀ i, AnalyticAt ℂ (S i) 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, AnalyticOnNhd ℂ (S i) (closedBall 0 r) := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i, AnalyticAt ℂ (S i) t :=
    Filter.eventually_all.mpr fun i => (isOpen_analyticAt ℂ (S i)).eventually_mem (hS i)
  obtain ⟨r, hr, hlocal⟩ := nhds_basis_closedBall.mem_iff.mp hevent
  exact ⟨r, hr, fun i t ht => hlocal ht i⟩

/-- All local capture, shrinking and nonverticality inputs at an omitted finite target.
The branch selection and open projection are conclusions of continuation, not fields. -/
structure OmittedHighCountBranchCover (m : ℕ) (g : ℂ → ℂ) (L : ℕ) (s₀ : ℂ) where
  ι : Type
  finite : Finite ι
  N : ℕ
  positiveN : 0 < N
  S : ι → ℂ → ℂ
  δ : ℝ
  positiveRadius : 0 < δ
  analytic : ∀ i, AnalyticOnNhd ℂ (S i) (closedBall 0 δ)
  center : ∀ i, S i 0 = s₀
  nonconstant : ∀ i, ¬∀ᶠ t in 𝓝 (0 : ℂ), S i t = S i 0
  comparisons : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i j : ι, ∀ ω : ℂ, ω ^ N = 1 →
    (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u)
  W : Set (ℂ × ℂ)
  openW : IsOpen W
  memW : (s₀, (m : ℂ)) ∈ W
  cylinder : W ⊆ BranchValueCylinder N (m : ℂ) δ
  branchW : ∀ i, ImageBranch (S i) N (m : ℂ) '' ball 0 δ ⊆ W
  capture : FiniteRegularLogDerivativeHighCount m g L ∩ W ⊆
    ⋃ i, ImageBranch (S i) N (m : ℂ) '' ball 0 δ

instance {m : ℕ} {g : ℂ → ℂ} {L : ℕ} {s₀ : ℂ}
    (C : OmittedHighCountBranchCover m g L s₀) : Finite C.ι := C.finite

/-- The actual bounded-survivor chart construction supplies all omitted-target cover
inputs. Finite families with other central products are discarded using actual continuity. -/
theorem omittedHighCountBranchCover_exists {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    Nonempty (OmittedHighCountBranchCover m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) s₀) := by
  classical
  let bound : ℝ := ‖s₀‖ + 1
  obtain ⟨ε, hε, hfamily⟩ := logDerivative_high_count_omitted_finite_image_cover hg hg0 hnm hfactor
  obtain ⟨ι, hfinite, N, hN, P, hP, _, ⟨ρ, hρ, hvalues⟩, V, hV, hcV, hcapture⟩ := hfamily bound
  have : Finite ι := hfinite
  let S : ι → ℂ → ℂ := fun i t => (P i t).1 * (P i t).2
  have hS : ∀ i, AnalyticAt ℂ (S i) 0 := fun i => (hP i).1.mul (hP i).2
  obtain ⟨r, hr, hcentral⟩ := finite_germ_central_value_capture (fun i => (hS i).continuousAt) s₀
  obtain ⟨rA, hrA, hanalytic⟩ := finite_analytic_germs_closed_radius hS
  obtain ⟨rC, hrC, hcomparisons⟩ := finite_imageBranch_comparisons_radius hS hN
  let κ := {i : ι // S i 0 = s₀}
  let U : Set (ℂ × ℂ) := {y | ‖y.1‖ < bound ∧ ‖y.1 - s₀‖ < r ∧ (y.2 : OnePoint ℂ) ∈ V}
  have hU : IsOpen U :=
    (isOpen_lt continuous_fst.norm continuous_const).inter
      ((isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
        (hV.preimage (OnePoint.continuous_coe.comp continuous_snd)))
  have hcU : (s₀, (m : ℂ)) ∈ U := by
    refine ⟨?_, ?_, hcV⟩
    · dsimp [bound]
      linarith
    · simpa using hr
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i : κ, ImageBranch (S i.val) N (m : ℂ) t ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (ImageBranch (S i.val) N (m : ℂ)) 0 :=
      (hS i.val).continuousAt.prodMk (continuousAt_const.add (continuousAt_id.pow N))
    have hzero : ImageBranch (S i.val) N (m : ℂ) 0 = (s₀, (m : ℂ)) := by
      simp [ImageBranch, i.property, hN.ne']
    have hmem : U ∈ 𝓝 (ImageBranch (S i.val) N (m : ℂ) 0) := by
      rw [hzero]
      exact hU.mem_nhds hcU
    exact hc.eventually hmem
  obtain ⟨rU, hrU, hlocalU⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ : ℝ := min rU (min r (min rC rA))
  have hδ : 0 < δ := lt_min hrU (lt_min hr (lt_min hrC hrA))
  have hδU : δ ≤ rU := min_le_left _ _
  have hδr : δ ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hδC : δ ≤ rC := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδA : δ ≤ rA := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let W : Set (ℂ × ℂ) := U ∩ BranchValueCylinder N (m : ℂ) δ
  have hW : IsOpen W := hU.inter (isOpen_branchValueCylinder N (m : ℂ) δ)
  have hcW : (s₀, (m : ℂ)) ∈ W := by
    refine ⟨hcU, ?_⟩
    simpa [BranchValueCylinder] using pow_pos hδ N
  have hbranchW : ∀ i : κ, ImageBranch (S i.val) N (m : ℂ) '' ball 0 δ ⊆ W := by
    intro i y hy
    obtain ⟨t, ht, rfl⟩ := hy
    have htnorm : ‖t‖ < δ := by simpa only [mem_ball, dist_zero_right] using ht
    refine ⟨hlocalU (by simpa only [dist_zero_right] using htnorm.trans_le hδU) i, ?_⟩
    change ‖(m : ℂ) + t ^ N - (m : ℂ)‖ < δ ^ N
    simpa only [add_sub_cancel_left, norm_pow] using
      pow_lt_pow_left₀ htnorm (norm_nonneg t) hN.ne'
  have hcover : FiniteRegularLogDerivativeHighCount m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) ∩ W ⊆
      ⋃ i : κ, ImageBranch (S i.val) N (m : ℂ) '' ball 0 δ := by
    intro y hy
    have hyhigh : (y.1, (y.2 : OnePoint ℂ)) ∈ LogDerivativeHighCount m g
        (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) := hy.1.1
    have hyU : y ∈ U := hy.2.1
    have hymem := hcapture y.1 y.2 hyhigh hyU.1.le hyU.2.2 δ hδ hy.2.2
    obtain ⟨i, t, ht, heq⟩ := mem_iUnion.mp hymem
    have htnorm : ‖t‖ < δ := by simpa only [mem_ball, dist_zero_right] using ht.1
    have hi : S i 0 = s₀ := hcentral t y.1 (htnorm.trans_le hδr) hyU.2.1 i
      (congrArg Prod.fst heq)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, t, ht.1, heq⟩
  have hnonconstant : ∀ i : κ, ¬∀ᶠ t in 𝓝 (0 : ℂ), S i.val t = S i.val 0 := by
    intro i
    apply logarithmic_pair_product_germ_nonconstant hg hg0 hnm hfactor hN (m : ℂ)
      (hP i.val).1 (hP i.val).2.continuousAt (fun _ => rfl)
    · change S i.val 0 ≠ 0
      rw [i.property]
      exact hs₀
    · filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with t ht
      exact hvalues t (by simpa only [mem_ball, dist_zero_right] using ht) i.val
  refine ⟨⟨κ, inferInstance, N, hN, fun i => S i.val, δ, hδ,
    fun i => (hanalytic i.val).mono (closedBall_subset_closedBall hδA),
    fun i => i.property, hnonconstant, ?_, W, hW, hcW, inter_subset_right,
    hbranchW, hcover⟩⟩
  intro t ht hn i j ω hω
  exact hcomparisons t (ht.trans_le hδC) hn i.val j.val ω hω

/-- At an omitted finite value, the closure selects complete branches of the actual
bounded-survivor family. The interior analytic subbranches are proved, not assumed. -/
theorem OmittedHighCountBranchCover.actual_closure_branches {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {s₀ : ℂ}
    (C : OmittedHighCountBranchCover m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) s₀) :
    ∃ J : Set C.ι,
      (∀ i ∈ J, ImageBranch (C.S i) C.N (m : ℂ) '' ball 0 C.δ ⊆
        closure (FiniteRegularLogDerivativeHighCount m g
          (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0))) ∧
      closure (FiniteRegularLogDerivativeHighCount m g
        (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)) ∩ C.W =
        (⋃ i ∈ J, ImageBranch (C.S i) C.N (m : ℂ) '' ball 0 C.δ) ∩ C.W := by
  apply closure_continues_through_finite_imageBranches C.positiveN (m : ℂ) C.positiveRadius
    C.analytic C.comparisons C.openW C.cylinder C.branchW C.capture
    (fun y hy => finiteRegularLogDerivativeHighCount_omits_common_value m g _ hy)
  intro y hy _ hyvalue
  have hySphere : finiteValueEmbedding y ∈ closure (RegularLogDerivativeHighCount m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)) := by
    change y ∈ finiteValueEmbedding ⁻¹' closure _
    rw [finiteRegularLogDerivativeHighCount_closure]
    exact hy
  obtain ⟨ε, hε, havoid⟩ :=
    regularLogDerivativeHighCount_closure_avoids_small_products hg hg0 hnm hfactor
  have hyproduct : y.1 ≠ 0 := by
    intro hzero
    apply havoid hySphere
    simpa [finiteValueEmbedding, hzero, mem_ball_iff_norm] using pow_pos hε 2
  obtain ⟨T, N, ρ, hN, hρ, hT, hcenter, hsub⟩ :=
    finite_regular_high_count_closure_contains_analytic_branch hg hg0 hnm hfactor
      hyproduct hyvalue hy
  exact ⟨T, N, y.2, ρ, hN, hρ, hT, hcenter, hsub⟩

/-- Actual continuation through the omitted finite value yields open local product
projection of the finite-coordinate high-count closure. -/
theorem finite_regular_high_count_closure_omitted_local_projection_isOpen
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (s₀, (m : ℂ)) ∈ W ∧
      IsOpen (Prod.fst '' (closure (FiniteRegularLogDerivativeHighCount m g
        (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)) ∩ W)) := by
  obtain ⟨C⟩ := omittedHighCountBranchCover_exists hg hg0 hnm hfactor hs₀
  obtain ⟨J, _, heq⟩ := C.actual_closure_branches hg hg0 hnm hfactor
  exact ⟨C.W, C.openW, C.memW,
    finite_imageBranches_local_projection_isOpen (m : ℂ) C.positiveRadius
      (fun i _ => C.analytic i) (fun i _ => C.nonconstant i) C.openW heq⟩

/-- The proved omitted-value continuation transfers to the actual spherical closure. -/
theorem regular_high_count_closure_omitted_local_projection_isOpen
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    ∃ W : Set (ℂ × OnePoint ℂ), IsOpen W ∧ (s₀, ((m : ℂ) : OnePoint ℂ)) ∈ W ∧
      IsOpen (Prod.fst '' (closure (RegularLogDerivativeHighCount m g
        (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)) ∩ W)) := by
  obtain ⟨W, hW, hyW, hproj⟩ :=
    finite_regular_high_count_closure_omitted_local_projection_isOpen hg hg0 hnm hfactor hs₀
  have hproj' : IsOpen (Prod.fst ''
      ((finiteValueEmbedding ⁻¹' closure (RegularLogDerivativeHighCount m g
        (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0))) ∩ W)) := by
    rw [finiteRegularLogDerivativeHighCount_closure]
    exact hproj
  have htransfer := finiteValueEmbedding_open_local_projection hW hproj'
  exact ⟨finiteValueEmbedding '' W, htransfer.1,
    ⟨(s₀, (m : ℂ)), hyW, rfl⟩, htransfer.2⟩

end

end MaximumModulus
