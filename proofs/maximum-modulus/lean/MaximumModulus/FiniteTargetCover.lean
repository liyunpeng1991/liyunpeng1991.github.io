module

public import MaximumModulus.GlobalCharts
public import MaximumModulus.FiniteImageGraphs
public import MaximumModulus.HighCountLocus
public import MaximumModulus.DuplicateSafeCount
public import MaximumModulus.PairNonvertical

@[expose] public section

open Set Filter Metric
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- Every small finite value has a power parameter in the corresponding small disk. -/
theorem exists_small_power_parameter {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    {p p₀ : ℂ} (hp : ‖p - p₀‖ < δ ^ N) :
    ∃ t : ℂ, ‖t‖ < δ ∧ p₀ + t ^ N = p := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (p - p₀) hN
  refine ⟨t, ?_, ?_⟩
  · apply lt_of_pow_lt_pow_left₀ N hδ.le
    simpa [← norm_pow, ht] using hp
  · rw [ht]
    ring

/-- An open neighborhood in the restricted spherical target pulls back to an open
neighborhood of its finite-value representative. -/
theorem finiteTarget_capture_neighborhood {m : ℕ} {y : SphereCorrespondenceTarget m}
    {p₀ : ℂ} (hp₀ : y.val.2 = (p₀ : OnePoint ℂ))
    {V : Set (SphereCorrespondenceTarget m)} (hV : IsOpen V) (hy : y ∈ V) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (y.val.1, p₀) ∈ W ∧
      ∀ z ∈ W, ∃ hz : z.1 ≠ 0 ∧ (z.2 : OnePoint ℂ) ≠ ((m : ℂ) : OnePoint ℂ),
        (⟨(z.1, (z.2 : OnePoint ℂ)), hz⟩ : SphereCorrespondenceTarget m) ∈ V := by
  have hdomain : IsOpen {z : ℂ × OnePoint ℂ |
      z.1 ≠ 0 ∧ z.2 ≠ ((m : ℂ) : OnePoint ℂ)} :=
    (isClosed_singleton.isOpen_compl.preimage continuous_fst).inter
      (isClosed_singleton.isOpen_compl.preimage continuous_snd)
  let L : ℂ × ℂ → ℂ × OnePoint ℂ := fun z => (z.1, (z.2 : OnePoint ℂ))
  have hL : Continuous L := continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)
  let W := L ⁻¹' (Subtype.val '' V)
  have hW : IsOpen W := (hdomain.isOpenMap_subtype_val V hV).preimage hL
  refine ⟨W, hW, ?_, ?_⟩
  · exact ⟨y, hy, Prod.ext rfl hp₀⟩
  · intro z hz
    obtain ⟨q, hq, heq⟩ := hz
    have heq' : q.val = (z.1, (z.2 : OnePoint ℂ)) := heq
    have hprop : z.1 ≠ 0 ∧ (z.2 : OnePoint ℂ) ≠ ((m : ℂ) : OnePoint ℂ) := by
      change (z.1, (z.2 : OnePoint ℂ)).1 ≠ 0 ∧
        (z.1, (z.2 : OnePoint ℂ)).2 ≠ ((m : ℂ) : OnePoint ℂ)
      rw [← heq']
      exact q.property
    refine ⟨hprop, ?_⟩
    have hsub : (⟨(z.1, (z.2 : OnePoint ℂ)), hprop⟩ : SphereCorrespondenceTarget m) = q :=
      Subtype.ext heq'.symm
    rw [hsub]
    exact hq

/-- A chart captures the central value too: both root coordinates must be zero. -/
theorem RegularSpherePairChart.capture_central_pair {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    {x' : SphereCorrespondenceSource m g} (hx' : x' ∈ C.source)
    (hvalue : sphereLogDerivative m g x'.val.1 = (p₀ : OnePoint ℂ)) :
    x'.val = x.val := by
  have hA : (C.eA x'.val.1) ^ C.kA = 0 := by
    have heq := OnePoint.coe_injective ((C.valueA _ hx'.1).symm.trans hvalue)
    exact add_left_cancel (heq.trans (add_zero p₀).symm)
  have hB : (C.eB x'.val.2) ^ C.kB = 0 := by
    have heq := OnePoint.coe_injective
      ((C.valueB _ hx'.2).symm.trans (x'.property.1.symm.trans hvalue))
    exact add_left_cancel (heq.trans (add_zero p₀).symm)
  have hz : C.eA x'.val.1 = 0 := (pow_eq_zero_iff C.posA.ne').mp hA
  have hw : C.eB x'.val.2 = 0 := (pow_eq_zero_iff C.posB.ne').mp hB
  apply Prod.ext
  · calc
      x'.val.1 = C.eA.symm (C.eA x'.val.1) := (C.eA.left_inv hx'.1).symm
      _ = x.val.1 := by rw [hz, C.inverseCenterA]
  · calc
      x'.val.2 = C.eB.symm (C.eB x'.val.2) := (C.eB.left_inv hx'.2).symm
      _ = x.val.2 := by rw [hw, C.inverseCenterB]

/-- Complete chart capture includes the central parameter as well as the punctured disk. -/
theorem regularSphereRootFamily_capture_all_parameters {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val)
    {N : ℕ} (hN : 0 < N) (lA lB : SphereCentralFiber m g y → ℕ)
    (horders : ∀ i, 0 < lA i ∧ 0 < lB i ∧ N = (C i).kA * lA i ∧ N = (C i).kB * lB i)
    {V : Set (SphereCorrespondenceTarget m)}
    (hcapture : ∀ x : SphereCorrespondenceSource m g, sphereCorrespondenceMap m g x ∈ V →
      ∃ i : SphereCentralFiber m g y, x ∈ (C i).source)
    {t : ℂ} {x : SphereCorrespondenceSource m g}
    (hx : sphereCorrespondenceMap m g x ∈ V)
    (hv : sphereLogDerivative m g x.val.1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ)) :
    ∃ j : RegularSphereRootIndex C, regularSphereRootPair C lA lB j t = x.val := by
  obtain ⟨i, hi⟩ := hcapture x hx
  by_cases ht : t = 0
  · have hvalue : sphereLogDerivative m g x.val.1 = (p₀ : OnePoint ℂ) := by
      simpa only [ht, zero_pow hN.ne', add_zero] using hv
    have hcentral := (C i).capture_central_pair hi hvalue
    let j : RegularSphereRootIndex C := ⟨i, ⟨(1, 1), by simp [RootPairIndices]⟩⟩
    refine ⟨j, ?_⟩
    change (C i).rootPair (lA i) (lB i) (1, 1) t = x.val
    rw [ht, (C i).rootPair_zero (horders i).1 (horders i).2.1]
    exact hcentral.symm
  · obtain ⟨η, hη, hpair⟩ := (C i).capture_rootPair
      (horders i).2.2.1 (horders i).2.2.2 ht hi hv
    exact ⟨⟨i, ⟨η, hη⟩⟩, hpair⟩

/-- Every raw branch is centered at the original target product. -/
theorem regularSphereRootProduct_zero {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val)
    (lA lB : SphereCentralFiber m g y → ℕ)
    (hA : ∀ i, 0 < lA i) (hB : ∀ i, 0 < lB i) (j : RegularSphereRootIndex C) :
    regularSphereRootProduct C lA lB j 0 = y.val.1 := by
  change ((C j.1).rootPair (lA j.1) (lB j.1) j.2.val 0).1 *
    ((C j.1).rootPair (lA j.1) (lB j.1) j.2.val 0).2 = y.val.1
  rw [(C j.1).rootPair_zero (hA j.1) (hB j.1)]
  exact congrArg (fun q : SphereCorrespondenceTarget m => q.val.1) j.1.property

/-- A finite raw branch cover built from the actual logarithmic-derivative fibers.
The family may contain duplicate physical indices; the fiber is its actual image set. -/
structure FiniteTargetBranchCover (m : ℕ) (g : ℂ → ℂ) (s₀ p₀ : ℂ) where
  Index : Type
  finite_index : Finite Index
  N : ℕ
  posN : 0 < N
  δ : ℝ
  posδ : 0 < δ
  P : Index → ℂ → ℂ × ℂ
  S : Index → ℂ → ℂ
  product : ∀ j t, (P j t).1 * (P j t).2 = S j t
  analyticA : ∀ j, AnalyticAt ℂ (fun t => (P j t).1) 0
  analyticB : ∀ j, AnalyticAt ℂ (fun t => (P j t).2) 0
  analyticS : ∀ j, AnalyticOnNhd ℂ (S j) (closedBall 0 δ)
  center : ∀ j, S j 0 = s₀
  forward : ∀ t : ℂ, ‖t‖ < δ → ∀ j,
    sphereLogDerivative m g (P j t).1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
    sphereLogDerivative m (reflection g) (P j t).2 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ)
  W : Set (ℂ × ℂ)
  openW : IsOpen W
  centerW : (s₀, p₀) ∈ W
  domainW : ∀ z ∈ W, z.1 ≠ 0 ∧ z.2 ≠ (m : ℂ)
  Wcylinder : W ⊆ BranchValueCylinder N p₀ δ
  branchW : ∀ j t, ‖t‖ < δ → ImageBranch (S j) N p₀ t ∈ W
  imageCover : ∀ z ∈ W,
    z ∈ FiniteLogDerivativeImage m g ↔
      z ∈ ⋃ j, ImageBranch (S j) N p₀ '' ball 0 δ
  fiber_eq : ∀ t : ℂ, ‖t‖ < δ → ∀ j,
    InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
      (S j t) ((p₀ + t ^ N : ℂ) : OnePoint ℂ) =
        (fun k => P k t) '' {k | S k t = S j t}
  comparisons : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i j, ∀ ω : ℂ, ω ^ N = 1 →
    (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u)

attribute [instance] FiniteTargetBranchCover.finite_index

/-- The actual proper correspondence has a constructed finite raw image cover near
 every finite target away from the omitted value. No image-cover assumption is used. -/
theorem finiteTargetBranchCover_exists {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z)
    {s₀ p₀ : ℂ} (hs₀ : s₀ ≠ 0) (hp₀ : p₀ ≠ (m : ℂ)) :
    Nonempty (FiniteTargetBranchCover m g s₀ p₀) := by
  classical
  let y : SphereCorrespondenceTarget m := ⟨(s₀, (p₀ : OnePoint ℂ)), hs₀,
    fun h => hp₀ (OnePoint.coe_injective h)⟩
  obtain ⟨hfinite, C, V, hV, hy, hcapture⟩ :=
    sphereCorrespondence_regular_chart_capture hg hg0 hnm hfactor y p₀ rfl
  let : Finite (SphereCentralFiber m g y) := hfinite
  obtain ⟨N, hN, hdiv⟩ := finite_orders_common_power (fun i => (C i).kA)
    (fun i => (C i).kB) (fun i => (C i).posA) (fun i => (C i).posB)
  choose lA lB hA hB hN_A hN_B using hdiv
  have horders : ∀ i, 0 < lA i ∧ 0 < lB i ∧ N = (C i).kA * lA i ∧ N = (C i).kB * lB i :=
    fun i => ⟨hA i, hB i, hN_A i, hN_B i⟩
  let ι := RegularSphereRootIndex C
  let P := regularSphereRootPair C lA lB
  let S := regularSphereRootProduct C lA lB
  have hS : ∀ j : ι, AnalyticAt ℂ (S j) 0 :=
    fun j => (C j.1).analytic_rootProduct (hA j.1) (hB j.1) j.2.val
  have hcenter : ∀ j : ι, S j 0 = s₀ :=
    regularSphereRootProduct_zero C lA lB hA hB
  obtain ⟨W₀, hW₀, hyW₀, hWcapture⟩ := finiteTarget_capture_neighborhood (m := m)
    (y := y) rfl hV hy
  obtain ⟨ε₁, hε₁, hvalues⟩ := regularSphereRootFamily_values_radius C hN lA lB horders hp₀
  have hWbranch : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j : ι, ImageBranch (S j) N p₀ t ∈ W₀ := by
    apply Filter.eventually_all.mpr
    intro j
    have hto : Tendsto (ImageBranch (S j) N p₀) (𝓝 0) (𝓝 (s₀, p₀)) := by
      have hc : ContinuousAt (fun t : ℂ => (S j t, p₀ + t ^ N)) 0 :=
        (hS j).continuousAt.prodMk
          (continuous_const.continuousAt.add (continuous_id.pow N).continuousAt)
      change Tendsto (fun t : ℂ => (S j t, p₀ + t ^ N)) (𝓝 0) (𝓝 (s₀, p₀))
      convert! hc.tendsto using 1
      simp only [hcenter j, zero_pow hN.ne', add_zero]
    exact hto.eventually (hW₀.mem_nhds hyW₀)
  obtain ⟨ε₂, hε₂, hbranch⟩ := Metric.eventually_nhds_iff.mp hWbranch
  have hnearAnalytic : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j : ι, AnalyticAt ℂ (S j) t :=
    Filter.eventually_all.mpr fun j => (hS j).eventually_analyticAt
  obtain ⟨ε₃, hε₃, hlocalAnalytic⟩ := Metric.eventually_nhds_iff.mp hnearAnalytic
  obtain ⟨ε₄, hε₄, hcmp⟩ := finite_imageBranch_comparisons_radius hS hN
  let δ := min ε₁ (min ε₂ (min (ε₃ / 2) ε₄))
  have hδ : 0 < δ := lt_min hε₁ (lt_min hε₂ (lt_min (half_pos hε₃) hε₄))
  have hδ₁ : δ ≤ ε₁ := min_le_left _ _
  have hδ₂ : δ ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃ : δ < ε₃ := lt_of_le_of_lt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    (half_lt_self hε₃)
  have hδ₄ : δ ≤ ε₄ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let W := W₀ ∩ BranchValueCylinder N p₀ δ
  have hW : IsOpen W := hW₀.inter (isOpen_branchValueCylinder N p₀ δ)
  have hyW : (s₀, p₀) ∈ W := ⟨hyW₀, by
    change ‖p₀ - p₀‖ < δ ^ N
    simpa only [sub_self, norm_zero] using pow_pos hδ N⟩
  have hbranchW : ∀ j : ι, ∀ t : ℂ, ‖t‖ < δ → ImageBranch (S j) N p₀ t ∈ W := by
    intro j t ht
    refine ⟨hbranch (by simpa only [dist_zero_right] using ht.trans_le hδ₂) j, ?_⟩
    change ‖p₀ + t ^ N - p₀‖ < δ ^ N
    simpa only [add_sub_cancel_left, norm_pow] using pow_lt_pow_left₀ ht (norm_nonneg _) hN.ne'
  have hphysicalCapture : ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ W,
      z.2 = p₀ + t ^ N → ∀ zw ∈ InversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) z.1 (z.2 : OnePoint ℂ),
          ∃ j : ι, P j t = zw := by
    intro t _ z hz hv zw hzw
    obtain ⟨hzprop, hzV⟩ := hWcapture z hz.1
    let q : SphereCorrespondenceTarget m := ⟨(z.1, (z.2 : OnePoint ℂ)), hzprop⟩
    let x : SphereCorrespondenceSource m g := ⟨zw,
      hzw.2.1.trans hzw.2.2.symm,
      fun heq => hzprop.1 (hzw.1.symm.trans heq),
      fun heq => hzprop.2 (hzw.2.1.symm.trans heq)⟩
    have hxq : sphereCorrespondenceMap m g x = q :=
      Subtype.ext (Prod.ext hzw.1 hzw.2.1)
    have hxV : sphereCorrespondenceMap m g x ∈ V := hxq ▸ hzV
    have hvalue : sphereLogDerivative m g x.val.1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) := by
      exact hzw.2.1.trans (congrArg (fun p : ℂ => (p : OnePoint ℂ)) hv)
    exact regularSphereRootFamily_capture_all_parameters C hN lA lB horders hcapture hxV hvalue
  have hcover : ∀ z ∈ W, z ∈ FiniteLogDerivativeImage m g ↔
      z ∈ ⋃ j : ι, ImageBranch (S j) N p₀ '' ball 0 δ := by
    intro z hz
    constructor
    · intro himage
      obtain ⟨zw, hzw⟩ := himage
      obtain ⟨t, ht, hv⟩ := exists_small_power_parameter hN hδ hz.2
      obtain ⟨j, hj⟩ := hphysicalCapture t ht z hz hv.symm zw hzw
      apply mem_iUnion.mpr
      refine ⟨j, t, by simpa only [mem_ball, dist_zero_right] using ht, ?_⟩
      apply Prod.ext
      · change (P j t).1 * (P j t).2 = z.1
        rw [hj]
        exact hzw.1
      · exact hv
    · intro himage
      obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.mp himage
      have hv := hvalues t (by
        exact (show ‖t‖ < δ by simpa only [mem_ball, dist_zero_right] using ht).trans_le hδ₁) j
      exact ⟨P j t, rfl, hv.1, hv.2.1⟩
  refine ⟨⟨ι, inferInstance, N, hN, δ, hδ, P, S, fun j t => rfl,
    ?_, ?_, ?_, hcenter, ?_, W, hW, hyW, ?_, (fun _ hz => hz.2), hbranchW, hcover, ?_, ?_⟩⟩
  · exact fun j => (regularSphereRootPair_analytic C lA lB hA hB j).1
  · exact fun j => (regularSphereRootPair_analytic C lA lB hA hB j).2
  · intro j t ht
    have hnorm : ‖t‖ ≤ δ := by simpa only [mem_closedBall, dist_zero_right] using ht
    exact hlocalAnalytic (by simpa only [dist_zero_right] using hnorm.trans_lt hδ₃) j
  · intro t ht j
    exact ⟨(hvalues t (ht.trans_le hδ₁) j).1, (hvalues t (ht.trans_le hδ₁) j).2.1⟩
  · intro z hz
    obtain ⟨hprop, _⟩ := hWcapture z hz.1
    exact ⟨hprop.1, fun heq => hprop.2 (congrArg (fun p : ℂ => (p : OnePoint ℂ)) heq)⟩
  · intro t ht j
    ext zw
    constructor
    · intro hzw
      have hz := hbranchW j t ht
      obtain ⟨k, hk⟩ := hphysicalCapture t ht (ImageBranch (S j) N p₀ t) hz rfl zw hzw
      refine ⟨k, ?_, hk⟩
      change (P k t).1 * (P k t).2 = S j t
      rw [hk]
      exact hzw.1
    · rintro ⟨k, hk, rfl⟩
      have hv := hvalues t (ht.trans_le hδ₁) k
      exact ⟨hk, hv.1, hv.2.1⟩
  · exact fun t ht => hcmp t (ht.trans_le hδ₄)

/-- Every noncentral point of the constructed cover is a regular point of the
entire actual finite target image, including all physical chart branches. -/
theorem FiniteTargetBranchCover.regular_at_punctured_branch
    {m : ℕ} {g : ℂ → ℂ} {s₀ p₀ : ℂ} (C : FiniteTargetBranchCover m g s₀ p₀)
    (j : C.Index) {t : ℂ} (ht : ‖t‖ < C.δ) (hne : t ≠ 0) :
    IsSingleValueGraph m g (ImageBranch (C.S j) C.N p₀ t) := by
  let : Finite C.Index := C.finite_index
  have hanalytic : ∀ i, AnalyticOnNhd ℂ (C.S i) (ball 0 C.δ) :=
    fun i => (C.analyticS i).mono ball_subset_closedBall
  obtain ⟨F, hF, hcenter, hgraph⟩ := finite_imageBranches_noncentral_image_is_graph C.posN p₀
    C.posδ hanalytic (fun i => (C.analyticS i).continuousOn) C.comparisons j ht hne
  refine ⟨F, hF, hcenter, ?_⟩
  filter_upwards [hgraph, C.openW.mem_nhds (C.branchW j t ht)] with y hy hyW
  exact (C.imageCover y hyW).trans hy

/-- Physical fiber counts on the constructed branches are constant on a smaller
punctured disk. Duplicate chart indices are counted through their physical image. -/
theorem FiniteTargetBranchCover.physical_count_radius
    {m : ℕ} {g : ℂ → ℂ} {s₀ p₀ : ℂ} (C : FiniteTargetBranchCover m g s₀ p₀) :
    ∃ ε : ℝ, ∃ d : C.Index → ℕ, 0 < ε ∧ ε ≤ C.δ ∧
      ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 → ∀ j : C.Index,
        (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
          (C.S j t) ((p₀ + t ^ C.N : ℂ) : OnePoint ℂ)).Finite ∧
        (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
          (C.S j t) ((p₀ + t ^ C.N : ℂ) : OnePoint ℂ)).ncard = d j := by
  let : Finite C.Index := C.finite_index
  apply finite_analytic_physical_inversePairs_count_radius C.analyticA C.analyticB
    (fun j => C.analyticS j 0 (mem_closedBall_self C.posδ.le)) C.posδ
  · intro t ht _ j
    exact ⟨(C.forward t ht j).1, (C.forward t ht j).2, C.product j t⟩
  · intro t ht _ j zw hzw
    rw [C.fiber_eq t ht j] at hzw
    obtain ⟨k, _, hk⟩ := hzw
    exact ⟨k, hk⟩

end MaximumModulus
