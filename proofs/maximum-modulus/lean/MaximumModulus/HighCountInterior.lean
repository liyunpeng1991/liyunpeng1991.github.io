module

public import MaximumModulus.FiniteTargetCover
public import MaximumModulus.FiniteValueCoordinates
public import MaximumModulus.ProductNonconstant

@[expose] public section

open Set Filter Metric
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- Finite coordinates express the actual regular high-count condition directly. -/
theorem mem_finiteRegularLogDerivativeHighCount_iff (m : ℕ) (g : ℂ → ℂ) (L : ℕ)
    (y : ℂ × ℂ) :
    y ∈ FiniteRegularLogDerivativeHighCount m g L ↔
      y.1 ≠ 0 ∧ y.2 ≠ (m : ℂ) ∧
      (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
        y.1 (y.2 : OnePoint ℂ)).Finite ∧
      L < (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
        y.1 (y.2 : OnePoint ℂ)).ncard ∧ IsSingleValueGraph m g y := by
  change (y.1, (y.2 : OnePoint ℂ)) ∈ RegularLogDerivativeHighCount m g L ↔ _
  constructor
  · rintro ⟨hy, p, hp, hgraph⟩
    have hyeq : y.2 = p := OnePoint.coe_injective hp
    have hne : y.2 ≠ (m : ℂ) := fun h => hy.2.1 (congrArg (fun z : ℂ => (z : OnePoint ℂ)) h)
    exact ⟨hy.1, hne, hy.2.2.1, hy.2.2.2, by simpa only [← hyeq] using hgraph⟩
  · rintro ⟨hs, hp, hfinite, hcount, hgraph⟩
    exact ⟨⟨hs, fun h => hp (OnePoint.coe_injective h), hfinite, hcount⟩,
      y.2, rfl, hgraph⟩

/-- Every constructed physical branch has a genuine nonconstant product germ. -/
theorem FiniteTargetBranchCover.product_germ_nonconstant
    {f g : ℂ → ℂ} {m : ℕ} {s₀ p₀ : ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z)
    (C : FiniteTargetBranchCover m g s₀ p₀) (j : C.Index) :
    ¬∀ᶠ t in 𝓝 (0 : ℂ), C.S j t = C.S j 0 := by
  apply logarithmic_pair_product_germ_nonconstant hg hg0 hnm hfactor C.posN p₀
    (C.analyticA j) (C.analyticB j).continuousAt (C.product j)
  · rw [C.center j]
    exact (C.domainW (s₀, p₀) C.centerW).1
  · filter_upwards [ball_mem_nhds (0 : ℂ) C.posδ] with t ht
    exact C.forward t (by simpa only [mem_ball, dist_zero_right] using ht) j

/-- A regular central fiber cannot be larger than a nearby physical branch fiber.
This uses equality of actual physical collision kernels, not the number of indices. -/
theorem FiniteTargetBranchCover.central_fiber_count_le_branch
    {m : ℕ} {g : ℂ → ℂ} {s₀ p₀ : ℂ} (C : FiniteTargetBranchCover m g s₀ p₀)
    (hregular : IsSingleValueGraph m g (s₀, p₀)) (j : C.Index)
    {t : ℂ} (ht : ‖t‖ < C.δ) (hne : t ≠ 0)
    (hphysical : ∀ i k : C.Index, C.P i t = C.P k t →
      ∀ᶠ u in 𝓝 (0 : ℂ), C.P i u = C.P k u) :
    (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
      s₀ (p₀ : OnePoint ℂ)).Finite ∧
    (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
      s₀ (p₀ : OnePoint ℂ)).ncard ≤
    (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
      (C.S j t) ((p₀ + t ^ C.N : ℂ) : OnePoint ℂ)).ncard := by
  obtain ⟨F, _, _, hgraph⟩ := hregular
  have hS : ∀ i, ContinuousAt (C.S i) 0 :=
    fun i => (C.analyticS i 0 (mem_closedBall_self C.posδ.le)).continuousAt
  have hV : ContinuousAt (fun u : ℂ => p₀ + u ^ C.N) 0 := by fun_prop
  have hbranch : ∀ i, ∀ᶠ u in 𝓝 (0 : ℂ),
      (C.S i u, p₀ + u ^ C.N) ∈ FiniteLogDerivativeImage m g := by
    intro i
    filter_upwards [ball_mem_nhds (0 : ℂ) C.posδ] with u hu
    have hforward := C.forward u (by simpa only [mem_ball, dist_zero_right] using hu) i
    exact ⟨C.P i u, C.product i u, hforward.1, hforward.2⟩
  have hgraph' : ∀ᶠ y in 𝓝 (s₀, p₀ + (0 : ℂ) ^ C.N),
      y ∈ FiniteLogDerivativeImage m g → y.1 = F y.2 := by
    simpa only [zero_pow C.posN.ne', add_zero] using hgraph.mono (fun y hy => hy.mp)
  have hcover : InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
      s₀ (p₀ : OnePoint ℂ) ⊆ (fun i => C.P i 0) '' univ := by
    have hfiber := C.fiber_eq 0 (by simpa using C.posδ) j
    simp only [C.center j, zero_pow C.posN.ne', add_zero] at hfiber
    rw [hfiber]
    exact image_mono (subset_univ _)
  have hcentral := central_fiber_count_le_of_total_graph hS hV C.center hbranch
    hgraph' hcover hphysical j
  have hclass : {i : C.Index | C.S i t = C.S j t} = ProductGermClass C.S j := by
    ext i
    exact by simpa only [ProductGermClass, mem_ofPred_eq, one_mul] using
      C.comparisons t ht hne i j 1 (by simp)
  refine ⟨hcentral.1, ?_⟩
  rw [C.fiber_eq t ht j, hclass]
  exact hcentral.2

/-- The actual regular high-count locus is locally sandwiched between the
punctured and full images of exactly the branches with large physical count. -/
theorem FiniteTargetBranchCover.high_count_selected_sandwich
    {m : ℕ} {g : ℂ → ℂ} {s₀ p₀ : ℂ} (C : FiniteTargetBranchCover m g s₀ p₀) (L : ℕ) :
    ∃ ρ : ℝ, ∃ W : Set (ℂ × ℂ), ∃ J : Set C.Index,
      0 < ρ ∧ ρ ≤ C.δ ∧ IsOpen W ∧ (s₀, p₀) ∈ W ∧
      W ⊆ BranchValueCylinder C.N p₀ ρ ∧
      (∀ j, ImageBranch (C.S j) C.N p₀ '' ball 0 ρ ⊆ W) ∧
      (⋃ j ∈ J, ImageBranch (C.S j) C.N p₀ '' (ball 0 ρ \ {0})) ⊆
        FiniteRegularLogDerivativeHighCount m g L ∧
      FiniteRegularLogDerivativeHighCount m g L ∩ W ⊆
        ⋃ j ∈ J, ImageBranch (C.S j) C.N p₀ '' ball 0 ρ := by
  obtain ⟨ε, d, hε, hεδ, hcount⟩ := C.physical_count_radius
  obtain ⟨εP, hεP, hPcmp⟩ := finite_physical_pair_comparisons_radius C.analyticA C.analyticB
  let ρ := min ε εP
  have hρ : 0 < ρ := lt_min hε hεP
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρP : ρ ≤ εP := min_le_right _ _
  have hρδ : ρ ≤ C.δ := hρε.trans hεδ
  let W := C.W ∩ BranchValueCylinder C.N p₀ ρ
  let J : Set C.Index := {j | L < d j}
  have hW : IsOpen W := C.openW.inter (isOpen_branchValueCylinder C.N p₀ ρ)
  have hcenterW : (s₀, p₀) ∈ W := ⟨C.centerW, by
    change ‖p₀ - p₀‖ < ρ ^ C.N
    simpa only [sub_self, norm_zero] using pow_pos hρ C.N⟩
  have hbranchW : ∀ j, ImageBranch (C.S j) C.N p₀ '' ball 0 ρ ⊆ W := by
    rintro j z ⟨t, ht, rfl⟩
    have hnorm : ‖t‖ < ρ := by simpa only [mem_ball, dist_zero_right] using ht
    refine ⟨C.branchW j t (hnorm.trans_le hρδ), ?_⟩
    change ‖p₀ + t ^ C.N - p₀‖ < ρ ^ C.N
    simpa only [add_sub_cancel_left, norm_pow] using
      pow_lt_pow_left₀ hnorm (norm_nonneg _) C.posN.ne'
  have hlower : (⋃ j ∈ J, ImageBranch (C.S j) C.N p₀ '' (ball 0 ρ \ {0})) ⊆
      FiniteRegularLogDerivativeHighCount m g L := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    obtain ⟨hjJ, t, ht, rfl⟩ := mem_iUnion.mp hj
    have hnorm : ‖t‖ < ρ := by simpa only [mem_ball, dist_zero_right] using ht.1
    have hne : t ≠ 0 := by simpa using ht.2
    have hphysical := hcount t (hnorm.trans_le hρε) hne j
    have hdomain := C.domainW _ (C.branchW j t (hnorm.trans_le hρδ))
    apply (mem_finiteRegularLogDerivativeHighCount_iff m g L _).mpr
    refine ⟨hdomain.1, hdomain.2, hphysical.1, ?_,
      C.regular_at_punctured_branch j (hnorm.trans_le hρδ) hne⟩
    change L < (InversePairs (sphereLogDerivative m g)
      (sphereLogDerivative m (reflection g)) (C.S j t)
        ((p₀ + t ^ C.N : ℂ) : OnePoint ℂ)).ncard
    rw [hphysical.2]
    exact hjJ
  have hupper : FiniteRegularLogDerivativeHighCount m g L ∩ W ⊆
      ⋃ j ∈ J, ImageBranch (C.S j) C.N p₀ '' ball 0 ρ := by
    intro z hz
    have hhigh := (mem_finiteRegularLogDerivativeHighCount_iff m g L z).mp hz.1
    have himage : z ∈ FiniteLogDerivativeImage m g := by
      exact (Set.ncard_pos hhigh.2.2.1).mp
        (lt_of_le_of_lt (Nat.zero_le L) hhigh.2.2.2.1)
    obtain ⟨j, t, ht, heq⟩ := mem_iUnion.mp ((C.imageCover z hz.2.1).mp himage)
    have hnorm : ‖t‖ < ρ := by
      have hpower : ‖t‖ ^ C.N < ρ ^ C.N := by
        simpa only [← heq, BranchValueCylinder, mem_ofPred_eq, ImageBranch,
          add_sub_cancel_left, norm_pow] using hz.2.2
      exact lt_of_pow_lt_pow_left₀ C.N hρ.le hpower
    have hjJ : j ∈ J := by
      by_cases ht0 : t = 0
      · have hzcenter : z = (s₀, p₀) := by
          rw [← heq, ht0]
          simp only [ImageBranch, C.center j, zero_pow C.posN.ne', add_zero]
        have hcentralRegular : IsSingleValueGraph m g (s₀, p₀) := by
          simpa only [hzcenter] using hhigh.2.2.2.2
        let u : ℂ := (ρ / 2 : ℝ)
        have hunorm : ‖u‖ < ρ := by
          simpa only [u, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hρ)] using
            half_lt_self hρ
        have hune : u ≠ 0 := by
          change ((ρ / 2 : ℝ) : ℂ) ≠ 0
          exact_mod_cast (half_pos hρ).ne'
        have hcentralCount := C.central_fiber_count_le_branch hcentralRegular j
          (hunorm.trans_le hρδ) hune
          (fun i k heq => (hPcmp u (hunorm.trans_le hρP) hune i k).mp heq)
        have hgeneric := hcount u (hunorm.trans_le hρε) hune j
        have hlarge : L < (InversePairs (sphereLogDerivative m g)
            (sphereLogDerivative m (reflection g)) s₀ (p₀ : OnePoint ℂ)).ncard := by
          simpa only [hzcenter] using hhigh.2.2.2.1
        exact lt_of_lt_of_le hlarge (hcentralCount.2.trans_eq hgeneric.2)
      · have hgeneric := hcount t (hnorm.trans_le hρε) ht0 j
        have hlarge : L < (InversePairs (sphereLogDerivative m g)
            (sphereLogDerivative m (reflection g)) (C.S j t)
              ((p₀ + t ^ C.N : ℂ) : OnePoint ℂ)).ncard := by
          simpa only [← heq, ImageBranch] using hhigh.2.2.2.1
        change L < d j
        exact hlarge.trans_le hgeneric.2.le
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjJ, t,
      by simpa only [mem_ball, dist_zero_right] using hnorm, heq⟩⟩
  exact ⟨ρ, W, J, hρ, hρδ, hW, hcenterW, fun _ hz => hz.2,
    hbranchW, hlower, hupper⟩

/-- The closure of the actual finite regular high-count locus is a union of
selected complete raw branches in a neighborhood of each permitted finite target. -/
theorem FiniteTargetBranchCover.high_count_local_closure_branches
    {m : ℕ} {g : ℂ → ℂ} {s₀ p₀ : ℂ} (C : FiniteTargetBranchCover m g s₀ p₀) (L : ℕ) :
    ∃ ρ : ℝ, ∃ W : Set (ℂ × ℂ), ∃ J : Set C.Index,
      0 < ρ ∧ ρ ≤ C.δ ∧ IsOpen W ∧ (s₀, p₀) ∈ W ∧
      closure (FiniteRegularLogDerivativeHighCount m g L) ∩ W =
        (⋃ j ∈ J, ImageBranch (C.S j) C.N p₀ '' ball 0 ρ) ∩ W ∧
      ∀ j ∈ J, ImageBranch (C.S j) C.N p₀ '' ball 0 ρ ⊆
        closure (FiniteRegularLogDerivativeHighCount m g L) := by
  obtain ⟨ρ, W, J, hρ, hρδ, hW, hcenterW, hWcyl, hbranchW, hlower, hupper⟩ :=
    C.high_count_selected_sandwich L
  have hclosure := closure_of_local_selected_imageBranches (Set.toFinite J) C.posN p₀ hρ
    (fun j _ => (C.analyticS j).continuousOn.mono (closedBall_subset_closedBall hρδ))
    hW hWcyl (fun _ hz => hlower hz.1) hupper
  refine ⟨ρ, W, J, hρ, hρδ, hW, hcenterW, hclosure, ?_⟩
  intro j hj z hz
  have hmem : z ∈ closure (FiniteRegularLogDerivativeHighCount m g L) ∩ W := by
    rw [hclosure]
    exact ⟨mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hz⟩⟩, hbranchW j hz⟩
  exact hmem.1

/-- Every interior finite point of the actual high-count closure carries a
whole analytic power branch centered at that point. -/
theorem finite_regular_high_count_closure_contains_analytic_branch
    {f g : ℂ → ℂ} {m L : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z)
    {s₀ p₀ : ℂ} (hs₀ : s₀ ≠ 0) (hp₀ : p₀ ≠ (m : ℂ))
    (hy : (s₀, p₀) ∈ closure (FiniteRegularLogDerivativeHighCount m g L)) :
    ∃ (T : ℂ → ℂ) (N : ℕ) (ρ : ℝ),
      0 < N ∧ 0 < ρ ∧ AnalyticAt ℂ T 0 ∧ ImageBranch T N p₀ 0 = (s₀, p₀) ∧
      ImageBranch T N p₀ '' ball 0 ρ ⊆ closure (FiniteRegularLogDerivativeHighCount m g L) := by
  obtain ⟨C⟩ := finiteTargetBranchCover_exists hg hg0 hnm hfactor hs₀ hp₀
  obtain ⟨ρ, W, J, hρ, _, _, hcenterW, hclosure, hbranch⟩ :=
    C.high_count_local_closure_branches L
  have hselected : (s₀, p₀) ∈ ⋃ j ∈ J, ImageBranch (C.S j) C.N p₀ '' ball 0 ρ :=
    (hclosure ▸ (show (s₀, p₀) ∈ closure (FiniteRegularLogDerivativeHighCount m g L) ∩ W from
      ⟨hy, hcenterW⟩)).1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hselected
  obtain ⟨hjJ, _⟩ := mem_iUnion.mp hj
  refine ⟨C.S j, C.N, ρ, C.posN, hρ,
    C.analyticS j 0 (mem_closedBall_self C.posδ.le), ?_, hbranch j hjJ⟩
  simp only [ImageBranch, C.center j, zero_pow C.posN.ne', add_zero]

/-- The finite part of the actual high-count closure has open product
projection locally, proved from its selected nonconstant physical branches. -/
theorem finite_regular_high_count_closure_local_projection_isOpen
    {f g : ℂ → ℂ} {m L : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z)
    {s₀ p₀ : ℂ} (hs₀ : s₀ ≠ 0) (hp₀ : p₀ ≠ (m : ℂ)) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (s₀, p₀) ∈ W ∧
      IsOpen (Prod.fst '' (closure (FiniteRegularLogDerivativeHighCount m g L) ∩ W)) := by
  obtain ⟨C⟩ := finiteTargetBranchCover_exists hg hg0 hnm hfactor hs₀ hp₀
  obtain ⟨ρ, W, J, hρ, hρδ, hW, hcenterW, hWcyl, _, hlower, hupper⟩ :=
    C.high_count_selected_sandwich L
  refine ⟨W, hW, hcenterW, ?_⟩
  apply local_selected_imageBranches_closure_projection_isOpen (Set.toFinite J) C.posN p₀ hρ
    (fun j _ => (C.analyticS j).mono (closedBall_subset_closedBall hρδ))
    (fun j _ => C.product_germ_nonconstant hg hg0 hnm hfactor j)
    hW hWcyl (fun _ hz => hlower hz.1) hupper

/-- The local open projection at finite values transfers to the actual
spherical closure through the ordinary finite-value open embedding. -/
theorem regular_high_count_closure_finite_local_projection_isOpen
    {f g : ℂ → ℂ} {m L : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z)
    {s₀ p₀ : ℂ} (hs₀ : s₀ ≠ 0) (hp₀ : p₀ ≠ (m : ℂ)) :
    ∃ W : Set (ℂ × OnePoint ℂ), IsOpen W ∧ (s₀, (p₀ : OnePoint ℂ)) ∈ W ∧
      IsOpen (Prod.fst '' (closure (RegularLogDerivativeHighCount m g L) ∩ W)) := by
  obtain ⟨W, hW, hyW, hproj⟩ :=
    finite_regular_high_count_closure_local_projection_isOpen hg hg0 hnm hfactor hs₀ hp₀
  have hproj' : IsOpen (Prod.fst ''
      ((finiteValueEmbedding ⁻¹' closure (RegularLogDerivativeHighCount m g L)) ∩ W)) := by
    rw [finiteRegularLogDerivativeHighCount_closure]
    exact hproj
  have htransfer := finiteValueEmbedding_open_local_projection hW hproj'
  exact ⟨finiteValueEmbedding '' W, htransfer.1, ⟨(s₀, p₀), hyW, rfl⟩, htransfer.2⟩

end MaximumModulus
