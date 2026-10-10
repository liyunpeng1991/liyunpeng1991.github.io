module

public import MaximumModulus.InfinityCharts
public import MaximumModulus.DuplicateSafeCount

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace MaximumModulus

noncomputable section

/-- A reciprocal image graph at a nonzero parameter is a genuine ordinary finite-value
graph after analytic inversion of its value coordinate. -/
theorem singleValueGraph_of_reciprocal_graph {m : ℕ} {g : ℂ → ℂ} {s t : ℂ}
    (ht : t ≠ 0) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F t) (hcenter : F t = s)
    (hgraph : ∀ᶠ y in 𝓝 (s, t), y ∈ ReciprocalLogDerivativeImage m g ↔ y.1 = F y.2) :
    IsSingleValueGraph m g (s, t⁻¹) := by
  have hp : t⁻¹ ≠ 0 := inv_ne_zero ht
  let Ψ : ℂ × ℂ → ℂ × ℂ := fun z => (z.1, z.2⁻¹)
  have hΨ : ContinuousAt Ψ (s, t⁻¹) :=
    continuousAt_fst.prodMk ((continuousAt_inv₀ hp).comp (f := Prod.snd) (x := (s, t⁻¹)) continuousAt_snd)
  have hΨcenter : Ψ (s, t⁻¹) = (s, t) := by simp [Ψ]
  have hnear : ∀ᶠ y in 𝓝 (s, t⁻¹),
      Ψ y ∈ ReciprocalLogDerivativeImage m g ↔ (Ψ y).1 = F (Ψ y).2 :=
    by
      have hto := hΨ.tendsto
      rw [hΨcenter] at hto
      exact hto.eventually hgraph
  refine ⟨fun p => F p⁻¹, ?_, ?_, ?_⟩
  · have hInv : AnalyticAt ℂ (fun p : ℂ => p⁻¹) t⁻¹ := by
      convert! (analyticAt_id.inv hp) using 1
    exact hF.comp_of_eq hInv (inv_inv t)
  · simpa only [inv_inv] using hcenter
  · filter_upwards [hnear, (continuous_snd.tendsto (s, t⁻¹)).eventually
      (eventually_ne_nhds hp)] with y hy hyp
    have hvalue : infinityValue y.2⁻¹ = (y.2 : OnePoint ℂ) := by
      simp [infinityValue, hyp]
    simpa only [Ψ, ReciprocalLogDerivativeImage, FiniteLogDerivativeImage, mem_ofPred_eq, hvalue] using hy

theorem InfinityTargetBranchCover.regular_at_punctured_branch
    {m : ℕ} {g : ℂ → ℂ} {s₀ : ℂ} (C : InfinityTargetBranchCover m g s₀)
    (j : C.Index) {t : ℂ} (ht : ‖t‖ < C.δ) (hne : t ≠ 0) :
    IsSingleValueGraph m g (C.S j t, t⁻¹) := by
  let : Finite C.Index := C.finite_index
  have hanalytic : ∀ i, AnalyticOnNhd ℂ (C.S i) (ball 0 C.δ) :=
    fun i => (C.analyticS i).mono ball_subset_closedBall
  obtain ⟨F, hF, hcenter, hgraph⟩ := finite_imageBranches_noncentral_image_is_graph
    (by decide : 0 < (1 : ℕ)) 0 C.posδ hanalytic
    (fun i => (C.analyticS i).continuousOn) C.comparisons j ht hne
  apply singleValueGraph_of_reciprocal_graph hne
    (by simpa [ImageBranch] using hF) (by simpa [ImageBranch] using hcenter)
  have hgraph' : ∀ᶠ y in 𝓝 (C.S j t, t),
      y ∈ ⋃ i : C.Index, ImageBranch (C.S i) 1 0 '' ball 0 C.δ ↔ y.1 = F y.2 := by
    simpa [ImageBranch] using hgraph
  filter_upwards [hgraph', C.openW.mem_nhds (by simpa [ImageBranch] using C.branchW j t ht)]
    with y hy hyW
  exact (C.imageCover y hyW).trans hy

theorem InfinityTargetBranchCover.physical_count_radius
    {m : ℕ} {g : ℂ → ℂ} {s₀ : ℂ} (C : InfinityTargetBranchCover m g s₀) :
    ∃ ε : ℝ, ∃ d : C.Index → ℕ, 0 < ε ∧ ε ≤ C.δ ∧
      ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 → ∀ j : C.Index,
        (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
          (C.S j t) (infinityValue t)).Finite ∧
        (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
          (C.S j t) (infinityValue t)).ncard = d j := by
  let : Finite C.Index := C.finite_index
  apply finite_analytic_physical_inversePairs_count_radius C.analyticA C.analyticB
    (fun j => C.analyticS j 0 (mem_closedBall_self C.posδ.le)) C.posδ
  · intro t ht _ j
    exact ⟨(C.forward t ht j).1, (C.forward t ht j).2, C.product j t⟩
  · intro t ht _ j zw hzw
    rw [C.fiber_eq t ht j] at hzw
    obtain ⟨k, _, hk⟩ := hzw
    exact ⟨k, hk⟩

/-- Pole-centered product branches cannot be vertical. The proof moves to an actual
nonzero reciprocal parameter, where both physical coordinates are regular, and applies
the proved exclusion of local reciprocal symmetry. -/
theorem InfinityTargetBranchCover.product_germ_nonconstant
    {f g : ℂ → ℂ} {m : ℕ} {s₀ : ℂ} (C : InfinityTargetBranchCover m g s₀)
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) (j : C.Index) :
    ¬∀ᶠ t in 𝓝 (0 : ℂ), C.S j t = C.S j 0 := by
  intro hconst
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hconst
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ),
      AnalyticAt ℂ (fun u => (C.P j u).1) t ∧
      AnalyticAt ℂ (fun u => (C.P j u).2) t ∧ ‖t‖ < ε ∧ ‖t‖ < C.δ := by
    filter_upwards [(C.analyticA j).eventually_analyticAt, (C.analyticB j).eventually_analyticAt,
      ball_mem_nhds (0 : ℂ) hε, ball_mem_nhds (0 : ℂ) C.posδ] with t hA hB he hδ
    exact ⟨hA, hB, by simpa [mem_ball_iff_norm] using he, by simpa [mem_ball_iff_norm] using hδ⟩
  have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (AnalyticAt ℂ (fun u => (C.P j u).1) t ∧
        AnalyticAt ℂ (fun u => (C.P j u).2) t ∧ ‖t‖ < ε ∧ ‖t‖ < C.δ) ∧ t ≠ 0 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
    exact ⟨ht, by simpa using hn⟩
  obtain ⟨t₀, ht₀, ht₀n⟩ := hevent.exists
  have ht₀δ : ‖t₀‖ < C.δ := ht₀.2.2.2
  have hft := C.forward t₀ ht₀δ j
  have hfinitevalue : infinityValue t₀ = ((t₀⁻¹ : ℂ) : OnePoint ℂ) := by simp [infinityValue, ht₀n]
  have hga : g (C.P j t₀).1 ≠ 0 :=
    ((sphereLogDerivative_eq_coe m g (C.P j t₀).1 t₀⁻¹).mp (hft.1.trans hfinitevalue)).1
  have hgb : reflection g (C.P j t₀).2 ≠ 0 :=
    ((sphereLogDerivative_eq_coe m (reflection g) (C.P j t₀).2 t₀⁻¹).mp
      (hft.2.trans hfinitevalue)).1
  have hprodne : (C.P j t₀).1 * (C.P j t₀).2 ≠ 0 := by
    rw [C.product j t₀]
    exact (C.domainW _ (C.branchW j t₀ ht₀δ)).1
  have hparameter : ∀ᶠ t in 𝓝 t₀, ‖t‖ < C.δ := by
    have hb : ∀ᶠ t in 𝓝 t₀, t ∈ ball (0 : ℂ) C.δ :=
      isOpen_ball.mem_nhds (by simpa [mem_ball_iff_norm] using ht₀δ)
    filter_upwards [hb] with t ht
    simpa [mem_ball_iff_norm] using ht
  have hfirstne : ¬∀ᶠ t in 𝓝 t₀, (C.P j t).1 = (C.P j t₀).1 := by
    intro hfirst
    have heq : ∀ᶠ t in 𝓝[≠] t₀, t = t₀ ∧ t ≠ t₀ := by
      filter_upwards [hfirst.filter_mono nhdsWithin_le_nhds,
        hparameter.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hz hδ hne
      have hq : infinityValue t = infinityValue t₀ := by
        rw [← (C.forward t hδ j).1, hz, hft.1]
      exact ⟨infinityValue_injective hq, by simpa using hne⟩
    obtain ⟨t, heq, hne⟩ := heq.exists
    exact hne heq
  have hvalue : ∀ᶠ t in 𝓝 t₀,
      sphereLogDerivative m g (C.P j t).1 = sphereLogDerivative m (reflection g) (C.P j t).2 :=
    hparameter.mono fun t ht => (C.forward t ht j).1.trans (C.forward t ht j).2.symm
  have hproduct : ∀ᶠ t in 𝓝 t₀, (C.P j t).1 * (C.P j t).2 = C.S j 0 := by
    filter_upwards [isOpen_ball.mem_nhds (show t₀ ∈ ball (0 : ℂ) ε from by
      simpa [mem_ball_iff_norm] using ht₀.2.2.1)] with t ht
    rw [C.product j t]
    exact hlocal (by simpa [dist_zero_right] using ht)
  have hcenter : (C.P j t₀).1 * (C.P j t₀).2 = C.S j 0 := by
    rw [C.product j t₀]
    exact hlocal (by simpa [dist_zero_right] using ht₀.2.2.1)
  exact no_constant_product_spherical_regular_pair_germ hg hg0 hnm hfactor ht₀.1
    ht₀.2.1.continuousAt hfirstne (left_ne_zero_of_mul hprodne) hga hgb hvalue hcenter hproduct

def ReciprocalRegularLogDerivativeHighCount (m : ℕ) (g : ℂ → ℂ) (L : ℕ) : Set (ℂ × ℂ) :=
  infinityValueEmbedding ⁻¹' RegularLogDerivativeHighCount m g L

theorem reciprocalRegularLogDerivativeHighCount_omits_zero
    (m : ℕ) (g : ℂ → ℂ) (L : ℕ) {z : ℂ × ℂ}
    (hz : z ∈ ReciprocalRegularLogDerivativeHighCount m g L) : z.2 ≠ 0 := by
  intro hzero
  obtain ⟨p, hp, _⟩ := hz.2
  simp [infinityValueEmbedding, infinityValue, hzero] at hp

/-- Infinity itself is absent from the regular locus. Its punctured branches are
selected exactly by their constant actual physical count. -/
theorem InfinityTargetBranchCover.high_count_selected_sandwich
    {m : ℕ} {g : ℂ → ℂ} {s₀ : ℂ} (C : InfinityTargetBranchCover m g s₀) (L : ℕ) :
    ∃ ρ : ℝ, ∃ W : Set (ℂ × ℂ), ∃ J : Set C.Index,
      0 < ρ ∧ ρ ≤ C.δ ∧ IsOpen W ∧ (s₀, (0 : ℂ)) ∈ W ∧
      W ⊆ BranchValueCylinder 1 0 ρ ∧
      (∀ j, ImageBranch (C.S j) 1 0 '' ball 0 ρ ⊆ W) ∧
      (⋃ j ∈ J, ImageBranch (C.S j) 1 0 '' (ball 0 ρ \ {0})) ⊆
        ReciprocalRegularLogDerivativeHighCount m g L ∧
      ReciprocalRegularLogDerivativeHighCount m g L ∩ W ⊆
        ⋃ j ∈ J, ImageBranch (C.S j) 1 0 '' ball 0 ρ := by
  obtain ⟨ρ, d, hρ, hρδ, hcount⟩ := C.physical_count_radius
  let W := C.W ∩ BranchValueCylinder 1 0 ρ
  let J : Set C.Index := {j | L < d j}
  have hW : IsOpen W := C.openW.inter (isOpen_branchValueCylinder 1 0 ρ)
  have hcenterW : (s₀, (0 : ℂ)) ∈ W := ⟨C.centerW, by simpa [BranchValueCylinder] using hρ⟩
  have hbranchW : ∀ j, ImageBranch (C.S j) 1 0 '' ball 0 ρ ⊆ W := by
    rintro j z ⟨t, ht, rfl⟩
    have hnorm : ‖t‖ < ρ := by simpa [mem_ball_iff_norm] using ht
    refine ⟨C.branchW j t (hnorm.trans_le hρδ), ?_⟩
    simpa [ImageBranch, BranchValueCylinder] using hnorm
  have hlower : (⋃ j ∈ J, ImageBranch (C.S j) 1 0 '' (ball 0 ρ \ {0})) ⊆
      ReciprocalRegularLogDerivativeHighCount m g L := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    obtain ⟨hjJ, t, ht, rfl⟩ := mem_iUnion.mp hj
    have hnorm : ‖t‖ < ρ := by simpa [mem_ball_iff_norm] using ht.1
    have hne : t ≠ 0 := by simpa using ht.2
    have hc := hcount t hnorm hne j
    have hdomain := C.domainW _ (C.branchW j t (hnorm.trans_le hρδ))
    have hdom : C.S j t ≠ 0 ∧ infinityValue t ≠ ((m : ℂ) : OnePoint ℂ) := by
      simpa [ImageBranch] using hdomain
    have hlarge : L < (InversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) (C.S j t) (infinityValue t)).ncard := by
      rw [hc.2]
      exact hjJ
    have hE : (C.S j t, infinityValue t) ∈ RegularLogDerivativeHighCount m g L :=
      ⟨⟨hdom.1, hdom.2, hc.1, hlarge⟩, t⁻¹, by simp [infinityValue, hne],
        C.regular_at_punctured_branch j (hnorm.trans_le hρδ) hne⟩
    simpa [ReciprocalRegularLogDerivativeHighCount, infinityValueEmbedding, ImageBranch] using hE
  have hupper : ReciprocalRegularLogDerivativeHighCount m g L ∩ W ⊆
      ⋃ j ∈ J, ImageBranch (C.S j) 1 0 '' ball 0 ρ := by
    intro z hz
    have htn := reciprocalRegularLogDerivativeHighCount_omits_zero m g L hz.1
    have hhigh := hz.1.1
    have himage : z ∈ ReciprocalLogDerivativeImage m g :=
      (Set.ncard_pos hhigh.2.2.1).mp (lt_of_le_of_lt (Nat.zero_le L) hhigh.2.2.2)
    obtain ⟨j, t, ht, heq⟩ := mem_iUnion.mp ((C.imageCover z hz.2.1).mp himage)
    have hnorm : ‖t‖ < ρ := by
      simpa [← heq, BranchValueCylinder, ImageBranch] using hz.2.2
    have htne : t ≠ 0 := by
      have htval : z.2 = t := by simpa [ImageBranch] using congrArg Prod.snd heq.symm
      exact htval ▸ htn
    have hc := hcount t hnorm htne j
    have hjJ : j ∈ J := by
      have hlarge : L < (InversePairs (sphereLogDerivative m g)
          (sphereLogDerivative m (reflection g)) (C.S j t) (infinityValue t)).ncard := by
        simpa [← heq, infinityValueEmbedding, ImageBranch] using hhigh.2.2.2
      exact hlarge.trans_le hc.2.le
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjJ, t,
      by simpa [mem_ball_iff_norm] using hnorm, heq⟩⟩
  exact ⟨ρ, W, J, hρ, hρδ, hW, hcenterW, fun _ hz => hz.2, hbranchW, hlower, hupper⟩

/-- The actual closure has open local product projection at every nonzero product
point over infinity. All selected branches and all counts arise from the actual maps. -/
theorem regularLogDerivativeHighCount_open_local_projection_at_infinity
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) (L : ℕ) {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    ∃ V : Set (ℂ × OnePoint ℂ), IsOpen V ∧ (s₀, OnePoint.infty) ∈ V ∧
      IsOpen (Prod.fst '' (closure (RegularLogDerivativeHighCount m g L) ∩ V)) := by
  obtain ⟨C⟩ := infinityTargetBranchCover_exists hg hg0 hs₀
  obtain ⟨ρ, W, J, hρ, hρδ, hW, hcenterW, hWcyl, _, hlower, hupper⟩ :=
    C.high_count_selected_sandwich L
  have hopen : IsOpen (Prod.fst '' (closure (ReciprocalRegularLogDerivativeHighCount m g L) ∩ W)) :=
    local_selected_imageBranches_closure_projection_isOpen (Set.toFinite J)
      (by decide : 0 < (1 : ℕ)) 0 hρ
      (fun j _ => (C.analyticS j).mono (closedBall_subset_closedBall hρδ))
      (fun j _ => C.product_germ_nonconstant hg hg0 hnm hfactor j)
      hW hWcyl (fun _ hz => hlower hz.1) hupper
  have hopen' : IsOpen (Prod.fst ''
      ((infinityValueEmbedding ⁻¹' closure (RegularLogDerivativeHighCount m g L)) ∩ W)) := by
    rw [infinityValueEmbedding_preimage_closure]
    exact hopen
  obtain ⟨hV, hproj⟩ := infinityValueEmbedding_open_local_projection hW hopen'
  refine ⟨infinityValueEmbedding '' W, hV, ?_, hproj⟩
  exact ⟨(s₀, (0 : ℂ)), hcenterW, by simp [infinityValueEmbedding, infinityValue]⟩

end

end MaximumModulus
