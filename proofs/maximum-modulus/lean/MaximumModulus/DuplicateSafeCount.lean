module

public import MaximumModulus.BranchCollision
public import MaximumModulus.SmallFibers

@[expose] public section

/-!
# Counts of physical finite families, allowing duplicate chart indices

The count is always the cardinality of an actual image of physical pairs. Equality
of the pair collision kernels, rather than injectivity of the chart index family,
is sufficient to make this count constant on a punctured parameter disk.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- A finer collision kernel cannot have fewer distinct image values. -/
theorem ncard_image_le_of_kernel_imp {ι α β : Type*} {J : Set ι} (hJ : J.Finite)
    (f : ι → α) (g : ι → β)
    (hkernel : ∀ i ∈ J, ∀ j ∈ J, f i = f j → g i = g j) :
    (g '' J).ncard ≤ (f '' J).ncard := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  let _ : Nonempty ι := ⟨i₀⟩
  let F : β → α := fun y => f (Function.invFunOn g J y)
  have hmaps : ∀ y ∈ g '' J, F y ∈ f '' J := by
    intro y hy
    exact ⟨_, Function.invFunOn_mem hy, rfl⟩
  have hinj : InjOn F (g '' J) := by
    intro y hy y' hy' heq
    have hk := hkernel _ (Function.invFunOn_mem hy) _
      (Function.invFunOn_mem hy') heq
    simpa only [Function.invFunOn_eq hy, Function.invFunOn_eq hy'] using hk
  exact Set.ncard_le_ncard_of_injOn F hmaps hinj (hJ.image f)

/-- Identical pairwise collisions give identical finite image cardinalities. -/
theorem ncard_image_eq_of_kernel_iff {ι α β : Type*} {J : Set ι} (hJ : J.Finite)
    (f : ι → α) (g : ι → β)
    (hkernel : ∀ i ∈ J, ∀ j ∈ J, f i = f j ↔ g i = g j) :
    (f '' J).ncard = (g '' J).ncard := by
  apply Nat.le_antisymm
  · exact ncard_image_le_of_kernel_imp hJ g f fun i hi j hj => (hkernel i hi j hj).mpr
  · exact ncard_image_le_of_kernel_imp hJ f g fun i hi j hj => (hkernel i hi j hj).mp

/-- Persistent product collisions determine a finite index class. -/
def ProductGermClass {ι : Type*} (S : ι → ℂ → ℂ) (i : ι) : Set ι :=
  {j | ∀ᶠ u in 𝓝 (0 : ℂ), S j u = S i u}

/-- Both physical coordinates can be stabilized simultaneously. -/
theorem finite_physical_pair_comparisons_radius {ι : Type*} [Finite ι]
    {P : ι → ℂ → ℂ × ℂ}
    (hA : ∀ i, AnalyticAt ℂ (fun t => (P i t).1) 0)
    (hB : ∀ i, AnalyticAt ℂ (fun t => (P i t).2) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 → ∀ i j : ι,
      (P i t = P j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), P i u = P j u) := by
  obtain ⟨εA, hεA, hAclass⟩ := finite_imageBranch_classes_radius hA
  obtain ⟨εB, hεB, hBclass⟩ := finite_imageBranch_classes_radius hB
  refine ⟨min εA εB, lt_min hεA hεB, ?_⟩
  intro t ht hn i j
  have hAc := Set.ext_iff.mp (hAclass t (ht.trans_le (min_le_left _ _)) hn j) i
  have hBc := Set.ext_iff.mp (hBclass t (ht.trans_le (min_le_right _ _)) hn j) i
  simp only [Set.mem_ofPred_eq] at hAc hBc
  constructor
  · intro hp
    filter_upwards [hAc.mp (congrArg Prod.fst hp), hBc.mp (congrArg Prod.snd hp)] with u ha hb
    exact Prod.ext ha hb
  · intro hgerm
    apply Prod.ext
    · exact hAc.mpr (hgerm.mono fun u hu => congrArg Prod.fst hu)
    · exact hBc.mpr (hgerm.mono fun u hu => congrArg Prod.snd hu)

/-- The actual physical image count in each persistent product class is constant
on a small punctured disk, even when several chart indices represent the same pair. -/
theorem finite_physical_class_count_radius {ι : Type*} [Finite ι]
    {P : ι → ℂ → ℂ × ℂ} {S : ι → ℂ → ℂ}
    (hA : ∀ i, AnalyticAt ℂ (fun t => (P i t).1) 0)
    (hB : ∀ i, AnalyticAt ℂ (fun t => (P i t).2) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t u : ℂ, ‖t‖ < ε → t ≠ 0 → ‖u‖ < ε → u ≠ 0 →
      ∀ i : ι,
        ((fun j => P j t) '' ProductGermClass S i).Finite ∧
        ((fun j => P j t) '' ProductGermClass S i).ncard =
          ((fun j => P j u) '' ProductGermClass S i).ncard := by
  obtain ⟨ε, hε, hcmp⟩ := finite_physical_pair_comparisons_radius hA hB
  refine ⟨ε, hε, ?_⟩
  intro t u ht htn hu hun i
  have hJ : (ProductGermClass S i).Finite := Set.toFinite _
  refine ⟨hJ.image _, ncard_image_eq_of_kernel_iff hJ _ _ ?_⟩
  intro j _ k _
  exact (hcmp t ht htn j k).trans (hcmp u hu hun j k).symm

/-- The center can merge physical pairs, but cannot create new distinct pairs
inside a persistent class. Finiteness is explicit on both sides. -/
theorem center_physical_class_count_le {ι : Type*} [Finite ι]
    {P : ι → ℂ → ℂ × ℂ} {S : ι → ℂ → ℂ}
    {t : ℂ}
    (hcmp : ∀ i j : ι, P i t = P j t → ∀ᶠ u in 𝓝 (0 : ℂ), P i u = P j u)
    (i : ι) :
    ((fun j => P j 0) '' ProductGermClass S i).Finite ∧
    ((fun j => P j t) '' ProductGermClass S i).Finite ∧
    ((fun j => P j 0) '' ProductGermClass S i).ncard ≤
      ((fun j => P j t) '' ProductGermClass S i).ncard := by
  have hJ : (ProductGermClass S i).Finite := Set.toFinite _
  refine ⟨hJ.image _, hJ.image _, ncard_image_le_of_kernel_imp hJ _ _ ?_⟩
  intro j _ k _ hjk
  exact (hcmp j k hjk).self_of_nhds

/-- An exact physical family description of a fiber only requires complete
forward validity and capture. Duplicate indices are harmless because the right
side is an image set of actual pairs. -/
theorem inversePairs_eq_physical_family_image {ι β : Type*}
    {A B : ℂ → β} {P : ι → ℂ × ℂ} {S : ι → ℂ} {p : β}
    (hforward : ∀ i, A (P i).1 = p ∧ B (P i).2 = p ∧ (P i).1 * (P i).2 = S i)
    (i : ι)
    (hcapture : ∀ zw ∈ InversePairs A B (S i) p, ∃ j : ι, P j = zw) :
    InversePairs A B (S i) p = P '' {j : ι | S j = S i} := by
  ext zw
  constructor
  · intro hzw
    obtain ⟨j, hj⟩ := hcapture zw hzw
    refine ⟨j, ?_, hj⟩
    have hprod := (hforward j).2.2
    rw [hj] at hprod
    exact hprod.symm.trans hzw.1
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(hforward j).2.2.trans hj, (hforward j).1, (hforward j).2.1⟩

/-- Finite analytic families give constant actual inverse-pair counts on every
punctured image branch. The enumeration hypotheses involve the original maps,
and no injectivity or abstract degree assumption is required. -/
theorem finite_analytic_physical_inversePairs_count_radius {ι β : Type*} [Finite ι]
    {A B : ℂ → β} {P : ι → ℂ → ℂ × ℂ} {S : ι → ℂ → ℂ} {V : ℂ → β}
    (hA : ∀ i, AnalyticAt ℂ (fun t => (P i t).1) 0)
    (hB : ∀ i, AnalyticAt ℂ (fun t => (P i t).2) 0)
    (hS : ∀ i, AnalyticAt ℂ (S i) 0) {δ : ℝ} (hδ : 0 < δ)
    (hforward : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i : ι,
      A (P i t).1 = V t ∧ B (P i t).2 = V t ∧ (P i t).1 * (P i t).2 = S i t)
    (hcapture : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i : ι,
      ∀ zw ∈ InversePairs A B (S i t) (V t), ∃ j : ι, P j t = zw) :
    ∃ ε : ℝ, ∃ d : ι → ℕ, 0 < ε ∧ ε ≤ δ ∧
      ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 → ∀ i : ι,
        (InversePairs A B (S i t) (V t)).Finite ∧
        (InversePairs A B (S i t) (V t)).ncard = d i := by
  obtain ⟨εP, hεP, hcount⟩ := finite_physical_class_count_radius (S := S) hA hB
  obtain ⟨εS, hεS, hclass⟩ := finite_imageBranch_classes_radius hS
  let ε := min δ (min εP εS)
  have hε : 0 < ε := lt_min hδ (lt_min hεP hεS)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεP' : ε ≤ εP := (min_le_right _ _).trans (min_le_left _ _)
  have hεS' : ε ≤ εS := (min_le_right _ _).trans (min_le_right _ _)
  let t₀ : ℂ := (ε / 2 : ℝ)
  have ht₀ : ‖t₀‖ < ε := by
    simpa only [t₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)] using half_lt_self hε
  have ht₀n : t₀ ≠ 0 := by
    change ((ε / 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (half_pos hε))
  let d : ι → ℕ := fun i => ((fun j => P j t₀) '' ProductGermClass S i).ncard
  refine ⟨ε, d, hε, hεδ, ?_⟩
  intro t ht hn i
  have himage := inversePairs_eq_physical_family_image
    (hforward t (ht.trans_le hεδ) hn) i (hcapture t (ht.trans_le hεδ) hn i)
  have hindices := hclass t (ht.trans_le hεS') hn i
  change {j | S j t = S i t} = ProductGermClass S i at hindices
  rw [himage, hindices]
  exact hcount t t₀ (ht.trans_le hεP') hn (ht₀.trans_le hεP') ht₀n i

/-- A smooth total image forces all branches centered at its point to have
the same product germ. The graph condition is about the actual total image. -/
theorem productGermClass_eq_univ_of_total_graph {ι : Type*}
    {S : ι → ℂ → ℂ} {V : ℂ → ℂ} {Y : Set (ℂ × ℂ)} {s₀ : ℂ}
    (hS : ∀ j, ContinuousAt (S j) 0) (hV : ContinuousAt V 0)
    (hcenter : ∀ j, S j 0 = s₀)
    (hbranch : ∀ j, ∀ᶠ t in 𝓝 (0 : ℂ), (S j t, V t) ∈ Y)
    {F : ℂ → ℂ}
    (hgraph : ∀ᶠ y in 𝓝 (s₀, V 0), y ∈ Y → y.1 = F y.2)
    (i : ι) : ProductGermClass S i = univ := by
  have hvalue : ∀ j, ∀ᶠ t in 𝓝 (0 : ℂ), S j t = F (V t) := by
    intro j
    have htend : Tendsto (fun t => (S j t, V t)) (𝓝 0) (𝓝 (s₀, V 0)) := by
      have hct := (hS j).prodMk hV
      change Tendsto (fun t => (S j t, V t)) (𝓝 0) (𝓝 (S j 0, V 0)) at hct
      simpa only [hcenter j] using hct
    filter_upwards [htend.eventually hgraph, hbranch j] with t hg hb
    exact hg hb
  ext j
  simp only [ProductGermClass, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  filter_upwards [hvalue j, hvalue i] with t hj hi
  exact hj.trans hi.symm

/-- A smooth central fiber cannot exceed the nearby constant physical count,
even if central ramification merges several chart indices. -/
theorem central_fiber_count_le_of_total_graph {ι α : Type*} [Finite ι]
    {P : ι → ℂ → α} {S : ι → ℂ → ℂ} {V : ℂ → ℂ}
    {Y : Set (ℂ × ℂ)} {s₀ : ℂ} {C : Set α}
    (hS : ∀ j, ContinuousAt (S j) 0) (hV : ContinuousAt V 0)
    (hcenter : ∀ j, S j 0 = s₀)
    (hbranch : ∀ j, ∀ᶠ t in 𝓝 (0 : ℂ), (S j t, V t) ∈ Y)
    {F : ℂ → ℂ}
    (hgraph : ∀ᶠ y in 𝓝 (s₀, V 0), y ∈ Y → y.1 = F y.2)
    (hcover : C ⊆ (fun j => P j 0) '' univ) {t : ℂ}
    (hcmp : ∀ j k : ι, P j t = P k t → ∀ᶠ u in 𝓝 (0 : ℂ), P j u = P k u)
    (i : ι) : C.Finite ∧
      C.ncard ≤ ((fun j => P j t) '' ProductGermClass S i).ncard := by
  have hfull := productGermClass_eq_univ_of_total_graph hS hV hcenter hbranch hgraph i
  have hJ : (univ : Set ι).Finite := Set.toFinite _
  have hfinite : C.Finite := (hJ.image _).subset hcover
  refine ⟨hfinite, ?_⟩
  rw [hfull]
  apply (Set.ncard_le_ncard hcover (hJ.image _)).trans
  apply ncard_image_le_of_kernel_imp hJ
  intro j _ k _ hjk
  exact (hcmp j k hjk).self_of_nhds

end MaximumModulus
