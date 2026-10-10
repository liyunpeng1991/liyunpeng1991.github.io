module

public import MaximumModulus.FiniteImageGraphs

@[expose] public section

open Set Filter Metric
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- Stabilized finite branch comparisons capture the entire nearby union
inside any branch through a noncentral point. -/
theorem finite_imageBranches_eventually_capture_branch {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} {N : ℕ} (hN : 0 < N) (c : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hcont : ∀ i, ContinuousOn (S i) (closedBall 0 δ))
    (hcmp : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i j : ι, ∀ ω : ℂ, ω ^ N = 1 →
      (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u))
    (i : ι) {t₀ : ℂ} (htball : ‖t₀‖ < δ) (ht0 : t₀ ≠ 0) :
    ∀ᶠ y in 𝓝 (ImageBranch (S i) N c t₀),
      y ∈ (⋃ j : ι, ImageBranch (S j) N c '' ball 0 δ) →
      y ∈ ImageBranch (S i) N c '' ball 0 δ := by
  let y₀ := ImageBranch (S i) N c t₀
  have hval : y₀.2 ≠ c := add_ne_left.mpr (pow_ne_zero N ht0)
  have hyi : y₀ ∈ ImageBranch (S i) N c '' (ball 0 δ \ {0}) :=
    ⟨t₀, ⟨by simpa [mem_ball_iff_norm] using htball, by simpa using ht0⟩, rfl⟩
  have hcyl : y₀ ∈ BranchValueCylinder N c δ := by
    change ‖c + t₀ ^ N - c‖ < δ ^ N
    simpa [norm_pow] using pow_lt_pow_left₀ htball (norm_nonneg _) hN.ne'
  have hcover : ∀ᶠ y in 𝓝 y₀, ∀ j : ι,
      y ∈ ImageBranch (S j) N c '' ball 0 δ →
      y ∈ ImageBranch (S i) N c '' ball 0 δ := by
    apply Filter.eventually_all.mpr
    intro j
    rcases imageBranches_eq_or_disjoint_of_stable_comparisons hN c
      (fun t ht hn ω hω => hcmp t ht hn i j ω hω) with heq | hdisj
    · filter_upwards [(continuous_snd.tendsto y₀).eventually
        (eventually_ne_nhds hval)] with y hy
      intro hmem
      have hpunc := imageBranch_mem_punctured_of_value_ne hN hy hmem
      rw [← heq] at hpunc
      exact (image_mono sdiff_subset) hpunc
    · have hnot : y₀ ∉ closure (ImageBranch (S j) N c '' ball 0 δ) := by
        intro hycl
        have hymem := (imageBranch_closure_inter_valueCylinder hN c hδ (hcont j)).subset
          ⟨hycl, hcyl⟩
        exact Set.disjoint_left.mp hdisj hyi
          (imageBranch_mem_punctured_of_value_ne hN hval hymem)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnot] with y hy
      intro hmem
      exact False.elim (hy (subset_closure hmem))
  filter_upwards [hcover] with y hy hymem
  obtain ⟨j, hj⟩ := mem_iUnion.mp hymem
  exact hy j hj

/-- Local capture of a set persists to its closure in an open value
cylinder, because a finite full-branch union is relatively closed there. -/
theorem closure_captured_by_finite_imageBranches {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} {N : ℕ} (hN : 0 < N) (c : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hcont : ∀ i, ContinuousOn (S i) (closedBall 0 δ))
    {A W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWcyl : W ⊆ BranchValueCylinder N c δ)
    (hcapture : A ∩ W ⊆ ⋃ i : ι, ImageBranch (S i) N c '' ball 0 δ) :
    closure A ∩ W ⊆ ⋃ i : ι, ImageBranch (S i) N c '' ball 0 δ := by
  intro y hy
  have hycl := closure_mono hcapture (hW.closure_inter hy)
  have hclosed := selected_imageBranches_full_closure (Set.toFinite (univ : Set ι))
    hN c hδ (fun i _ => hcont i)
  simp only [mem_univ, iUnion_true] at hclosed
  exact hclosed.subset ⟨hycl, hWcyl hy.2⟩

/-- A finite image cover and genuine interior analytic subbranches suffice
to continue the closure through the omitted value. Branch-membership openness
is derived, rather than assumed. The explicit cover/subbranch inputs must
still be constructed for any particular correspondence. -/
theorem closure_continues_through_finite_imageBranches {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} {N : ℕ} (hN : 0 < N) (c : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ i, AnalyticOnNhd ℂ (S i) (closedBall 0 δ))
    (hcmp : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i j : ι, ∀ ω : ℂ, ω ^ N = 1 →
      (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u))
    {A W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWcyl : W ⊆ BranchValueCylinder N c δ)
    (hbranchW : ∀ i, ImageBranch (S i) N c '' ball 0 δ ⊆ W)
    (hcapture : A ∩ W ⊆ ⋃ i : ι, ImageBranch (S i) N c '' ball 0 δ)
    (homit : ∀ y ∈ A, y.2 ≠ c)
    (hinterior : ∀ y ∈ closure A, y ∈ W → y.2 ≠ c →
      ∃ (T : ℂ → ℂ) (M : ℕ) (q : ℂ) (ρ : ℝ),
        0 < M ∧ 0 < ρ ∧ AnalyticAt ℂ T 0 ∧
        ImageBranch T M q 0 = y ∧ ImageBranch T M q '' ball 0 ρ ⊆ closure A) :
    ∃ J : Set ι, (∀ i ∈ J, ImageBranch (S i) N c '' ball 0 δ ⊆ closure A) ∧
      closure A ∩ W = (⋃ i ∈ J, ImageBranch (S i) N c '' ball 0 δ) ∩ W := by
  let H := closure A
  let J : Set ι := {i | (ImageBranch (S i) N c '' (ball 0 δ \ {0}) ∩ H).Nonempty}
  have hHcap : H ∩ W ⊆ ⋃ i : ι, ImageBranch (S i) N c '' ball 0 δ :=
    closure_captured_by_finite_imageBranches hN c hδ (fun i => (hS i).continuousOn)
      hW hWcyl hcapture
  have hselected : ∀ i ∈ J, ImageBranch (S i) N c '' ball 0 δ ⊆ H := by
    intro i hi
    apply imageBranch_full_branch_of_captured_subbranches hN c hδ
      ((hS i).mono ball_subset_closedBall)
      (fun t ht hn ω hω => by simpa [PersistentSymmetries, hω] using hcmp t ht hn i i ω hω)
      isClosed_closure ?_ hi
    intro t₀ ht hn htH
    have htW : ImageBranch (S i) N c t₀ ∈ W :=
      hbranchW i ⟨t₀, by simpa [mem_ball_iff_norm] using ht, rfl⟩
    have hvalue : (ImageBranch (S i) N c t₀).2 ≠ c :=
      add_ne_left.mpr (pow_ne_zero N hn)
    obtain ⟨T, M, q, ρ, hM, hρ, hT, hcenter, hsub⟩ :=
      hinterior _ htH htW hvalue
    refine ⟨T, M, q, ρ, hM, hρ, hT, hcenter, hsub, ?_⟩
    have hTc : ContinuousAt (ImageBranch T M q) 0 :=
      hT.continuousAt.prodMk (continuousAt_const.add (continuousAt_id.pow M))
    have htend : Tendsto (ImageBranch T M q) (𝓝 0)
        (𝓝 (ImageBranch (S i) N c t₀)) := by rw [← hcenter]; exact hTc
    have hnear := finite_imageBranches_eventually_capture_branch hN c hδ
      (fun j => (hS j).continuousOn) hcmp i ht hn
    filter_upwards [htend.eventually hnear, htend.eventually (hW.mem_nhds htW),
      ball_mem_nhds (0 : ℂ) hρ] with u hu huW huBall
    exact hu (hHcap ⟨hsub ⟨u, huBall, rfl⟩, huW⟩)
  have hAselected : A ∩ W ⊆ ⋃ i ∈ J, ImageBranch (S i) N c '' ball 0 δ := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcapture hy)
    have hip := imageBranch_mem_punctured_of_value_ne hN (homit y hy.1) hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⟨y, hip, subset_closure hy.1⟩, hi⟩⟩
  have hclosed := selected_imageBranches_full_closure (Set.toFinite J) hN c hδ
    (fun i _ => (hS i).continuousOn)
  have heq : H ∩ W = (⋃ i ∈ J, ImageBranch (S i) N c '' ball 0 δ) ∩ W := by
    apply Subset.antisymm
    · intro y hy
      have hycl := closure_mono hAselected (hW.closure_inter hy)
      exact ⟨hclosed.subset ⟨hycl, hWcyl hy.2⟩, hy.2⟩
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy.1
      obtain ⟨hiJ, hi⟩ := mem_iUnion.mp hi
      exact ⟨hselected i hiJ hi, hy.2⟩
  exact ⟨J, hselected, heq⟩

/-- A proved finite full-branch description gives an open local product
projection when its actual product germs are nonconstant. -/
theorem finite_imageBranches_local_projection_isOpen {ι : Type*}
    {J : Set ι} {S : ι → ℂ → ℂ} {N : ℕ} (c : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ i ∈ J, AnalyticOnNhd ℂ (S i) (closedBall 0 δ))
    (hne : ∀ i ∈ J, ¬∀ᶠ t in 𝓝 (0 : ℂ), S i t = S i 0)
    {H W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (heq : H ∩ W = (⋃ i ∈ J, ImageBranch (S i) N c '' ball 0 δ) ∩ W) :
    IsOpen (Prod.fst '' (H ∩ W)) := by
  rw [heq]
  have hdistrib : (⋃ i ∈ J, ImageBranch (S i) N c '' ball 0 δ) ∩ W =
      ⋃ i ∈ J, ((ImageBranch (S i) N c '' ball 0 δ) ∩ W) := by
    ext y
    simp only [mem_inter_iff, mem_iUnion]
    aesop
  rw [hdistrib]
  simp only [image_iUnion]
  apply isOpen_iUnion
  intro i
  apply isOpen_iUnion
  intro hi
  exact imageBranch_restricted_product_projection_isOpen hδ
    ((hS i hi).mono ball_subset_closedBall) (hne i hi) N c hW

end MaximumModulus
