module

public import MaximumModulus.LocalImageTopology

@[expose] public section

open Set Filter Metric
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- Stabilized comparisons identify two entire punctured image branches,
or separate them completely. -/
theorem imageBranches_eq_or_disjoint_of_stable_comparisons
    {S T : ℂ → ℂ} {E : ℕ} (hE : 0 < E) (p₀ : ℂ) {δ : ℝ}
    (hcmp : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ ω : ℂ, ω ^ E = 1 →
      (S (ω * t) = T t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = T u)) :
    ImageBranch S E p₀ '' (ball 0 δ \ {0}) =
        ImageBranch T E p₀ '' (ball 0 δ \ {0}) ∨
      Disjoint (ImageBranch S E p₀ '' (ball 0 δ \ {0}))
        (ImageBranch T E p₀ '' (ball 0 δ \ {0})) := by
  by_cases hg : ∃ ω : ℂ, ω ^ E = 1 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = T u
  · left
    obtain ⟨ω, hω, hgerm⟩ := hg
    have hωnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hE.ne'
    have hωne : ω ≠ 0 := norm_ne_zero_iff.mp (by simp [hωnorm])
    have hrot : ∀ t ∈ ball (0 : ℂ) δ \ {0},
        ImageBranch S E p₀ (ω * t) = ImageBranch T E p₀ t := by
      intro t ht
      apply Prod.ext
      · exact (hcmp t (by simpa [mem_ball_iff_norm] using ht.1)
          (by simpa using ht.2) ω hω).mpr hgerm
      · simp [ImageBranch, mul_pow, hω]
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hu : ω⁻¹ * t ∈ ball (0 : ℂ) δ \ {0} := by
        have htne : t ≠ 0 := by simpa using ht.2
        refine ⟨?_, ?_⟩
        · simpa [mem_ball_iff_norm, hωnorm] using ht.1
        · simpa using (mul_ne_zero (inv_ne_zero hωne) htne)
      refine ⟨ω⁻¹ * t, hu, ?_⟩
      simpa [← mul_assoc, hωne] using (hrot _ hu).symm
    · rintro ⟨t, ht, rfl⟩
      refine ⟨ω * t, ⟨?_, ?_⟩, hrot t ht⟩
      · simpa [mem_ball_iff_norm, hωnorm] using ht.1
      · simpa using mul_ne_zero hωne (show t ≠ 0 by simpa using ht.2)
  · right
    apply Set.disjoint_left.mpr
    rintro y ⟨u, hu, rfl⟩ ⟨t, ht, heq⟩
    have ht0 : t ≠ 0 := by simpa using ht.2
    have hpow : u ^ E = t ^ E :=
      add_left_cancel (congrArg Prod.snd heq).symm
    have hω : (u / t) ^ E = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero E ht0)]
    have hfirst : S (u / t * t) = T t := by
      simpa [ImageBranch, div_mul_cancel₀ _ ht0] using (congrArg Prod.fst heq).symm
    exact hg ⟨u / t, hω, (hcmp t (by simpa [mem_ball_iff_norm] using ht.1)
      ht0 (u / t) hω).mp hfirst⟩

/-- Away from the central value, belonging to a full branch image is
the same as belonging to its punctured image. -/
theorem imageBranch_mem_punctured_of_value_ne {S : ℂ → ℂ} {E : ℕ}
    (hE : 0 < E) {p₀ : ℂ} {δ : ℝ} {y : ℂ × ℂ} (hy : y.2 ≠ p₀)
    (hmem : y ∈ ImageBranch S E p₀ '' ball 0 δ) :
    y ∈ ImageBranch S E p₀ '' (ball 0 δ \ {0}) := by
  obtain ⟨t, ht, rfl⟩ := hmem
  refine ⟨t, ⟨ht, ?_⟩, rfl⟩
  intro ht0
  have htzero : t = 0 := by simpa using ht0
  exact hy (by simp [ImageBranch, htzero, hE.ne'])

/-- A finite stabilized family has a single analytic graph near every
noncentral image point. Equal germs contribute multiplicity to the
physical fiber, rather than extra intersecting image branches. -/
theorem finite_imageBranches_noncentral_image_is_graph {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} {E : ℕ} (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ i, AnalyticOnNhd ℂ (S i) (ball 0 δ))
    (hcont : ∀ i, ContinuousOn (S i) (closedBall 0 δ))
    (hcmp : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i j : ι, ∀ ω : ℂ, ω ^ E = 1 →
      (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u))
    (i : ι) {t₀ : ℂ} (htball : ‖t₀‖ < δ) (ht0 : t₀ ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (p₀ + t₀ ^ E) ∧ F (p₀ + t₀ ^ E) = S i t₀ ∧
      ∀ᶠ y in 𝓝 (ImageBranch (S i) E p₀ t₀),
        y ∈ (⋃ j : ι, ImageBranch (S j) E p₀ '' ball 0 δ) ↔ y.1 = F y.2 := by
  let y₀ := ImageBranch (S i) E p₀ t₀
  have hval : y₀.2 ≠ p₀ := by
    change p₀ + t₀ ^ E ≠ p₀
    exact add_ne_left.mpr (pow_ne_zero E ht0)
  have hyi : y₀ ∈ ImageBranch (S i) E p₀ '' (ball 0 δ \ {0}) :=
    ⟨t₀, ⟨by simpa [mem_ball_iff_norm] using htball, by simpa using ht0⟩, rfl⟩
  have hcyl : y₀ ∈ BranchValueCylinder E p₀ δ := by
    change ‖p₀ + t₀ ^ E - p₀‖ < δ ^ E
    simpa [norm_pow] using pow_lt_pow_left₀ htball (norm_nonneg _) hE.ne'
  have hcover : ∀ᶠ y in 𝓝 y₀, ∀ j : ι,
      y ∈ ImageBranch (S j) E p₀ '' ball 0 δ →
        y ∈ ImageBranch (S i) E p₀ '' ball 0 δ := by
    apply Filter.eventually_all.mpr
    intro j
    rcases imageBranches_eq_or_disjoint_of_stable_comparisons hE p₀
      (fun t ht hn ω hω => hcmp t ht hn i j ω hω) with heq | hdisj
    · filter_upwards [(continuous_snd.tendsto y₀).eventually
        (eventually_ne_nhds hval)] with y hy
      intro hmem
      have hpunc := imageBranch_mem_punctured_of_value_ne hE hy hmem
      rw [← heq] at hpunc
      exact (image_mono sdiff_subset) hpunc
    · have hnot : y₀ ∉ closure (ImageBranch (S j) E p₀ '' ball 0 δ) := by
        intro hycl
        have hymem := (imageBranch_closure_inter_valueCylinder hE p₀ hδ (hcont j)).subset
          ⟨hycl, hcyl⟩
        exact Set.disjoint_left.mp hdisj hyi
          (imageBranch_mem_punctured_of_value_ne hE hval hymem)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnot] with y hy
      intro hmem
      exact False.elim (hy (subset_closure hmem))
  obtain ⟨F, hF, hcenter, hgraph⟩ := imageBranch_noncentral_image_is_graph hE p₀ hδ
    (hS i) (fun t ht hn ω hω => by
      simpa [PersistentSymmetries, hω] using hcmp t ht hn i i ω hω) htball ht0
  refine ⟨F, hF, hcenter, ?_⟩
  filter_upwards [hcover, hgraph] with y hy hgy
  constructor
  · intro hymem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hymem
    exact hgy.mp (hy j hj)
  · intro hyeq
    exact mem_iUnion.mpr ⟨i, hgy.mpr hyeq⟩

end MaximumModulus
