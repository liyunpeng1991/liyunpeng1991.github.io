module

public import MaximumModulus.BranchCollision
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
Topological properties of actual local branch images `(S(t),p₀+t^E)`.
These results do not assume an analytic normalization, an analytic image
theorem, or a global correspondence degree.  In particular, relative
closedness comes directly from the value-coordinate power identity and
compactness of a closed parameter disk.
-/

open Set Filter Metric
open scoped Topology

namespace MaximumModulus

noncomputable section

/-- The open target cylinder in which the power coordinate comes from
the open parameter disk of radius `δ`. -/
def BranchValueCylinder (E : ℕ) (p₀ : ℂ) (δ : ℝ) : Set (ℂ × ℂ) :=
  {y | ‖y.2 - p₀‖ < δ ^ E}

theorem isOpen_branchValueCylinder (E : ℕ) (p₀ : ℂ) (δ : ℝ) :
    IsOpen (BranchValueCylinder E p₀ δ) := by
  exact isOpen_lt (continuous_snd.sub continuous_const).norm continuous_const

/-- The open parameter disk image is exactly the compact closed disk
image restricted to its open value cylinder. -/
theorem imageBranch_open_disk_eq_closed_disk_inter {S : ℂ → ℂ} {E : ℕ}
    (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ImageBranch S E p₀ '' ball 0 δ =
      (ImageBranch S E p₀ '' closedBall 0 δ) ∩ BranchValueCylinder E p₀ δ := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : ‖t‖ < δ := by simpa only [mem_ball, dist_zero_right] using ht
    refine ⟨⟨t, by simpa only [mem_closedBall, dist_zero_right] using ht'.le, rfl⟩, ?_⟩
    change ‖p₀ + t ^ E - p₀‖ < δ ^ E
    simpa only [add_sub_cancel_left, norm_pow] using
      pow_lt_pow_left₀ ht' (norm_nonneg t) hE.ne'
  · rintro ⟨⟨t, _, rfl⟩, ht⟩
    have ht' : ‖t‖ ^ E < δ ^ E := by
      simpa only [BranchValueCylinder, mem_ofPred_eq, ImageBranch,
        add_sub_cancel_left, norm_pow] using ht
    refine ⟨t, ?_, rfl⟩
    simpa only [mem_ball, dist_zero_right] using
      lt_of_pow_lt_pow_left₀ E hδ.le ht'

theorem imageBranch_continuousOn {S : ℂ → ℂ} {D : Set ℂ}
    (hS : ContinuousOn S D) (E : ℕ) (p₀ : ℂ) :
    ContinuousOn (ImageBranch S E p₀) D := by
  exact hS.prodMk (continuousOn_const.add (continuousOn_id.pow E))

/-- A closed parameter disk has compact and hence closed branch image
whenever `S` is continuous on that disk. -/
theorem imageBranch_closed_disk_isClosed {S : ℂ → ℂ} (E : ℕ) (p₀ : ℂ)
    (δ : ℝ) (hS : ContinuousOn S (closedBall 0 δ)) :
    IsClosed (ImageBranch S E p₀ '' closedBall 0 δ) := by
  exact ((isCompact_closedBall (0 : ℂ) δ).image_of_continuousOn
    (imageBranch_continuousOn hS E p₀)).isClosed

/-- Exact local closedness: every closure point lying inside the value
cylinder already belongs to the open disk image. -/
theorem imageBranch_closure_inter_valueCylinder {S : ℂ → ℂ} {E : ℕ}
    (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ContinuousOn S (closedBall 0 δ)) :
    closure (ImageBranch S E p₀ '' ball 0 δ) ∩ BranchValueCylinder E p₀ δ =
      ImageBranch S E p₀ '' ball 0 δ := by
  apply Subset.antisymm
  · have hsubset : closure (ImageBranch S E p₀ '' ball 0 δ) ⊆
        ImageBranch S E p₀ '' closedBall 0 δ := by
      apply closure_minimal
      · exact image_mono ball_subset_closedBall
      · exact imageBranch_closed_disk_isClosed E p₀ δ hS
    intro y hy
    rw [imageBranch_open_disk_eq_closed_disk_inter hE p₀ hδ]
    exact ⟨hsubset hy.1, hy.2⟩
  · intro y hy
    refine ⟨subset_closure hy, ?_⟩
    exact ((imageBranch_open_disk_eq_closed_disk_inter hE p₀ hδ).subset hy).2

/-- An analytic germ supplies a closed parameter disk on which the exact
relative-closedness statement applies. -/
theorem analytic_imageBranch_locally_closed {S : ℂ → ℂ}
    (hS : AnalyticAt ℂ S 0) {E : ℕ} (hE : 0 < E) (p₀ : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧
      closure (ImageBranch S E p₀ '' ball 0 δ) ∩ BranchValueCylinder E p₀ δ =
        ImageBranch S E p₀ '' ball 0 δ := by
  obtain ⟨r, hr, han⟩ := hS.exists_ball_analyticOnNhd
  have hcont : ContinuousOn S (closedBall 0 (r / 2)) := by
    apply han.continuousOn.mono
    intro t ht
    exact mem_ball.mpr ((mem_closedBall.mp ht).trans_lt (half_lt_self hr))
  exact ⟨r / 2, half_pos hr,
    imageBranch_closure_inter_valueCylinder hE p₀ (half_pos hr) hcont⟩

/-- A nonconstant analytic germ has open product projection on any
analytic disk.  The raw image parameter need not be injective. -/
theorem imageBranch_product_projection_isOpen {S : ℂ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hS : AnalyticOnNhd ℂ S (ball 0 δ))
    (hne : ¬∀ᶠ t in 𝓝 (0 : ℂ), S t = S 0) (E : ℕ) (p₀ : ℂ) :
    IsOpen (Prod.fst '' (ImageBranch S E p₀ '' ball 0 δ)) := by
  have hnotconst : ¬∃ c : ℂ, ∀ t ∈ ball 0 δ, S t = c := by
    rintro ⟨c, hc⟩
    apply hne
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with t ht
    exact (hc t ht).trans (hc 0 (mem_ball_self hδ)).symm
  have hopen := (hS.is_constant_or_isOpen isPreconnected_ball).resolve_left hnotconst
  simpa only [image_image, Function.comp_def, ImageBranch] using
    hopen (ball 0 δ) Subset.rfl isOpen_ball

/-- A whole nonconstant local branch contained in a set supplies a
neighborhood in that set's product projection, including at its center. -/
theorem imageBranch_product_projection_mem_nhds {S : ℂ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hS : AnalyticOnNhd ℂ S (ball 0 δ))
    (hne : ¬∀ᶠ t in 𝓝 (0 : ℂ), S t = S 0) (E : ℕ) (p₀ : ℂ)
    {H : Set (ℂ × ℂ)} (hsubset : ImageBranch S E p₀ '' ball 0 δ ⊆ H)
    {t : ℂ} (ht : t ∈ ball 0 δ) : Prod.fst '' H ∈ 𝓝 (S t) := by
  apply mem_of_superset
    ((imageBranch_product_projection_isOpen hδ hS hne E p₀).mem_nhds ?_)
    (image_mono hsubset)
  exact ⟨ImageBranch S E p₀ t, ⟨t, ht, rfl⟩, rfl⟩

/-- The punctured complex disk is preconnected.  This uses a product of
the positive-radius interval and the complex unit circle; it does not
assume that deleting a point preserves connectedness in arbitrary spaces. -/
theorem punctured_disk_preconnected (δ : ℝ) :
    IsPreconnected ((ball (0 : ℂ) δ) \ {0}) := by
  have hsphere : IsPreconnected (sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (by simp [Complex.rank_real_complex]) (0 : ℂ) 1
  let f : ℝ × ℂ → ℂ := fun rz => rz.1 • rz.2
  have himage : f '' (Ioo (0 : ℝ) δ ×ˢ sphere (0 : ℂ) 1) = ball (0 : ℂ) δ \ {0} := by
    ext z
    constructor
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      have hun : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
      have hnorm : ‖r • u‖ = r := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hun, mul_one]
      refine ⟨?_, ?_⟩
      · simpa only [f, mem_ball, dist_zero_right, hnorm] using hr.2
      · intro hz
        have hz0 : r • u = 0 := by simpa only [f, mem_singleton_iff] using hz
        exact hr.1.ne' (by simpa only [hz0, norm_zero] using hnorm.symm)
    · rintro ⟨hz, hz0⟩
      have hzne : z ≠ 0 := by simpa only [mem_singleton_iff] using hz0
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzne
      have hzlt : ‖z‖ < δ := by simpa only [mem_ball, dist_zero_right] using hz
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨⟨hn, hzlt⟩, ?_⟩, ?_⟩
      · simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
      · simp only [f, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [← himage]
  exact (isPreconnected_Ioo.prod hsphere).image f (by fun_prop)

/-- A continuous raw branch has connected punctured image. -/
theorem imageBranch_punctured_image_preconnected {S : ℂ → ℂ} {δ : ℝ}
    (hS : ContinuousOn S (ball 0 δ)) (E : ℕ) (p₀ : ℂ) :
    IsPreconnected (ImageBranch S E p₀ '' (ball 0 δ \ {0})) := by
  exact (punctured_disk_preconnected δ).image _
    ((imageBranch_continuousOn hS E p₀).mono sdiff_subset)

/-- Membership in a closed set selects either a whole connected
parameter branch or none of it when the membership pullback is open.
The openness hypothesis is explicit: proving it from the actual image
germs remains a separate local analytic step. -/
theorem connected_branch_selected_or_disjoint {Z Y : Type*}
    [TopologicalSpace Z] [TopologicalSpace Y] {D : Set Z}
    (hD : IsPreconnected D) {γ : Z → Y} (hγ : ContinuousOn γ D)
    {H : Set Y} (hH : IsClosed H)
    (hopen : IsOpen ((fun t : D => γ t) ⁻¹' H)) :
    γ '' D ⊆ H ∨ Disjoint (γ '' D) H := by
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp hD
  have hclopen : IsClopen ((fun t : D => γ t) ⁻¹' H) :=
    ⟨hH.preimage hγ.domRestrict, hopen⟩
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · right
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ htH
    have htpre : (⟨t, ht⟩ : D) ∈ (fun t : D => γ t) ⁻¹' H := htH
    rw [hempty] at htpre
    exact Set.notMem_empty _ htpre
  · left
    rintro _ ⟨t, ht, rfl⟩
    have htpre : (⟨t, ht⟩ : D) ∈ (fun t : D => γ t) ⁻¹' H := by
      rw [huniv]
      trivial
    exact htpre

/-- The origin is a closure point of every positive-radius punctured disk. -/
theorem zero_mem_closure_punctured_disk {δ : ℝ} (hδ : 0 < δ) :
    (0 : ℂ) ∈ closure (ball (0 : ℂ) δ \ {0}) := by
  have hc : (0 : ℂ) ∈ closure ({0}ᶜ : Set ℂ) := by
    rw [closure_compl_singleton]
    trivial
  exact isOpen_ball.inter_closure ⟨mem_ball_self hδ, hc⟩

/-- A closed set containing a full punctured raw branch contains its
center and hence its full disk image. -/
theorem imageBranch_complete_selected_branch {S : ℂ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hS : ContinuousAt S 0) (E : ℕ) (p₀ : ℂ)
    {H : Set (ℂ × ℂ)} (hH : IsClosed H)
    (hselected : ImageBranch S E p₀ '' (ball 0 δ \ {0}) ⊆ H) :
    ImageBranch S E p₀ '' ball 0 δ ⊆ H := by
  have hγ : ContinuousAt (ImageBranch S E p₀) 0 :=
    hS.prodMk (continuousAt_const.add (continuousAt_id.pow E))
  have hcenter : ImageBranch S E p₀ 0 ∈ H :=
    hH.closure_subset (closure_mono hselected
      (mem_closure_image hγ (zero_mem_closure_punctured_disk hδ)))
  rintro _ ⟨t, ht, rfl⟩
  by_cases ht0 : t = 0
  · simpa only [ht0] using hcenter
  · exact hselected ⟨t, ⟨ht, by simpa only [mem_singleton_iff] using ht0⟩, rfl⟩

/-- A raw punctured branch meeting a closed set is selected in full,
including its center, when branch membership is relatively open. -/
theorem imageBranch_full_branch_of_clopen_membership {S : ℂ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hS : ContinuousOn S (ball 0 δ)) (E : ℕ) (p₀ : ℂ)
    {H : Set (ℂ × ℂ)} (hH : IsClosed H)
    (hopen : IsOpen ((fun t : {t : ℂ // t ∈ ball (0 : ℂ) δ \ {0}} =>
      ImageBranch S E p₀ t) ⁻¹' H))
    (hmeet : (ImageBranch S E p₀ '' (ball 0 δ \ {0}) ∩ H).Nonempty) :
    ImageBranch S E p₀ '' ball 0 δ ⊆ H := by
  have hγ := (imageBranch_continuousOn hS E p₀).mono
    (sdiff_subset : ball (0 : ℂ) δ \ {0} ⊆ ball 0 δ)
  have hselected : ImageBranch S E p₀ '' (ball 0 δ \ {0}) ⊆ H := by
    rcases connected_branch_selected_or_disjoint (punctured_disk_preconnected δ)
        hγ hH hopen with h | h
    · exact h
    · obtain ⟨y, hybranch, hyH⟩ := hmeet
      exact False.elim (Set.disjoint_left.mp h hybranch hyH)
  exact imageBranch_complete_selected_branch hδ
    ((hS 0 (mem_ball_self hδ)).continuousAt (ball_mem_nhds (0 : ℂ) hδ))
    E p₀ hH hselected

/-- Full selected nonconstant branches make the entire product
projection open.  The chart hypothesis describes actual branch maps and
does not assume a correspondence degree. -/
theorem isOpen_product_projection_of_imageBranch_charts {H : Set (ℂ × ℂ)}
    (hcharts : ∀ y ∈ H, ∃ (S : ℂ → ℂ) (E : ℕ) (p₀ : ℂ) (δ : ℝ),
      0 < δ ∧ AnalyticOnNhd ℂ S (ball 0 δ) ∧
      (¬∀ᶠ t in 𝓝 (0 : ℂ), S t = S 0) ∧
      ImageBranch S E p₀ 0 = y ∧ ImageBranch S E p₀ '' ball 0 δ ⊆ H) :
    IsOpen (Prod.fst '' H) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨S, E, p₀, δ, hδ, hS, hne, hcenter, hsub⟩ := hcharts y hy
  have hx : S 0 = x := (congrArg Prod.fst hcenter).trans hxy
  simpa only [hx] using imageBranch_product_projection_mem_nhds
    hδ hS hne E p₀ hsub (mem_ball_self hδ)

/-- Projection openness only uses the analytic first coordinate of each
selected branch.  The value coordinate can take values in any
topological space, allowing finite and infinite compactified-value
charts to be treated by the same theorem. -/
theorem isOpen_product_projection_of_analytic_charts {P : Type*}
    [TopologicalSpace P] {H : Set (ℂ × P)}
    (hcharts : ∀ y ∈ H, ∃ (S : ℂ → ℂ) (V : ℂ → P) (δ : ℝ),
      0 < δ ∧ AnalyticOnNhd ℂ S (ball 0 δ) ∧
      (¬∀ᶠ t in 𝓝 (0 : ℂ), S t = S 0) ∧
      (S 0, V 0) = y ∧ (fun t => (S t, V t)) '' ball 0 δ ⊆ H) :
    IsOpen (Prod.fst '' H) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨S, V, δ, hδ, hS, hne, hcenter, hsub⟩ := hcharts y hy
  have hopen : IsOpen (S '' ball 0 δ) := by
    simpa only [image_image, Function.comp_def, ImageBranch] using
      imageBranch_product_projection_isOpen hδ hS hne 1 0
  have hx : S 0 = x := (congrArg Prod.fst hcenter).trans hxy
  have hximage : S 0 ∈ S '' ball 0 δ := ⟨0, mem_ball_self hδ, rfl⟩
  have hproj : S '' ball 0 δ ⊆ Prod.fst '' H := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨(S t, V t), hsub ⟨t, ht, rfl⟩, rfl⟩
  simpa only [hx] using mem_of_superset (hopen.mem_nhds hximage) hproj

/-- Completing a selected punctured branch also works in a general
compactified-value target, provided its value chart is continuous at
the center. -/
theorem complete_selected_parametric_branch {P : Type*} [TopologicalSpace P]
    {S : ℂ → ℂ} {V : ℂ → P} {δ : ℝ} (hδ : 0 < δ)
    (hS : ContinuousAt S 0) (hV : ContinuousAt V 0)
    {H : Set (ℂ × P)} (hH : IsClosed H)
    (hselected : (fun t => (S t, V t)) '' (ball 0 δ \ {0}) ⊆ H) :
    (fun t => (S t, V t)) '' ball 0 δ ⊆ H := by
  have hcenter : (S 0, V 0) ∈ H :=
    hH.closure_subset (closure_mono hselected
      (mem_closure_image (hS.prodMk hV) (zero_mem_closure_punctured_disk hδ)))
  rintro _ ⟨t, ht, rfl⟩
  by_cases ht0 : t = 0
  · simpa only [ht0] using hcenter
  · exact hselected ⟨t, ⟨ht, by simpa only [mem_singleton_iff] using ht0⟩, rfl⟩

/-- Away from the central parameter, a raw power-coordinate branch is
an actual analytic graph over the value coordinate.  The local inverse
also supplies every nearby point of that graph. -/
theorem imageBranch_noncentral_graph_germ {S : ℂ → ℂ} {E : ℕ}
    (hE : 0 < E) (p₀ : ℂ) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    (hS : AnalyticAt ℂ S t₀) :
    ∃ F ψ : ℂ → ℂ,
      AnalyticAt ℂ F (p₀ + t₀ ^ E) ∧ AnalyticAt ℂ ψ (p₀ + t₀ ^ E) ∧
      ψ (p₀ + t₀ ^ E) = t₀ ∧
      (∀ᶠ t in 𝓝 t₀,
        ImageBranch S E p₀ t = (F (p₀ + t ^ E), p₀ + t ^ E)) ∧
      (∀ᶠ p in 𝓝 (p₀ + t₀ ^ E), ImageBranch S E p₀ (ψ p) = (F p, p)) := by
  let P : ℂ → ℂ := fun t => p₀ + t ^ E
  have hP : AnalyticAt ℂ P t₀ := analyticAt_const.add (analyticAt_id.pow E)
  have hd : HasStrictDerivAt P ((E : ℂ) * t₀ ^ (E - 1)) t₀ := by
    exact (hasStrictDerivAt_pow E t₀).const_add p₀
  have hne : deriv P t₀ ≠ 0 := by
    rw [hd.hasDerivAt.deriv]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hE.ne') (pow_ne_zero _ ht₀)
  let ψ := hP.hasStrictDerivAt.localInverse P (deriv P t₀) t₀ hne
  let F := S ∘ ψ
  have hψan : AnalyticAt ℂ ψ (P t₀) := hP.analyticAt_localInverse hne
  have hleft : ∀ᶠ t in 𝓝 t₀, ψ (P t) = t := hP.hasStrictDerivAt.eventually_left_inverse hne
  have hright : ∀ᶠ p in 𝓝 (P t₀), P (ψ p) = p :=
    hP.hasStrictDerivAt.eventually_right_inverse hne
  have hψ0 : ψ (P t₀) = t₀ := hleft.self_of_nhds
  have hFan : AnalyticAt ℂ F (P t₀) := hS.comp_of_eq hψan hψ0
  refine ⟨F, ψ, hFan, hψan, hψ0, ?_, ?_⟩
  · filter_upwards [hleft] with t ht
    apply Prod.ext
    · change S t = S (ψ (P t))
      exact congrArg S ht.symm
    · rfl
  · filter_upwards [hright] with p hp
    apply Prod.ext
    · rfl
    · exact hp

/-- A nonconstant analytic subbranch contained in a graph fills a
neighborhood of its central value.  This is the elementary local
openness argument used to select full captured branches, replacing a
dimension theorem for analytic subsets. -/
theorem eventually_graph_mem_of_analytic_subbranch {F P Q : ℂ → ℂ}
    {H : Set (ℂ × ℂ)} (hP : AnalyticAt ℂ P 0)
    (hne : ¬∀ᶠ u in 𝓝 (0 : ℂ), P u = P 0)
    (hbranch : ∀ᶠ u in 𝓝 (0 : ℂ), (F (P u), P u) ∈ H)
    {t₀ : ℂ} (hQ : ContinuousAt Q t₀) (hcenter : Q t₀ = P 0) :
    ∀ᶠ t in 𝓝 t₀, (F (Q t), Q t) ∈ H := by
  have hmap : 𝓝 (P 0) ≤ Filter.map P (𝓝 (0 : ℂ)) :=
    hP.eventually_constant_or_nhds_le_map_nhds.resolve_left hne
  have hvalues : ∀ᶠ p in 𝓝 (P 0), (F p, p) ∈ H :=
    hmap (Filter.eventually_map.mpr hbranch)
  have htend : Tendsto Q (𝓝 t₀) (𝓝 (P 0)) := by
    rw [← hcenter]
    exact hQ
  exact htend.eventually hvalues

/-- After the finite collision tests have stabilized, the *whole* raw
disk image is a single analytic graph near each noncentral image point.
Other power-coordinate inverse roots are either persistent copies of
that graph or are separated from the target point by continuity. -/
theorem imageBranch_noncentral_image_is_graph {S : ℂ → ℂ} {E : ℕ}
    (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (_hδ : 0 < δ)
    (hS : AnalyticOnNhd ℂ S (ball 0 δ))
    (hcollision : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ ω : ℂ, ω ^ E = 1 →
      (S (ω * t) = S t ↔ ω ∈ PersistentSymmetries S E))
    {t₀ : ℂ} (ht₀ball : ‖t₀‖ < δ) (ht₀ : t₀ ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (p₀ + t₀ ^ E) ∧
      F (p₀ + t₀ ^ E) = S t₀ ∧
      ∀ᶠ y in 𝓝 (ImageBranch S E p₀ t₀),
        y ∈ ImageBranch S E p₀ '' ball 0 δ ↔ y.1 = F y.2 := by
  have ht₀mem : t₀ ∈ ball (0 : ℂ) δ := by
    simpa only [mem_ball, dist_zero_right] using ht₀ball
  obtain ⟨F, ψ, hF, hψ, hψ0, _, hright⟩ :=
    imageBranch_noncentral_graph_germ hE p₀ ht₀ (hS t₀ ht₀mem)
  let y₀ := ImageBranch S E p₀ t₀
  let p₁ := p₀ + t₀ ^ E
  have hsnd : Tendsto (Prod.snd : ℂ × ℂ → ℂ) (𝓝 y₀) (𝓝 p₁) :=
    continuous_snd.tendsto y₀
  have htendψ : Tendsto ψ (𝓝 p₁) (𝓝 t₀) := by
    rw [← hψ0]
    exact hψ.continuousAt
  have hψball : ∀ᶠ p in 𝓝 p₁, ψ p ∈ ball (0 : ℂ) δ :=
    htendψ.eventually (isOpen_ball.mem_nhds ht₀mem)
  have hψne : ∀ᶠ p in 𝓝 p₁, ψ p ≠ 0 :=
    htendψ.eventually (eventually_ne_nhds ht₀)
  have hfinite := (power_fiber_finite_ncard_le E hE 1).1
  have havoid : ∀ᶠ y in 𝓝 y₀, ∀ ω : ℂ, ω ^ E = 1 →
      ω ∉ PersistentSymmetries S E → S (ω * ψ y.2) ≠ y.1 := by
    apply hfinite.eventually_all.mpr
    intro ω hω
    change ω ^ E = 1 at hω
    by_cases hωmem : ω ∈ PersistentSymmetries S E
    · exact Eventually.of_forall fun _ _ => False.elim (by contradiction)
    · have hωnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hE.ne'
      have hωball : ω * t₀ ∈ ball (0 : ℂ) δ := by
        simpa only [mem_ball, dist_zero_right, norm_mul, hωnorm, one_mul] using ht₀ball
      have hψcenter : ψ y₀.2 = t₀ := hψ0
      have hScont : ContinuousAt S (ω * ψ y₀.2) := by
        rw [hψcenter]
        exact (hS _ hωball).continuousAt
      have hψcont : ContinuousAt (fun y : ℂ × ℂ => ω * ψ y.2) y₀ :=
        continuousAt_const.mul
          (ContinuousAt.comp' (f := Prod.snd) (x := y₀) hψ.continuousAt continuousAt_snd)
      have hneq : S (ω * ψ y₀.2) ≠ y₀.1 := by
        rw [hψcenter]
        exact fun heq => hωmem ((hcollision t₀ ht₀ball ht₀ ω hω).mp heq)
      have hcont : ContinuousAt (fun y : ℂ × ℂ => S (ω * ψ y.2)) y₀ :=
        ContinuousAt.comp' (f := fun y : ℂ × ℂ => ω * ψ y.2) (x := y₀) hScont hψcont
      have hevent := (hcont.ne_iff_eventually_ne continuousAt_fst).mp hneq
      filter_upwards [hevent] with y hy
      exact fun _ => hy
  have hcenter : F p₁ = S t₀ := by
    have hc := congrArg Prod.fst hright.self_of_nhds
    simpa only [ImageBranch, hψ0] using hc.symm
  refine ⟨F, hF, hcenter, ?_⟩
  filter_upwards [hsnd.eventually hright, hsnd.eventually hψball,
    hsnd.eventually hψne, havoid] with y hyright hyball hyne hyavoid
  constructor
  · rintro ⟨t, _, ht⟩
    have hpow : t ^ E = (ψ y.2) ^ E := by
      apply add_left_cancel (a := p₀)
      exact (congrArg Prod.snd ht).trans (congrArg Prod.snd hyright).symm
    have hω : (t / ψ y.2) ^ E = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hyne)]
    have hωmem : t / ψ y.2 ∈ PersistentSymmetries S E := by
      by_contra hnot
      apply hyavoid _ hω hnot
      simpa only [ImageBranch, div_mul_cancel₀ _ hyne] using congrArg Prod.fst ht
    calc
      y.1 = S t := (congrArg Prod.fst ht).symm
      _ = S ((t / ψ y.2) * ψ y.2) := by rw [div_mul_cancel₀ _ hyne]
      _ = S (ψ y.2) := (hcollision _ (by simpa only [mem_ball, dist_zero_right] using hyball)
        hyne _ hω).mpr hωmem
      _ = F y.2 := congrArg Prod.fst hyright
  · intro hygraph
    refine ⟨ψ y.2, hyball, ?_⟩
    exact hyright.trans (Prod.ext hygraph.symm rfl)

/-- Every sufficiently small noncentral point has a single-graph
neighborhood in the actual disk image of an analytic raw branch. -/
theorem analytic_imageBranch_punctured_image_graphs {S : ℂ → ℂ}
    (hS : AnalyticAt ℂ S 0) {E : ℕ} (hE : 0 < E) (p₀ : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ : ℂ, ‖t₀‖ < δ → t₀ ≠ 0 →
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (p₀ + t₀ ^ E) ∧
        F (p₀ + t₀ ^ E) = S t₀ ∧
        ∀ᶠ y in 𝓝 (ImageBranch S E p₀ t₀),
          y ∈ ImageBranch S E p₀ '' ball 0 δ ↔ y.1 = F y.2 := by
  obtain ⟨r, hr, hanalytic⟩ := hS.exists_ball_analyticOnNhd
  obtain ⟨ε, hε, hcoll⟩ := imageBranch_collisions_radius hS hE
  let δ := min r ε
  have hδ : 0 < δ := lt_min hr hε
  refine ⟨δ, hδ, fun t₀ ht₀ ht₀ne => ?_⟩
  apply imageBranch_noncentral_image_is_graph hE p₀ hδ
  · exact hanalytic.mono (ball_subset_ball (min_le_left r ε))
  · intro t ht hne ω hω
    exact hcoll t (ht.trans_le (min_le_right r ε)) hne ω hω
  · exact ht₀
  · exact ht₀ne

/-- Closing a punctured branch and restricting to its value cylinder
recovers its whole open disk image, including the center. -/
theorem imageBranch_punctured_closure_inter_valueCylinder {S : ℂ → ℂ} {E : ℕ}
    (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ContinuousOn S (closedBall 0 δ)) :
    closure (ImageBranch S E p₀ '' (ball 0 δ \ {0})) ∩ BranchValueCylinder E p₀ δ =
      ImageBranch S E p₀ '' ball 0 δ := by
  apply Subset.antisymm
  · intro y hy
    have hy' : y ∈ closure (ImageBranch S E p₀ '' ball 0 δ) ∩
        BranchValueCylinder E p₀ δ :=
      ⟨closure_mono (image_mono sdiff_subset) hy.1, hy.2⟩
    exact (imageBranch_closure_inter_valueCylinder hE p₀ hδ hS).subset hy'
  · intro y hy
    refine ⟨?_, ((imageBranch_open_disk_eq_closed_disk_inter hE p₀ hδ).subset hy).2⟩
    exact imageBranch_complete_selected_branch hδ
      ((hS 0 (mem_closedBall_self hδ.le)).continuousAt (closedBall_mem_nhds (0 : ℂ) hδ))
      E p₀ isClosed_closure subset_closure hy

/-- Closing any finite selection of punctured branches recovers exactly
the corresponding full branches locally.  No membership-openness or
global degree hypothesis is needed for this finite-union step. -/
theorem selected_imageBranches_punctured_closure {ι : Type*} {J : Set ι}
    (hJ : J.Finite) {S : ι → ℂ → ℂ} {E : ℕ} (hE : 0 < E) (p₀ : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hS : ∀ i ∈ J, ContinuousOn (S i) (closedBall 0 δ)) :
    closure (⋃ i ∈ J, ImageBranch (S i) E p₀ '' (ball 0 δ \ {0})) ∩
        BranchValueCylinder E p₀ δ =
      ⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ := by
  rw [hJ.closure_biUnion]
  ext y
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi, hy⟩, hycyl⟩
    exact ⟨i, hi,
      (imageBranch_punctured_closure_inter_valueCylinder hE p₀ hδ (hS i hi)).subset ⟨hy, hycyl⟩⟩
  · rintro ⟨i, hi, hy⟩
    have hy' :=
      (imageBranch_punctured_closure_inter_valueCylinder hE p₀ hδ (hS i hi)).superset hy
    exact ⟨⟨i, hi, hy'.1⟩, hy'.2⟩

/-- A positive power value coordinate is never constant as a germ. -/
theorem power_value_germ_nonconstant {N : ℕ} (hN : 0 < N) (q₀ : ℂ) :
    ¬∀ᶠ u in 𝓝 (0 : ℂ), q₀ + u ^ N = q₀ + (0 : ℂ) ^ N := by
  intro hconstant
  have hevent : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      q₀ + u ^ N = q₀ + (0 : ℂ) ^ N ∧ u ≠ 0 := by
    filter_upwards [hconstant.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with u hu hu0
    exact ⟨hu, by simpa only [mem_compl_iff, mem_singleton_iff] using hu0⟩
  obtain ⟨u, hueq, hune⟩ := hevent.exists
  have hpow : u ^ N = 0 := by simpa only [zero_pow hN.ne'] using add_left_cancel hueq
  exact pow_ne_zero N hune hpow

/-- If a captured raw branch of a set lies in a smooth graph of another
actual branch image, it fills that graph near the intersection point.
This proves openness of branch membership from analytic containment;
branch-membership openness is not an assumption of this theorem. -/
theorem imageBranch_membership_eventually_of_captured_subbranch
    {S T : ℂ → ℂ} {E N : ℕ} (hN : 0 < N) (p₀ q₀ : ℂ)
    {δ ρ : ℝ} (hρ : 0 < ρ) {t₀ : ℂ} (ht₀ball : t₀ ∈ ball 0 δ)
    (hS : ContinuousAt S t₀) (hT : AnalyticAt ℂ T 0)
    {H : Set (ℂ × ℂ)}
    (hcenter : ImageBranch T N q₀ 0 = ImageBranch S E p₀ t₀)
    (hsub : ImageBranch T N q₀ '' ball 0 ρ ⊆ H)
    (hcaptured : ∀ᶠ u in 𝓝 (0 : ℂ),
      ImageBranch T N q₀ u ∈ ImageBranch S E p₀ '' ball 0 δ)
    (hgraph : ∃ F : ℂ → ℂ, ∀ᶠ y in 𝓝 (ImageBranch S E p₀ t₀),
      y ∈ ImageBranch S E p₀ '' ball 0 δ ↔ y.1 = F y.2) :
    ∀ᶠ t in 𝓝 t₀, ImageBranch S E p₀ t ∈ H := by
  obtain ⟨F, hgraph⟩ := hgraph
  let P : ℂ → ℂ := fun u => q₀ + u ^ N
  let Q : ℂ → ℂ := fun t => p₀ + t ^ E
  have hTcont : ContinuousAt (ImageBranch T N q₀) 0 :=
    hT.continuousAt.prodMk (continuousAt_const.add (continuousAt_id.pow N))
  have htendT : Tendsto (ImageBranch T N q₀) (𝓝 0)
      (𝓝 (ImageBranch S E p₀ t₀)) := by
    rw [← hcenter]
    exact hTcont
  have hbranch : ∀ᶠ u in 𝓝 (0 : ℂ), (F (P u), P u) ∈ H := by
    filter_upwards [htendT.eventually hgraph, hcaptured, ball_mem_nhds (0 : ℂ) hρ]
      with u huGraph huCaptured huBall
    have hfst : T u = F (P u) := huGraph.mp huCaptured
    rw [← hfst]
    exact hsub ⟨u, huBall, rfl⟩
  have hPQ : Q t₀ = P 0 := (congrArg Prod.snd hcenter).symm
  have hvalueH : ∀ᶠ t in 𝓝 t₀, (F (Q t), Q t) ∈ H :=
    eventually_graph_mem_of_analytic_subbranch
      (analyticAt_const.add (analyticAt_id.pow N)) (power_value_germ_nonconstant hN q₀)
      hbranch (continuousAt_const.add (continuousAt_id.pow E)) hPQ
  have hScont : ContinuousAt (ImageBranch S E p₀) t₀ :=
    hS.prodMk (continuousAt_const.add (continuousAt_id.pow E))
  filter_upwards [hScont.eventually hgraph, hvalueH, isOpen_ball.mem_nhds ht₀ball]
    with t htGraph htH htBall
  have hfst : S t = F (Q t) := htGraph.mp ⟨t, htBall, rfl⟩
  change (S t, Q t) ∈ H
  rw [hfst]
  exact htH

/-- Captured nonconstant analytic subbranches imply relative openness
of membership on a punctured raw branch.  The required single-graph
description is supplied by the proved collision lemma above. -/
theorem imageBranch_membership_isOpen_of_captured_subbranches
    {S : ℂ → ℂ} {E : ℕ} (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : AnalyticOnNhd ℂ S (ball 0 δ))
    (hcollision : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ ω : ℂ, ω ^ E = 1 →
      (S (ω * t) = S t ↔ ω ∈ PersistentSymmetries S E))
    {H : Set (ℂ × ℂ)}
    (hcover : ∀ t₀ : ℂ, ‖t₀‖ < δ → t₀ ≠ 0 → ImageBranch S E p₀ t₀ ∈ H →
      ∃ (T : ℂ → ℂ) (N : ℕ) (q₀ : ℂ) (ρ : ℝ),
        0 < N ∧ 0 < ρ ∧ AnalyticAt ℂ T 0 ∧
        ImageBranch T N q₀ 0 = ImageBranch S E p₀ t₀ ∧
        ImageBranch T N q₀ '' ball 0 ρ ⊆ H ∧
        ∀ᶠ u in 𝓝 (0 : ℂ), ImageBranch T N q₀ u ∈ ImageBranch S E p₀ '' ball 0 δ) :
    IsOpen ((fun t : {t : ℂ // t ∈ ball (0 : ℂ) δ \ {0}} =>
      ImageBranch S E p₀ t) ⁻¹' H) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t₀ ht₀H
  have ht₀ball : t₀.1 ∈ ball (0 : ℂ) δ := t₀.2.1
  have ht₀norm : ‖t₀.1‖ < δ := by
    simpa only [mem_ball, dist_zero_right] using ht₀ball
  have ht₀ne : t₀.1 ≠ 0 := by simpa only [mem_singleton_iff] using t₀.2.2
  obtain ⟨T, N, q₀, ρ, hN, hρ, hT, hcenter, hsub, hcaptured⟩ :=
    hcover t₀ ht₀norm ht₀ne ht₀H
  obtain ⟨F, _, _, hgraph⟩ :=
    imageBranch_noncentral_image_is_graph hE p₀ hδ hS hcollision ht₀norm ht₀ne
  have hevent := imageBranch_membership_eventually_of_captured_subbranch
    hN p₀ q₀ hρ ht₀ball (hS _ ht₀ball).continuousAt hT hcenter hsub hcaptured ⟨F, hgraph⟩
  exact (continuous_subtype_val.tendsto t₀).eventually hevent

/-- The captured-subbranch condition selects a whole branch meeting a
closed set, including its center.  In particular, it can be used in the
omitted-value continuation argument without an assumed analytic image
dimension theorem. -/
theorem imageBranch_full_branch_of_captured_subbranches
    {S : ℂ → ℂ} {E : ℕ} (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : AnalyticOnNhd ℂ S (ball 0 δ))
    (hcollision : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ ω : ℂ, ω ^ E = 1 →
      (S (ω * t) = S t ↔ ω ∈ PersistentSymmetries S E))
    {H : Set (ℂ × ℂ)} (hH : IsClosed H)
    (hcover : ∀ t₀ : ℂ, ‖t₀‖ < δ → t₀ ≠ 0 → ImageBranch S E p₀ t₀ ∈ H →
      ∃ (T : ℂ → ℂ) (N : ℕ) (q₀ : ℂ) (ρ : ℝ),
        0 < N ∧ 0 < ρ ∧ AnalyticAt ℂ T 0 ∧
        ImageBranch T N q₀ 0 = ImageBranch S E p₀ t₀ ∧
        ImageBranch T N q₀ '' ball 0 ρ ⊆ H ∧
        ∀ᶠ u in 𝓝 (0 : ℂ), ImageBranch T N q₀ u ∈ ImageBranch S E p₀ '' ball 0 δ)
    (hmeet : (ImageBranch S E p₀ '' (ball 0 δ \ {0}) ∩ H).Nonempty) :
    ImageBranch S E p₀ '' ball 0 δ ⊆ H := by
  exact imageBranch_full_branch_of_clopen_membership hδ hS.continuousOn E p₀ hH
    (imageBranch_membership_isOpen_of_captured_subbranches hE p₀ hδ hS hcollision hcover) hmeet

/-- The finite full-branch union itself is relatively closed in its
value cylinder. -/
theorem selected_imageBranches_full_closure {ι : Type*} {J : Set ι}
    (hJ : J.Finite) {S : ι → ℂ → ℂ} {E : ℕ} (hE : 0 < E) (p₀ : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hS : ∀ i ∈ J, ContinuousOn (S i) (closedBall 0 δ)) :
    closure (⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ) ∩
        BranchValueCylinder E p₀ δ =
      ⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ := by
  let P := ⋃ i ∈ J, ImageBranch (S i) E p₀ '' (ball 0 δ \ {0})
  let F := ⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ
  have hPF : P ⊆ F := by
    intro y hy
    simp only [P, F, mem_iUnion] at hy ⊢
    obtain ⟨i, hi, hy⟩ := hy
    exact ⟨i, hi, image_mono sdiff_subset hy⟩
  have hcloseP : closure P ∩ BranchValueCylinder E p₀ δ = F :=
    selected_imageBranches_punctured_closure hJ hE p₀ hδ hS
  have hFP : F ⊆ closure P := by
    intro y hy
    exact (hcloseP.superset hy).1
  have hclose : closure F = closure P :=
    Subset.antisymm (closure_minimal hFP isClosed_closure) (closure_mono hPF)
  change closure F ∩ BranchValueCylinder E p₀ δ = F
  rw [hclose]
  exact hcloseP

/-- A local sandwich by selected actual branch images determines the
closure exactly.  In the intended application, the lower inclusion is
the generic high fiber count and the upper inclusion permits central
exceptional fibers, provided they belong to a selected full branch. -/
theorem closure_of_local_selected_imageBranches {ι : Type*} {J : Set ι}
    (hJ : J.Finite) {S : ι → ℂ → ℂ} {E : ℕ} (hE : 0 < E) (p₀ : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hS : ∀ i ∈ J, ContinuousOn (S i) (closedBall 0 δ))
    {A W : Set (ℂ × ℂ)} (hW : IsOpen W) (hWcyl : W ⊆ BranchValueCylinder E p₀ δ)
    (hlower : (⋃ i ∈ J, ImageBranch (S i) E p₀ '' (ball 0 δ \ {0})) ∩ W ⊆ A)
    (hupper : A ∩ W ⊆ ⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ) :
    closure A ∩ W = (⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ) ∩ W := by
  let P := ⋃ i ∈ J, ImageBranch (S i) E p₀ '' (ball 0 δ \ {0})
  let F := ⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ
  have hcloseP : closure P ∩ BranchValueCylinder E p₀ δ = F :=
    selected_imageBranches_punctured_closure hJ hE p₀ hδ hS
  have hcloseF : closure F ∩ BranchValueCylinder E p₀ δ = F :=
    selected_imageBranches_full_closure hJ hE p₀ hδ hS
  apply Subset.antisymm
  · intro y hy
    have hyF : y ∈ closure F := closure_mono hupper (hW.closure_inter hy)
    exact ⟨hcloseF.subset ⟨hyF, hWcyl hy.2⟩, hy.2⟩
  · intro y hy
    have hyP : y ∈ closure P := (hcloseP.superset hy.1).1
    exact ⟨closure_mono hlower (hW.closure_inter ⟨hyP, hy.2⟩), hy.2⟩

/-- Restricting a full nonconstant raw branch to an open target
neighborhood preserves openness of its product projection. -/
theorem imageBranch_restricted_product_projection_isOpen {S : ℂ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hS : AnalyticOnNhd ℂ S (ball 0 δ))
    (hne : ¬∀ᶠ t in 𝓝 (0 : ℂ), S t = S 0) (E : ℕ) (p₀ : ℂ)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W) :
    IsOpen (Prod.fst '' ((ImageBranch S E p₀ '' ball 0 δ) ∩ W)) := by
  have hnotconst : ¬∃ c : ℂ, ∀ t ∈ ball 0 δ, S t = c := by
    rintro ⟨c, hc⟩
    apply hne
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with t ht
    exact (hc t ht).trans (hc 0 (mem_ball_self hδ)).symm
  have hopen := (hS.is_constant_or_isOpen isPreconnected_ball).resolve_left hnotconst
  let U := ball (0 : ℂ) δ ∩ ImageBranch S E p₀ ⁻¹' W
  have hU : IsOpen U :=
    (imageBranch_continuousOn hS.continuousOn E p₀).isOpen_inter_preimage isOpen_ball hW
  have heq : Prod.fst '' ((ImageBranch S E p₀ '' ball 0 δ) ∩ W) = S '' U := by
    ext x
    constructor
    · rintro ⟨y, ⟨⟨t, ht, rfl⟩, htW⟩, rfl⟩
      exact ⟨t, ⟨ht, htW⟩, rfl⟩
    · rintro ⟨t, ⟨ht, htW⟩, rfl⟩
      exact ⟨ImageBranch S E p₀ t, ⟨⟨t, ht, rfl⟩, htW⟩, rfl⟩
  rw [heq]
  exact hopen U inter_subset_left hU

/-- A finite local high-count branch sandwich gives an open local
product projection of the closure, with no assumed global degree or
assumed openness of that projection. -/
theorem local_selected_imageBranches_closure_projection_isOpen
    {ι : Type*} {J : Set ι} (hJ : J.Finite) {S : ι → ℂ → ℂ}
    {E : ℕ} (hE : 0 < E) (p₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ i ∈ J, AnalyticOnNhd ℂ (S i) (closedBall 0 δ))
    (hne : ∀ i ∈ J, ¬∀ᶠ t in 𝓝 (0 : ℂ), S i t = S i 0)
    {A W : Set (ℂ × ℂ)} (hW : IsOpen W) (hWcyl : W ⊆ BranchValueCylinder E p₀ δ)
    (hlower : (⋃ i ∈ J, ImageBranch (S i) E p₀ '' (ball 0 δ \ {0})) ∩ W ⊆ A)
    (hupper : A ∩ W ⊆ ⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ) :
    IsOpen (Prod.fst '' (closure A ∩ W)) := by
  rw [closure_of_local_selected_imageBranches hJ hE p₀ hδ
    (fun i hi => (hS i hi).continuousOn) hW hWcyl hlower hupper]
  have hdistrib : (⋃ i ∈ J, ImageBranch (S i) E p₀ '' ball 0 δ) ∩ W =
      ⋃ i ∈ J, ((ImageBranch (S i) E p₀ '' ball 0 δ) ∩ W) := by
    ext y
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨i, hi, hy⟩, hyW⟩
      exact ⟨i, hi, hy, hyW⟩
    · rintro ⟨i, hi, hy, hyW⟩
      exact ⟨⟨i, hi, hy⟩, hyW⟩
  rw [hdistrib]
  simp only [image_iUnion]
  apply isOpen_iUnion
  intro i
  apply isOpen_iUnion
  intro hi
  exact imageBranch_restricted_product_projection_isOpen hδ
    ((hS i hi).mono ball_subset_closedBall) (hne i hi) E p₀ hW

end

end MaximumModulus
