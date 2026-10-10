module

public import MaximumModulus.FiniteTargetCover
public import MaximumModulus.ExceptionalRadii
public import MaximumModulus.GeometricReduction

@[expose] public section

open Set Filter Metric
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- The exceptional set consists of actual finite target-image points whose entire
image germ is not a single analytic graph. -/
def FiniteSingularTargets (m : ℕ) (g : ℂ → ℂ) : Set (FiniteCorrespondenceTarget m) :=
  {y | y.val ∈ FiniteLogDerivativeImage m g ∧ ¬IsSingleValueGraph m g y.val}

/-- A constructed local cover contains at most its center as an exceptional image
point, because every punctured branch point has an actual total-image graph. -/
theorem FiniteTargetBranchCover.singular_inter_subset_center
    {m : ℕ} {g : ℂ → ℂ} {s₀ p₀ : ℂ} (C : FiniteTargetBranchCover m g s₀ p₀) :
    {z : ℂ × ℂ | z ∈ FiniteLogDerivativeImage m g ∧ ¬IsSingleValueGraph m g z} ∩ C.W ⊆
      {(s₀, p₀)} := by
  intro z hz
  have himage := (C.imageCover z hz.2).mp hz.1.1
  obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.mp himage
  have hnorm : ‖t‖ < C.δ := by simpa only [mem_ball, dist_zero_right] using ht
  by_cases hzero : t = 0
  · simp only [mem_singleton_iff]
    simp only [ImageBranch, hzero, C.center j, zero_pow C.posN.ne', add_zero]
  · exact False.elim (hz.1.2 (C.regular_at_punctured_branch j hnorm hzero))

/-- Local finiteness of the actual finite singular target set follows from the
constructed proper-map covers. -/
theorem finiteSingularTargets_locally_finite {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    LocallyFiniteExceptionalSet (FiniteSingularTargets m g) := by
  intro y
  obtain ⟨C⟩ := finiteTargetBranchCover_exists hg hg0 hnm hfactor y.property.1 y.property.2
  let U : Set (FiniteCorrespondenceTarget m) := Subtype.val ⁻¹' C.W
  have hU : IsOpen U := C.openW.preimage continuous_subtype_val
  have hyU : y ∈ U := C.centerW
  refine ⟨U, hU.mem_nhds hyU, (Set.finite_singleton y).subset ?_⟩
  intro z hz
  have heq : z.val = y.val := by
    exact mem_singleton_iff.mp (C.singular_inter_subset_center ⟨hz.1, hz.2⟩)
  exact mem_singleton_iff.mpr (Subtype.ext heq)

/-- The actual singular finite targets form a countable set. No local finiteness
at the omitted value or infinity is assumed or needed for this finite chart. -/
theorem finiteSingularTargets_countable {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    (FiniteSingularTargets m g).Countable := by
  have hopen : IsOpen {y : ℂ × ℂ | y.1 ≠ 0 ∧ y.2 ≠ (m : ℂ)} :=
    (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)
  have : LocallyCompactSpace (FiniteCorrespondenceTarget m) := hopen.locallyCompactSpace
  exact countable_of_locallyFiniteExceptionalSet
    (finiteSingularTargets_locally_finite hg hg0 hnm hfactor)

/-- Only countably many positive radii have squared product above any actual
singular finite target. -/
theorem finiteSingularSquareRadii_countable {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    (ExceptionalSquareRadii (fun y : FiniteCorrespondenceTarget m => y.val.1)
      (FiniteSingularTargets m g)).Countable :=
  countable_exceptionalSquareRadii _ (finiteSingularTargets_countable hg hg0 hnm hfactor)

/-- Off the constructed exceptional radius set, every actual finite target-image
point with that positive squared product is regular. -/
theorem regular_finite_target_off_exceptional_square_radius {m : ℕ} {g : ℂ → ℂ}
    {r : ℝ} (hr : 0 < r)
    (hrgood : r ∉ ExceptionalSquareRadii (fun y : FiniteCorrespondenceTarget m => y.val.1)
      (FiniteSingularTargets m g))
    {p : ℂ} (hp : p ≠ (m : ℂ))
    (himage : ((r : ℂ) ^ 2, p) ∈ FiniteLogDerivativeImage m g) :
    IsSingleValueGraph m g ((r : ℂ) ^ 2, p) := by
  have hs : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.ne')
  by_contra hregular
  let y : FiniteCorrespondenceTarget m := ⟨((r : ℂ) ^ 2, p), hs, hp⟩
  exact hrgood ⟨hr, y, ⟨himage, hregular⟩, rfl⟩

/-- Emptiness of the actual regular high-count locus yields the exact positive-product
fiber estimate with the constructed countable exceptional radius set. The analytic
continuation argument proving that emptiness remains a separate premise. -/
theorem positiveProductFiberBound_of_regular_high_count_empty
    {f g : ℂ → ℂ} {m L : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z)
    (hempty : RegularLogDerivativeHighCount m g L = ∅) :
    PositiveProductFiberBound (normalizedLogDerivative m g) m L := by
  let E := ExceptionalSquareRadii (fun y : FiniteCorrespondenceTarget m => y.val.1)
    (FiniteSingularTargets m g)
  refine ⟨E, finiteSingularSquareRadii_countable hg hg0 hnm hfactor, ?_⟩
  intro r hr hrgood p hp
  have hp' : (p : ℂ) ≠ (m : ℂ) := by exact_mod_cast (ne_of_gt hp)
  have hs : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.ne')
  by_cases himage : ((r : ℂ) ^ 2, (p : ℂ)) ∈ FiniteLogDerivativeImage m g
  · exact normalized_inversePairs_bound_at_regular_target hg hg0 m L hempty hs hp'
      (regular_finite_target_off_exceptional_square_radius hr hrgood hp' himage)
  · have hemptyfiber : InversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) ((r : ℂ) ^ 2) ((p : ℂ) : OnePoint ℂ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp himage
    rw [← sphere_inversePairs_eq_normalized m _ hp', hemptyfiber]
    exact ⟨Set.finite_empty, by simp⟩

end MaximumModulus
