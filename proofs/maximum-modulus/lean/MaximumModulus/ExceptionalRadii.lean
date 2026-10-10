module

public import MaximumModulus.MeromorphicCorrespondence
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

open Set Filter
open scoped Topology OnePoint

noncomputable section

namespace MaximumModulus

/-- The neighborhood formulation of a locally finite exceptional subset. -/
def LocallyFiniteExceptionalSet {X : Type*} [TopologicalSpace X] (E : Set X) : Prop :=
  ∀ x : X, ∃ U ∈ 𝓝 x, (E ∩ U).Finite

/-- Existing mathlib local-finiteness countability applies to the family of
singleton exceptional points. -/
theorem countable_of_locallyFiniteExceptionalSet {X : Type*} [TopologicalSpace X]
    [SigmaCompactSpace X] {E : Set X} (hE : LocallyFiniteExceptionalSet E) : E.Countable := by
  have hsingle : LocallyFinite (fun e : E => ({(e : X)} : Set X)) := by
    intro x
    obtain ⟨U, hU, hfinite⟩ := hE x
    refine ⟨U, hU, ?_⟩
    have hmaps : Set.MapsTo Subtype.val {e : E | (({(e : X)} : Set X) ∩ U).Nonempty}
        (E ∩ U) := by
      intro e he
      obtain ⟨y, hy, hyU⟩ := he
      have hye : y = (e : X) := mem_singleton_iff.mp hy
      exact ⟨e.property, by simpa [hye] using hyU⟩
    exact Set.Finite.of_injOn hmaps Subtype.val_injective.injOn hfinite
  have hcount := hsingle.countable_univ (fun e => Set.singleton_nonempty (e : X))
  exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hcount)

/-- Continuous injective charts preserve local finiteness of exceptional sets. -/
theorem locallyFiniteExceptionalSet_preimage {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {F : X → Y}
    (hF : Continuous F) (hinj : Function.Injective F) {E : Set Y}
    (hE : LocallyFiniteExceptionalSet E) : LocallyFiniteExceptionalSet (F ⁻¹' E) := by
  intro x
  obtain ⟨U, hU, hfinite⟩ := hE (F x)
  refine ⟨F ⁻¹' U, hF.continuousAt.preimage_mem_nhds hU, ?_⟩
  rw [← Set.preimage_inter]
  exact hfinite.preimage hinj.injOn

/-- Finite-value target chart, omitting zero products and the common value. -/
abbrev FiniteCorrespondenceTarget (m : ℕ) :=
  {y : ℂ × ℂ // y.1 ≠ 0 ∧ y.2 ≠ (m : ℂ)}

/-- The finite chart embeds in the actual spherical target. -/
def finiteCorrespondenceTargetMap (m : ℕ) :
    FiniteCorrespondenceTarget m → SphereCorrespondenceTarget m :=
  fun y => ⟨(y.val.1, (y.val.2 : OnePoint ℂ)), y.property.1,
    by simpa using y.property.2⟩

/-- The infinity slice of the actual spherical target. -/
def infiniteCorrespondenceTargetMap (m : ℕ) :
    ({s : ℂ // s ≠ 0}) → SphereCorrespondenceTarget m :=
  fun s => ⟨(s.val, ∞), s.property, OnePoint.infty_ne_coe _⟩

theorem continuous_finiteCorrespondenceTargetMap (m : ℕ) :
    Continuous (finiteCorrespondenceTargetMap m) := by
  apply Continuous.subtype_mk
  exact (continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)).comp continuous_subtype_val

theorem injective_finiteCorrespondenceTargetMap (m : ℕ) :
    Function.Injective (finiteCorrespondenceTargetMap m) := by
  intro y y' heq
  apply Subtype.ext
  have hfirst : y.val.1 = y'.val.1 :=
    congrArg (fun x : SphereCorrespondenceTarget m => x.val.1) heq
  have hsecond : (y.val.2 : OnePoint ℂ) = (y'.val.2 : OnePoint ℂ) :=
    congrArg (fun x : SphereCorrespondenceTarget m => x.val.2) heq
  exact Prod.ext hfirst (OnePoint.coe_injective hsecond)

theorem continuous_infiniteCorrespondenceTargetMap (m : ℕ) :
    Continuous (infiniteCorrespondenceTargetMap m) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.prodMk continuous_const

theorem injective_infiniteCorrespondenceTargetMap (m : ℕ) :
    Function.Injective (infiniteCorrespondenceTargetMap m) := by
  intro y y' heq
  exact Subtype.ext (congrArg (fun x : SphereCorrespondenceTarget m => x.val.1) heq)

/-- A locally finite exceptional set in the actual open spherical target is
countable. The proof uses the finite chart and infinity slice, rather than
assuming ambient local finiteness at the omitted value. -/
theorem countable_exceptional_sphere_targets {m : ℕ} {E : Set (SphereCorrespondenceTarget m)}
    (hE : LocallyFiniteExceptionalSet E) : E.Countable := by
  have hopen : IsOpen {y : ℂ × ℂ | y.1 ≠ 0 ∧ y.2 ≠ (m : ℂ)} :=
    (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)
  have : LocallyCompactSpace (FiniteCorrespondenceTarget m) := hopen.locallyCompactSpace
  have : LocallyCompactSpace {s : ℂ // s ≠ 0} := isOpen_ne.locallyCompactSpace
  have hfin := countable_of_locallyFiniteExceptionalSet
    (locallyFiniteExceptionalSet_preimage (continuous_finiteCorrespondenceTargetMap m)
      (injective_finiteCorrespondenceTargetMap m) hE)
  have hinf := countable_of_locallyFiniteExceptionalSet
    (locallyFiniteExceptionalSet_preimage (continuous_infiniteCorrespondenceTargetMap m)
      (injective_infiniteCorrespondenceTargetMap m) hE)
  apply ((hfin.image (finiteCorrespondenceTargetMap m)).union
    (hinf.image (infiniteCorrespondenceTargetMap m))).mono
  intro y hy
  rcases y with ⟨⟨s, p⟩, hs, hp⟩
  induction p using OnePoint.rec with
  | infty =>
    apply Set.mem_union_right
    refine ⟨⟨s, hs⟩, hy, ?_⟩
    rfl
  | coe p =>
    have hpm : p ≠ (m : ℂ) := by simpa using hp
    apply Set.mem_union_left
    refine ⟨⟨(s, p), hs, hpm⟩, hy, ?_⟩
    rfl

/-- Real positive radii whose squared complex product lies above an exceptional target. -/
def ExceptionalSquareRadii {Y : Type*} (π : Y → ℂ) (E : Set Y) : Set ℝ :=
  {r | 0 < r ∧ ∃ y ∈ E, π y = (r : ℂ) ^ 2}

/-- Squaring is injective on positive radii, so a countable exceptional target
set excludes only countably many positive circles. -/
theorem countable_exceptionalSquareRadii {Y : Type*} (π : Y → ℂ) {E : Set Y}
    (hE : E.Countable) : (ExceptionalSquareRadii π E).Countable := by
  have hmaps : Set.MapsTo (fun r : ℝ => (r : ℂ) ^ 2) (ExceptionalSquareRadii π E) (π '' E) := by
    intro r hr
    obtain ⟨y, hy, hπ⟩ := hr.2
    exact ⟨y, hy, hπ⟩
  have hinj : Set.InjOn (fun r : ℝ => (r : ℂ) ^ 2) (ExceptionalSquareRadii π E) := by
    intro r hr s hs heq
    have hnorm := congrArg norm heq
    have hsquares : r ^ 2 = s ^ 2 := by
      simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1, abs_of_pos hs.1] using hnorm
    nlinarith [hr.1, hs.1]
  exact hmaps.countable_of_injOn hinj (hE.image π)

/-- Locally finite target exceptions yield the countable radius set required
by the radius-selection argument. This does not assert local finiteness of
the actual singular set; that remains a chart-assembly obligation. -/
theorem countable_exceptional_sphere_radii {m : ℕ} {E : Set (SphereCorrespondenceTarget m)}
    (hE : LocallyFiniteExceptionalSet E) :
    (ExceptionalSquareRadii (fun y : SphereCorrespondenceTarget m => y.val.1) E).Countable := by
  exact countable_exceptionalSquareRadii _ (countable_exceptional_sphere_targets hE)

end MaximumModulus
