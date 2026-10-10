module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

open Set
open scoped Topology

namespace MaximumModulus

/-- A compact family cannot develop new preimages away from an open
neighborhood of its central fiber. This includes the bounded surviving
pairs used at the omitted value. -/
theorem compact_fiber_capture {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {F : X → Y} {K U : Set X} (hK : IsCompact K)
    (hF : ContinuousOn F K) (hU : IsOpen U) {y : Y}
    (hcapture : ∀ x ∈ K, F x = y → x ∈ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∀ x ∈ K, F x ∈ V → x ∈ U := by
  have hcompact : IsCompact (K ∩ Uᶜ) := hK.inter_right hU.isClosed_compl
  have himage : IsClosed (F '' (K ∩ Uᶜ)) :=
    (hcompact.image_of_continuousOn (hF.mono inter_subset_left)).isClosed
  refine ⟨(F '' (K ∩ Uᶜ))ᶜ, himage.isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, ⟨hxK, hxU⟩, hxy⟩
    exact hxU (hcapture x hxK hxy)
  · intro x hxK hxV
    by_contra hxU
    exact hxV ⟨x, ⟨hxK, hxU⟩, rfl⟩

/-- Closed maps capture all nearby fibers in any open set containing the
central fiber. Properness supplies this closed-map premise. -/
theorem closedMap_fiber_capture {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F : X → Y} (hF : IsClosedMap F) {U : Set X} (hU : IsOpen U) {y : Y}
    (hcapture : F ⁻¹' {y} ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ F ⁻¹' V ⊆ U := by
  have hclosed : IsClosed (F '' Uᶜ) := hF _ hU.isClosed_compl
  refine ⟨(F '' Uᶜ)ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hxU, hxy⟩
    exact hxU (hcapture (by simpa using hxy))
  · intro x hxV
    by_contra hxU
    exact hxV ⟨x, hxU, rfl⟩

end MaximumModulus
