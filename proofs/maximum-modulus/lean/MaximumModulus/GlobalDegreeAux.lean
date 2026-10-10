module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
A topological reduction used in the high-count-locus argument.

The intended set `E` is the set of smooth targets with too many actual
inverse pairs. Analytic local-branch arguments in `HighCountInterior`,
`InfinityInterior`, and `OmittedTargetCover` prove that the projection of
its closure is open; `HighCountGlobal` assembles them. The topological
theorems below retain explicit inputs and are not alone the all-radii proof.

The compact second factor makes projection of a closed set closed.  Thus
openness of the projection alone propagates nonemptiness to every point
of a connected first factor.  Working with the closure of the whole bad
locus avoids choosing global irreducible components or gluing their
degrees along their regular loci.
-/

namespace MaximumModulus

open Set

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
  [PreconnectedSpace X] [CompactSpace P]

omit [PreconnectedSpace X] [CompactSpace P] in
/-- Open local projection charts cover an open global projection. -/
theorem isOpen_projection_of_open_local_projections {H : Set (X × P)}
    (hlocal : ∀ y ∈ H, ∃ W : Set (X × P),
      IsOpen W ∧ y ∈ W ∧ IsOpen (Prod.fst '' (H ∩ W))) :
    IsOpen (Prod.fst '' H) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨W, _, hyW, hproj⟩ := hlocal y hy
  exact Filter.mem_of_superset (hproj.mem_nhds ⟨y, ⟨hy, hyW⟩, rfl⟩)
    (image_mono inter_subset_left)

/-- A nonempty closed subset of a product with compact second factor
projects onto the connected first factor if its projection is open. -/
theorem closed_locus_projects_surjectively {H : Set (X × P)}
    (hclosed : IsClosed H) (hopen : IsOpen (Prod.fst '' H))
    (hne : H.Nonempty) : Prod.fst '' H = Set.univ := by
  apply IsClopen.eq_univ
  · exact ⟨isClosedMap_fst_of_compactSpace H hclosed, hopen⟩
  · exact hne.image Prod.fst

/-- The closure of a bad locus is empty if its projection is open and
the bad locus avoids a nonempty open cylinder.  The latter exclusion
automatically persists to its closure; no separate boundary-fiber bound
is required for this topological step. -/
theorem bad_locus_empty_of_open_closure_projection {E : Set (X × P)}
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (havoid : Disjoint E (Prod.fst ⁻¹' U))
    (hopen : IsOpen (Prod.fst '' closure E)) : E = ∅ := by
  by_contra hne
  have hEnonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hHnonempty : (closure E).Nonempty := hEnonempty.mono subset_closure
  have hsurj : Prod.fst '' closure E = Set.univ :=
    closed_locus_projects_surjectively isClosed_closure hopen hHnonempty
  obtain ⟨x, hx⟩ := hUne
  have hximage : x ∈ Prod.fst '' closure E := by rw [hsurj]; trivial
  obtain ⟨y, hy, hxy⟩ := hximage
  have hsub : closure E ⊆ (Prod.fst ⁻¹' U)ᶜ := by
    apply closure_minimal
    · intro z hz hzU
      exact Set.disjoint_left.mp havoid hz hzU
    · exact (hU.preimage continuous_fst).isClosed_compl
  exact hsub hy (by simpa [hxy] using hx)

/-- The closure method needs only local open projection charts. -/
theorem bad_locus_empty_of_open_local_closure_projections {E : Set (X × P)}
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (havoid : Disjoint E (Prod.fst ⁻¹' U))
    (hlocal : ∀ y ∈ closure E, ∃ W : Set (X × P),
      IsOpen W ∧ y ∈ W ∧ IsOpen (Prod.fst '' (closure E ∩ W))) : E = ∅ := by
  exact bad_locus_empty_of_open_closure_projection hU hUne havoid
    (isOpen_projection_of_open_local_projections hlocal)

end MaximumModulus
