module

public import MaximumModulus.HighCountLocus
public import MaximumModulus.LocalImageTopology

@[expose] public section

open Set Filter Topology
open scoped Topology

noncomputable section

namespace MaximumModulus

/-- The ordinary finite-value coordinate chart in the spherical target. -/
def finiteValueEmbedding : ℂ × ℂ → ℂ × OnePoint ℂ :=
  fun y => (y.1, (y.2 : OnePoint ℂ))

theorem finiteValueEmbedding_isOpenEmbedding : IsOpenEmbedding finiteValueEmbedding := by
  exact IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe

theorem finiteValueEmbedding_continuous : Continuous finiteValueEmbedding :=
  finiteValueEmbedding_isOpenEmbedding.continuous

/-- Open finite coordinates commute with closure, so spherical closure
membership at finite values is exactly ordinary closure membership. -/
theorem finiteValueEmbedding_preimage_closure (A : Set (ℂ × OnePoint ℂ)) :
    finiteValueEmbedding ⁻¹' closure A = closure (finiteValueEmbedding ⁻¹' A) :=
  finiteValueEmbedding_isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    finiteValueEmbedding_continuous A

def FiniteRegularLogDerivativeHighCount (m : ℕ) (g : ℂ → ℂ) (L : ℕ) : Set (ℂ × ℂ) :=
  finiteValueEmbedding ⁻¹' RegularLogDerivativeHighCount m g L

theorem finiteRegularLogDerivativeHighCount_omits_common_value
    (m : ℕ) (g : ℂ → ℂ) (L : ℕ) {y : ℂ × ℂ}
    (hy : y ∈ FiniteRegularLogDerivativeHighCount m g L) : y.2 ≠ (m : ℂ) := by
  intro heq
  exact hy.1.2.1 (by simp [finiteValueEmbedding, heq])

theorem finiteRegularLogDerivativeHighCount_closure (m : ℕ) (g : ℂ → ℂ) (L : ℕ) :
    finiteValueEmbedding ⁻¹' closure (RegularLogDerivativeHighCount m g L) =
      closure (FiniteRegularLogDerivativeHighCount m g L) :=
  finiteValueEmbedding_preimage_closure _

/-- An open local product projection proved in ordinary finite coordinates
transfers to an open local product projection in the actual spherical target. -/
theorem finiteValueEmbedding_open_local_projection {H : Set (ℂ × OnePoint ℂ)}
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hproj : IsOpen (Prod.fst '' ((finiteValueEmbedding ⁻¹' H) ∩ W))) :
    IsOpen (finiteValueEmbedding '' W) ∧
      IsOpen (Prod.fst '' (H ∩ (finiteValueEmbedding '' W))) := by
  refine ⟨finiteValueEmbedding_isOpenEmbedding.isOpenMap W hW, ?_⟩
  have heq : Prod.fst '' (H ∩ (finiteValueEmbedding '' W)) =
      Prod.fst '' ((finiteValueEmbedding ⁻¹' H) ∩ W) := by
    ext s
    constructor
    · rintro ⟨y, ⟨hy, x, hx, rfl⟩, rfl⟩
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hxH, hxW⟩, rfl⟩
      exact ⟨finiteValueEmbedding x, ⟨hxH, x, hxW, rfl⟩, rfl⟩
  rw [heq]
  exact hproj

end MaximumModulus
