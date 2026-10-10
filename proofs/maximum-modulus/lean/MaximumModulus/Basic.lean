module

public import MaximumModulus.Definitions
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Order.Compact

@[expose] public section

open Set Metric

namespace MaximumModulus

theorem maxPoints_subset_sphere (f : ℂ → ℂ) (r : ℝ) :
    MaxPoints f r ⊆ sphere (0 : ℂ) r := by
  intro z hz
  simpa [mem_sphere_iff_norm] using hz.1

theorem maxPoints_nonempty {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ}
    (hr : 0 ≤ r) : (MaxPoints f r).Nonempty := by
  have hnon : (sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp [mem_sphere_iff_norm, abs_of_nonneg hr]
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn hnon
    hf.norm.continuousOn
  refine ⟨z, ?_, ?_⟩
  · simpa [mem_sphere_iff_norm] using hz
  · intro w hw
    exact hmax (by simpa [mem_sphere_iff_norm] using hw)

theorem norm_eq_of_mem_maxPoints {f : ℂ → ℂ} {r : ℝ} {z w : ℂ}
    (hz : z ∈ MaxPoints f r) (hw : w ∈ MaxPoints f r) : ‖f z‖ = ‖f w‖ :=
  le_antisymm (hw.2 z hz.1) (hz.2 w hw.1)

theorem maxPoints_eq_norm_level {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hz : z ∈ MaxPoints f r) :
    MaxPoints f r = {w : ℂ | ‖w‖ = r ∧ ‖f w‖ = ‖f z‖} := by
  ext w
  constructor
  · intro hw
    exact ⟨hw.1, norm_eq_of_mem_maxPoints hw hz⟩
  · rintro ⟨hwr, hvalue⟩
    refine ⟨hwr, ?_⟩
    intro v hv
    rw [hvalue]
    exact hz.2 v hv

end MaximumModulus
