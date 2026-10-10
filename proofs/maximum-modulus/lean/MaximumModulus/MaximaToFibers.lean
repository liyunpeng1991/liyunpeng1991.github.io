module

public import MaximumModulus.Finiteness
public import MaximumModulus.SmallFibers

@[expose] public section

open Set
open scoped ComplexConjugate

namespace MaximumModulus

/-- This is the actual ordered pair associated to a maximum point. -/
def conjugatePair (z : ℂ) : ℂ × ℂ := (z, conj z)

theorem conjugatePair_injective : Function.Injective conjugatePair := by
  intro z w h
  exact congrArg Prod.fst h

/-- The common real logarithmic-derivative value, when established, sends
each maximum point to a fiber of the reflected correspondence. -/
theorem maxPoints_mapsTo_inversePairs
    (f q : ℂ → ℂ) (r p : ℝ)
    (hvalue : ∀ z ∈ MaxPoints f r, q z = (p : ℂ)) :
    MapsTo conjugatePair (MaxPoints f r)
      (InversePairs q (reflection q) ((r : ℂ) ^ 2) (p : ℂ)) := by
  intro z hz
  refine ⟨?_, hvalue z hz, ?_⟩
  · change z * conj z = (r : ℂ) ^ 2
    rw [Complex.mul_conj', hz.1]
  · change conj (q (conj (conj z))) = (p : ℂ)
    simp [hvalue z hz]

/-- A finite fiber gives both actual finiteness and a cardinality bound.
No conclusion is obtained from an infinite fiber's `ncard`. -/
theorem maxPoints_finite_ncard_le_inversePairs
    (f q : ℂ → ℂ) (r p : ℝ)
    (hvalue : ∀ z ∈ MaxPoints f r, q z = (p : ℂ))
    (hfinite : (InversePairs q (reflection q) ((r : ℂ) ^ 2) (p : ℂ)).Finite) :
    (MaxPoints f r).Finite ∧
      (MaxPoints f r).ncard ≤
        (InversePairs q (reflection q) ((r : ℂ) ^ 2) (p : ℂ)).ncard := by
  have hmap := maxPoints_mapsTo_inversePairs f q r p hvalue
  have hfinimage : (conjugatePair '' MaxPoints f r).Finite :=
    hfinite.subset hmap.image_subset
  refine ⟨?_, Set.ncard_le_ncard_of_injOn conjugatePair hmap
    conjugatePair_injective.injOn hfinite⟩
  exact hfinimage.of_finite_image conjugatePair_injective.injOn

end MaximumModulus
