module

public import MaximumModulus.HighCountLocus
public import MaximumModulus.HighCountInterior
public import MaximumModulus.InfinityInterior
public import MaximumModulus.OmittedTargetCover

@[expose] public section

open Set
open scoped Topology OnePoint

noncomputable section

namespace MaximumModulus

/-- The closure of the actual regular high-count locus stays away from zero
product, including at the omitted spherical value and infinity. -/
theorem regularLogDerivativeHighCount_closure_product_ne_zero
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) {y : ℂ × OnePoint ℂ}
    (hy : y ∈ closure (RegularLogDerivativeHighCount m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0))) :
    y.1 ≠ 0 := by
  obtain ⟨ε, hε, havoid⟩ :=
    regularLogDerivativeHighCount_closure_avoids_small_products hg hg0 hnm hfactor
  intro heq
  apply havoid hy
  change y.1 ∈ Metric.ball (0 : ℂ) (ε ^ 2)
  rw [heq]
  exact Metric.mem_ball_self (pow_pos hε 2)

/-- All finite, omitted, and infinite value cases give open projection of
the closure of the actual regular high-count locus. -/
theorem regularLogDerivativeHighCount_open_closure_projection
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) :
    IsOpen (Prod.fst '' closure (RegularLogDerivativeHighCount m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0))) := by
  apply isOpen_projection_of_open_local_projections
  rintro ⟨s, p⟩ hy
  have hs := regularLogDerivativeHighCount_closure_product_ne_zero hg hg0 hnm hfactor hy
  cases p using OnePoint.rec with
  | infty =>
      exact regularLogDerivativeHighCount_open_local_projection_at_infinity
        hg hg0 hnm hfactor _ hs
  | coe p =>
      by_cases hp : p = (m : ℂ)
      · subst p
        exact regular_high_count_closure_omitted_local_projection_isOpen hg hg0 hnm hfactor hs
      · exact regular_high_count_closure_finite_local_projection_isOpen hg hg0 hnm hfactor hs hp

/-- The actual regular high-count locus is empty, with every analytic
continuation and projection premise supplied by proved constructions. -/
theorem regularLogDerivativeHighCount_empty
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) :
    RegularLogDerivativeHighCount m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) = ∅ :=
  regularLogDerivativeHighCount_empty_of_open_closure_projection hg hg0 hnm hfactor
    (regularLogDerivativeHighCount_open_closure_projection hg hg0 hnm hfactor)

end MaximumModulus
