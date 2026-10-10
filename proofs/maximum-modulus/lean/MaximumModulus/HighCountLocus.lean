module

public import MaximumModulus.HighCountCapture
public import MaximumModulus.GlobalDegreeAux

@[expose] public section

open Set Filter Metric
open scoped Topology OnePoint

noncomputable section

namespace MaximumModulus

/-- The finite-value target image, defined using actual spherical function
values and actual ordered inverse pairs. -/
def FiniteLogDerivativeImage (m : ℕ) (g : ℂ → ℂ) : Set (ℂ × ℂ) :=
  {y | (InversePairs (sphereLogDerivative m g)
    (sphereLogDerivative m (reflection g)) y.1 (y.2 : OnePoint ℂ)).Nonempty}

/-- Regularity here means that the entire actual target image is locally
one analytic graph over the common finite value. It is not merely regularity
of a chosen parameter branch. -/
def IsSingleValueGraph (m : ℕ) (g : ℂ → ℂ) (y : ℂ × ℂ) : Prop :=
  ∃ F : ℂ → ℂ, AnalyticAt ℂ F y.2 ∧ F y.2 = y.1 ∧
    ∀ᶠ y' in 𝓝 y, y' ∈ FiniteLogDerivativeImage m g ↔ y'.1 = F y'.2

/-- The actual finite-value regular high-count locus used by the reduced
continuation route. Singular high-count targets are deliberately excluded. -/
def RegularLogDerivativeHighCount (m : ℕ) (g : ℂ → ℂ) (L : ℕ) :
    Set (ℂ × OnePoint ℂ) :=
  {y | y ∈ LogDerivativeHighCount m g L ∧
    ∃ p : ℂ, y.2 = (p : OnePoint ℂ) ∧ IsSingleValueGraph m g (y.1, p)}

theorem regularLogDerivativeHighCount_subset (m : ℕ) (g : ℂ → ℂ) (L : ℕ) :
    RegularLogDerivativeHighCount m g L ⊆ LogDerivativeHighCount m g L :=
  fun _ hy => hy.1

/-- The actual high-count locus avoids a full small-product cylinder for
every spherical common value, so this exclusion survives taking its closure. -/
theorem regularLogDerivativeHighCount_closure_avoids_small_products
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧
      closure (RegularLogDerivativeHighCount m g
        (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)) ⊆
      (Prod.fst ⁻¹' ball (0 : ℂ) (ε ^ 2))ᶜ := by
  obtain ⟨ε, hε, hsmall⟩ := sphereLogDerivative_small_product_bound hg hg0 hnm hfactor
  refine ⟨ε, hε, closure_minimal ?_ (isOpen_ball.preimage continuous_fst).isClosed_compl⟩
  intro y hy hyball
  have hyhigh := hy.1
  have hnorm : ‖y.1‖ < ε ^ 2 := by simpa [mem_ball_iff_norm] using hyball
  have hbound := (hsmall y.1 y.2 hyhigh.1 hnorm).2
  exact (not_le_of_gt hyhigh.2.2.2) hbound

/-- The topological contradiction is fully instantiated for the actual
regular high-count locus. Its remaining analytic premise is open projection
of that locus's closure, including across the omitted value and infinity. -/
theorem regularLogDerivativeHighCount_empty_of_open_closure_projection
    {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z)
    (hopen : IsOpen (Prod.fst '' closure (RegularLogDerivativeHighCount m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)))) :
    RegularLogDerivativeHighCount m g
      (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) = ∅ := by
  obtain ⟨ε, hε, havoid⟩ :=
    regularLogDerivativeHighCount_closure_avoids_small_products hg hg0 hnm hfactor
  apply bad_locus_empty_of_open_closure_projection isOpen_ball
    ⟨0, mem_ball_self (pow_pos hε 2)⟩ ?_ hopen
  apply Set.disjoint_left.mpr
  intro y hy hyball
  exact havoid (subset_closure hy) hyball

/-- Away from the common value, assigning infinity at zeros produces exactly
the same finite-valued inverse pairs as the actual complex quotient. -/
theorem sphere_inversePairs_eq_normalized {g : ℂ → ℂ} (m : ℕ)
    (s : ℂ) {p : ℂ} (hp : p ≠ (m : ℂ)) :
    InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
      s (p : OnePoint ℂ) =
    InversePairs (normalizedLogDerivative m g) (reflection (normalizedLogDerivative m g)) s p := by
  ext zw
  rw [reflection_normalizedLogDerivative]
  constructor
  · intro h
    exact ⟨h.1, ((sphereLogDerivative_eq_coe m g zw.1 p).mp h.2.1).2,
      ((sphereLogDerivative_eq_coe m (reflection g) zw.2 p).mp h.2.2).2⟩
  · intro h
    have hz : g zw.1 ≠ 0 := by
      intro hz
      exact hp (by simpa [normalizedLogDerivative, weightedLogDerivative, hz] using h.2.1.symm)
    have hw : reflection g zw.2 ≠ 0 := by
      intro hw
      exact hp (by simpa [normalizedLogDerivative, weightedLogDerivative, hw] using h.2.2.symm)
    exact ⟨h.1, (sphereLogDerivative_eq_coe m g zw.1 p).mpr ⟨hz, h.2.1⟩,
      (sphereLogDerivative_eq_coe m (reflection g) zw.2 p).mpr ⟨hw, h.2.2⟩⟩

/-- Empty regular high-count locus gives the actual bound at each regular
finite target. The existence of a countable exceptional set of nonregular
targets is supplied separately by `FiniteExceptionalSet.lean`. -/
theorem normalized_inversePairs_bound_at_regular_target
    {g : ℂ → ℂ} (hg : Entire g) (hg0 : g 0 ≠ 0) (m L : ℕ)
    (hempty : RegularLogDerivativeHighCount m g L = ∅)
    {s p : ℂ} (hs : s ≠ 0) (hp : p ≠ (m : ℂ))
    (hregular : IsSingleValueGraph m g (s, p)) :
    (InversePairs (normalizedLogDerivative m g) (reflection (normalizedLogDerivative m g)) s p).Finite ∧
      (InversePairs (normalizedLogDerivative m g) (reflection (normalizedLogDerivative m g)) s p).ncard ≤ L := by
  rw [← sphere_inversePairs_eq_normalized m s hp]
  have hp' : (p : OnePoint ℂ) ≠ ((m : ℂ) : OnePoint ℂ) :=
    fun h => hp (OnePoint.coe_injective h)
  have hfinite := sphereLogDerivative_finite_inverse_pairs hg hg0 m hs hp'
  refine ⟨hfinite, ?_⟩
  by_contra hbound
  have hhigh : (s, (p : OnePoint ℂ)) ∈ RegularLogDerivativeHighCount m g L :=
    ⟨⟨hs, hp', hfinite, lt_of_not_ge hbound⟩, p, rfl, hregular⟩
  simp [hempty] at hhigh

end MaximumModulus
