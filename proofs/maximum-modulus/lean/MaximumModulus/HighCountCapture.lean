module

public import MaximumModulus.SphereSmallFibers
public import MaximumModulus.FiberCapture

@[expose] public section

open Set Filter Metric
open scoped Topology ComplexConjugate OnePoint

noncomputable section

namespace MaximumModulus

/-- Actual spherical targets with finite fibers exceeding a specified bound. -/
def LogDerivativeHighCount (m : ℕ) (g : ℂ → ℂ) (L : ℕ) : Set (ℂ × OnePoint ℂ) :=
  {y | y.1 ≠ 0 ∧ y.2 ≠ ((m : ℂ) : OnePoint ℂ) ∧
    (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) y.1 y.2).Finite ∧
    L < (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) y.1 y.2).ncard}

/-- A high-count target retains at least one inverse pair outside both small
coordinate disks. The pair is bounded above when its product is bounded. -/
theorem high_count_has_bounded_survivor {β : Type*} (A B : ℂ → β)
    {ε S : ℝ} (hε : 0 < ε) {s : ℂ} {p : β} (hS : ‖s‖ ≤ S) {L : ℕ}
    (hsmall : (SmallInversePairs A B ε s p).Finite ∧
      (SmallInversePairs A B ε s p).ncard ≤ L)
    (hlarge : L < (InversePairs A B s p).ncard) :
    ∃ zw ∈ InversePairs A B s p,
      ε ≤ ‖zw.1‖ ∧ ε ≤ ‖zw.2‖ ∧ ‖zw.1‖ ≤ S / ε ∧ ‖zw.2‖ ≤ S / ε := by
  have hnot : ¬InversePairs A B s p ⊆ SmallInversePairs A B ε s p := by
    intro hsub
    exact (not_le_of_gt hlarge) ((Set.ncard_le_ncard hsub hsmall.1).trans hsmall.2)
  obtain ⟨zw, hzw, hnotSmall⟩ := Set.not_subset.mp hnot
  have hz : ε ≤ ‖zw.1‖ := le_of_not_gt (fun hz => hnotSmall ⟨hzw, Or.inl hz⟩)
  have hw : ε ≤ ‖zw.2‖ := le_of_not_gt (fun hw => hnotSmall ⟨hzw, Or.inr hw⟩)
  have hprod : ‖zw.1‖ * ‖zw.2‖ ≤ S := by rw [← norm_mul, hzw.1]; exact hS
  refine ⟨zw, hzw, hz, hw, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans hprod
  · exact (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans (by simpa [mul_comm] using hprod)

/-- A closed coordinate annulus used for the surviving pairs. -/
def CoordinateAnnulus (ε T : ℝ) : Set ℂ := {z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ T}

theorem isCompact_coordinateAnnulus (ε T : ℝ) : IsCompact (CoordinateAnnulus ε T) := by
  have heq : CoordinateAnnulus ε T = closedBall (0 : ℂ) T ∩ {z : ℂ | ε ≤ ‖z‖} := by
    ext z
    simp [CoordinateAnnulus, and_comm]
  rw [heq]
  exact (isCompact_closedBall 0 T).inter_right (isClosed_le continuous_const continuous_norm)

/-- The actual high-count set has a uniformly bounded surviving inverse pair. -/
theorem logDerivative_high_count_has_bounded_survivor {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (S : ℝ) (y : ℂ × OnePoint ℂ),
      y ∈ LogDerivativeHighCount m g
        (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) →
      ‖y.1‖ ≤ S →
      ∃ zw ∈ InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) y.1 y.2,
        zw.1 ∈ CoordinateAnnulus ε (S / ε) ∧ zw.2 ∈ CoordinateAnnulus ε (S / ε) := by
  obtain ⟨ε, hε, hsmall⟩ := sphereLogDerivative_small_inverse_pairs hg hg0 hnm hfactor
  refine ⟨ε, hε, ?_⟩
  intro S y hy hS
  obtain ⟨zw, hzw, hz, hw, hzu, hwu⟩ := high_count_has_bounded_survivor
    (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) hε hS
    (hsmall y.1 y.2 hy.1) hy.2.2.2
  exact ⟨zw, hzw, ⟨hz, hzu⟩, ⟨hw, hwu⟩⟩

/-- All bounded inverse pairs over values sufficiently close to the omitted
value are captured by any open neighborhoods of the actual central roots. -/
theorem sphereLogDerivative_annulus_root_capture {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (m : ℕ) (ε T : ℝ)
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : {z : ℂ | z ∈ CoordinateAnnulus ε T ∧
      sphereLogDerivative m g z = ((m : ℂ) : OnePoint ℂ)} ⊆ U)
    (hBV : {z : ℂ | z ∈ CoordinateAnnulus ε T ∧
      sphereLogDerivative m (reflection g) z = ((m : ℂ) : OnePoint ℂ)} ⊆ V) :
    ∃ W : Set (OnePoint ℂ), IsOpen W ∧ ((m : ℂ) : OnePoint ℂ) ∈ W ∧
      ∀ (p : OnePoint ℂ) (zw : ℂ × ℂ), p ∈ W →
        zw.1 ∈ CoordinateAnnulus ε T → zw.2 ∈ CoordinateAnnulus ε T →
        sphereLogDerivative m g zw.1 = p → sphereLogDerivative m (reflection g) zw.2 = p →
        zw.1 ∈ U ∧ zw.2 ∈ V := by
  let F : ℂ × ℂ → OnePoint ℂ × OnePoint ℂ :=
    fun zw => (sphereLogDerivative m g zw.1, sphereLogDerivative m (reflection g) zw.2)
  have hF : Continuous F := (continuous_sphereLogDerivative hg hg0 m |>.comp continuous_fst).prodMk
    (continuous_sphereLogDerivative (entire_reflection hg) (by simpa [reflection] using hg0) m |>.comp continuous_snd)
  obtain ⟨N, hN, hcN, hcapture⟩ := compact_fiber_capture
    ((isCompact_coordinateAnnulus ε T).prod (isCompact_coordinateAnnulus ε T))
    hF.continuousOn (hU.prod hV)
    (y := (((m : ℂ) : OnePoint ℂ), ((m : ℂ) : OnePoint ℂ))) (by
      intro zw hzw heq
      exact ⟨hAU ⟨hzw.1, congrArg Prod.fst heq⟩,
        hBV ⟨hzw.2, congrArg Prod.snd heq⟩⟩)
  refine ⟨(fun p : OnePoint ℂ => (p, p)) ⁻¹' N,
    hN.preimage (continuous_id.prodMk continuous_id), hcN, ?_⟩
  intro p zw hp hz hw hA hB
  apply hcapture zw ⟨hz, hw⟩
  simpa [F, hA, hB] using hp

/-- The actual high-count locus near the omitted value is contained in products
of any open neighborhoods of the finitely many bounded central roots. No
regularity, generic-degree, or continuation hypothesis is used in this input. -/
theorem logDerivative_high_count_omitted_value_capture {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (S : ℝ) (U V : Set ℂ), IsOpen U → IsOpen V →
      ({z : ℂ | z ∈ CoordinateAnnulus ε (S / ε) ∧
        sphereLogDerivative m g z = ((m : ℂ) : OnePoint ℂ)} ⊆ U) →
      ({z : ℂ | z ∈ CoordinateAnnulus ε (S / ε) ∧
        sphereLogDerivative m (reflection g) z = ((m : ℂ) : OnePoint ℂ)} ⊆ V) →
      ∃ W : Set (OnePoint ℂ), IsOpen W ∧ ((m : ℂ) : OnePoint ℂ) ∈ W ∧
        ∀ y ∈ LogDerivativeHighCount m g
          (2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0),
          ‖y.1‖ ≤ S → y.2 ∈ W →
          ∃ zw ∈ InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) y.1 y.2,
            zw.1 ∈ U ∧ zw.2 ∈ V := by
  obtain ⟨ε, hε, hsurvive⟩ := logDerivative_high_count_has_bounded_survivor hg hg0 hnm hfactor
  refine ⟨ε, hε, ?_⟩
  intro S U V hU hV hAU hBV
  obtain ⟨W, hW, hcW, hcapture⟩ :=
    sphereLogDerivative_annulus_root_capture hg hg0 m ε (S / ε) hU hV hAU hBV
  refine ⟨W, hW, hcW, ?_⟩
  intro y hy hS hpW
  obtain ⟨zw, hzw, hz, hw⟩ := hsurvive S y hy hS
  exact ⟨zw, hzw, hcapture y.2 zw hpW hz hw hzw.2.1 hzw.2.2⟩

/-- Both lists of bounded central roots needed by the omitted-value capture
are finite, from the actual spherical logarithmic derivative. -/
theorem finite_omitted_roots_in_coordinate_annulus {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) (ε T : ℝ) :
    {z : ℂ | z ∈ CoordinateAnnulus ε T ∧
      sphereLogDerivative m g z = ((m : ℂ) : OnePoint ℂ)}.Finite ∧
    {z : ℂ | z ∈ CoordinateAnnulus ε T ∧
      sphereLogDerivative m (reflection g) z = ((m : ℂ) : OnePoint ℂ)}.Finite := by
  exact ⟨finite_sphereLogDerivative_omitted_roots_in_compact hg hg0 hnm hfactor
    (isCompact_coordinateAnnulus ε T),
    finite_reflected_sphereLogDerivative_omitted_roots_in_compact hg hg0 hnm hfactor
      (isCompact_coordinateAnnulus ε T)⟩

end MaximumModulus
