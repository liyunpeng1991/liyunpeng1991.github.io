module

public import MaximumModulus.MeromorphicCorrespondence

@[expose] public section

open Set Filter Metric
open scoped Topology ComplexConjugate OnePoint

noncomputable section

namespace MaximumModulus

/-- A nonzero entire function has only finitely many zeros in any compact set;
the chosen nonzero value need not be at the origin. -/
theorem finite_entire_zeros_in_compact_of_ne_zero {F : ℂ → ℂ} (hF : Entire F)
    (hne : F ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ F z = 0}.Finite := by
  by_contra hinf
  have hInf : {z : ℂ | z ∈ K ∧ F z = 0}.Infinite := hinf
  obtain ⟨a, _, hacc⟩ := hInf.exists_accPt_of_subset_isCompact hK (fun _ hz => hz.1)
  have heq : F = fun _ => (0 : ℂ) :=
    (hF.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
      analyticOnNhd_const ((accPt_iff_frequently_nhdsNE.mp hacc).mono (fun _ hz => hz.2))
  exact hne heq

/-- Non-monomiality makes the entire numerator for the omitted value nonzero. -/
theorem logDerivativeNumerator_omitted_value_ne_zero {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    logDerivativeNumerator m g (m : ℂ) ≠ 0 := by
  intro hzero
  have hq : ∀ᶠ z in 𝓝 (0 : ℂ), weightedLogDerivative g z = 0 := by
    apply Filter.Eventually.of_forall
    intro z
    have hz : z * deriv g z = 0 := by
      simpa [logDerivativeNumerator] using congrFun hzero z
    simp [weightedLogDerivative, hz]
  have hgconst := eq_zero_value_of_weightedLogDerivative_germ_zero hg hg0 hq
  apply hnm
  refine ⟨g 0, m, hg0, ?_⟩
  intro z
  rw [hfactor z, hgconst z]
  ring

/-- All roots at the omitted common value in a compact annulus are finite.
Spherical values ensure that poles are never misidentified as roots. -/
theorem finite_sphereLogDerivative_omitted_roots_in_compact {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ sphereLogDerivative m g z = ((m : ℂ) : OnePoint ℂ)}.Finite := by
  apply (finite_entire_zeros_in_compact_of_ne_zero (entire_logDerivativeNumerator hg m (m : ℂ))
    (logDerivativeNumerator_omitted_value_ne_zero hg hg0 hnm hfactor) hK).subset
  intro z hz
  refine ⟨hz.1, ?_⟩
  obtain ⟨hgz, hq⟩ := (sphereLogDerivative_eq_coe m g z (m : ℂ)).mp hz.2
  have hw : weightedLogDerivative g z = 0 := by simpa [normalizedLogDerivative] using hq
  have hnum : z * deriv g z = 0 := (div_eq_zero_iff.mp hw).resolve_right hgz
  simpa [logDerivativeNumerator] using hnum

/-- A complex-valued local valence bound transfers to the genuine spherical
representative wherever its entire denominator is nonzero. -/
theorem sphereLogDerivative_local_valence_of_nonzero {g : ℂ → ℂ} {m k : ℕ} {ε : ℝ}
    (hgn : ∀ z : ℂ, ‖z‖ < ε → g z ≠ 0)
    (hA : ∀ p : ℂ, {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.ncard ≤ k) :
    ∀ p : OnePoint ℂ, {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m g z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m g z = p}.ncard ≤ k := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    have heq : {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m g z = ∞} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hgn z hz.1 ((sphereLogDerivative_eq_infty m g z).mp hz.2)
    rw [heq]
    exact ⟨Set.finite_empty, by simp⟩
  | coe p =>
    have heq : {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m g z = (p : OnePoint ℂ)} =
        {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, (sphereLogDerivative_eq_coe m g z p).mp hz.2 |>.2⟩
      · intro hz
        exact ⟨hz.1, (sphereLogDerivative_eq_coe m g z p).mpr ⟨hgn z hz.1, hz.2⟩⟩
    rw [heq]
    exact hA p

/-- Reflection preserves every finite spherical local valence bound. -/
theorem reflected_sphereLogDerivative_local_valence {g : ℂ → ℂ} {m k : ℕ} {ε : ℝ}
    (hgn : ∀ z : ℂ, ‖z‖ < ε → g z ≠ 0)
    (hAc : ∀ p : ℂ, {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.ncard ≤ k) :
    ∀ p : OnePoint ℂ, {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m (reflection g) z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m (reflection g) z = p}.ncard ≤ k := by
  have hgn' : ∀ z : ℂ, ‖z‖ < ε → reflection g z ≠ 0 := by
    intro z hz
    simpa [reflection] using hgn (conj z) (by simpa using hz)
  have hB := reflection_local_valence hAc
  rw [reflection_normalizedLogDerivative] at hB
  exact sphereLogDerivative_local_valence_of_nonzero hgn' hB

/-- The actual spherical logarithmic derivative and its reflection have common
finite local valence bounded by the first nonconstant local order. -/
theorem sphereLogDerivative_common_local_valence {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z : ℂ, ‖z‖ < ε → g z ≠ 0) ∧
      (∀ p : OnePoint ℂ,
        {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m g z = p}.Finite ∧
        {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m g z = p}.ncard ≤
          analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) ∧
      (∀ p : OnePoint ℂ,
        {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m (reflection g) z = p}.Finite ∧
        {z : ℂ | ‖z‖ < ε ∧ sphereLogDerivative m (reflection g) z = p}.ncard ≤
          analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) := by
  obtain ⟨_, εA, hεA, hA⟩ := normalizedLogDerivative_local_valence hg hg0 hnm hfactor
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), g z ≠ 0 :=
    (hg 0).continuousAt.eventually (isOpen_ne.mem_nhds hg0)
  obtain ⟨εg, hεg, hgeps⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε := min εA εg
  have hε : 0 < ε := lt_min hεA hεg
  have hgn : ∀ z : ℂ, ‖z‖ < ε → g z ≠ 0 := by
    intro z hz
    exact hgeps (by simpa only [dist_zero_right] using hz.trans_le (min_le_right _ _))
  have hAc : ∀ p : ℂ, {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.ncard ≤
        analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 := by
    intro p
    have hsub : {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p} ⊆
        {z : ℂ | ‖z‖ < εA ∧ normalizedLogDerivative m g z = p} :=
      fun z hz => ⟨hz.1.trans_le (min_le_left _ _), hz.2⟩
    exact ⟨(hA p).1.subset hsub, (Set.ncard_le_ncard hsub (hA p).1).trans (hA p).2⟩
  have hAs := sphereLogDerivative_local_valence_of_nonzero hgn hAc
  exact ⟨ε, hε, hgn, hAs, reflected_sphereLogDerivative_local_valence hgn hAc⟩

/-- The actual spherical correspondence satisfies the `2k` escape bound at every
spherical value, including infinity and the omitted value. -/
theorem sphereLogDerivative_small_inverse_pairs {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (s : ℂ) (p : OnePoint ℂ), s ≠ 0 →
      (SmallInversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) ε s p).Finite ∧
      (SmallInversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) ε s p).ncard ≤
        2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 := by
  obtain ⟨ε, hε, _, hA, hB⟩ := sphereLogDerivative_common_local_valence hg hg0 hnm hfactor
  refine ⟨ε, hε, ?_⟩
  intro s p hs
  simpa only [two_mul] using small_inverse_pairs_finite_ncard_le
    (sphereLogDerivative m g) (sphereLogDerivative m (reflection g)) ε s p hs
    (analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)
    (analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)
    (hA p).1 (hB p).1 (hA p).2 (hB p).2

/-- Every actual spherical fiber at a sufficiently small nonzero product is finite
and has at most twice the local order many inverse pairs. -/
theorem sphereLogDerivative_small_product_bound {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (s : ℂ) (p : OnePoint ℂ), s ≠ 0 → ‖s‖ < ε ^ 2 →
      (InversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) s p).Finite ∧
      (InversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) s p).ncard ≤
        2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 := by
  obtain ⟨ε, hε, hsmall⟩ := sphereLogDerivative_small_inverse_pairs hg hg0 hnm hfactor
  refine ⟨ε, hε, ?_⟩
  intro s p hs hsp
  rw [inverse_pairs_eq_small_of_norm_lt_sq (sphereLogDerivative m g)
    (sphereLogDerivative m (reflection g)) ε s p hε hsp]
  exact hsmall s p hs

/-- Reflection cannot turn a non-monomial function into a monomial. -/
theorem isMonomial_of_reflection {f : ℂ → ℂ} (h : IsMonomial (reflection f)) :
    IsMonomial f := by
  obtain ⟨c, m, hc, hfactor⟩ := h
  refine ⟨conj c, m, by simpa using hc, ?_⟩
  intro z
  have heq := congrArg conj (hfactor (conj z))
  simpa [reflection] using heq

/-- The reflected numerator at the common omitted value is nonzero as well. -/
theorem reflected_logDerivativeNumerator_omitted_value_ne_zero {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    logDerivativeNumerator m (reflection g) (m : ℂ) ≠ 0 := by
  apply logDerivativeNumerator_omitted_value_ne_zero (entire_reflection hg)
    (by simpa [reflection] using hg0) (fun h => hnm (isMonomial_of_reflection h))
  intro z
  simp [reflection, hfactor]

/-- The reflected spherical roots at the omitted value are finite in compact sets. -/
theorem finite_reflected_sphereLogDerivative_omitted_roots_in_compact
    {f g : ℂ → ℂ} {m : ℕ} (hg : Entire g) (hg0 : g 0 ≠ 0)
    (hnm : ¬IsMonomial f) (hfactor : ∀ z : ℂ, f z = z ^ m * g z)
    {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ sphereLogDerivative m (reflection g) z = ((m : ℂ) : OnePoint ℂ)}.Finite := by
  apply finite_sphereLogDerivative_omitted_roots_in_compact (entire_reflection hg)
    (by simpa [reflection] using hg0) (fun h => hnm (isMonomial_of_reflection h)) ?_ hK
  intro z
  simp [reflection, hfactor]

end MaximumModulus
