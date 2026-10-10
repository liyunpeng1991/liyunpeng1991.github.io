module

public import MaximumModulus.Finiteness
public import MaximumModulus.LocalValence
public import MaximumModulus.SmallFibers
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Tactic.LinearCombination

@[expose] public section

open Set Filter
open scoped Topology ComplexConjugate

noncomputable section

namespace MaximumModulus

/-- The logarithmic derivative multiplied by the argument, using actual derivatives and values. -/
def weightedLogDerivative (g : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv g z / g z

/-- The removable extension of `z f'/f` obtained from `f = z^m g`. -/
def normalizedLogDerivative (m : ℕ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (m : ℂ) + weightedLogDerivative g z

@[simp] theorem weightedLogDerivative_zero (g : ℂ → ℂ) :
    weightedLogDerivative g 0 = 0 := by simp [weightedLogDerivative]

@[simp] theorem normalizedLogDerivative_zero (m : ℕ) (g : ℂ → ℂ) :
    normalizedLogDerivative m g 0 = (m : ℂ) := by simp [normalizedLogDerivative]

theorem analyticAt_weightedLogDerivative {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) : AnalyticAt ℂ (weightedLogDerivative g) 0 := by
  exact (analyticAt_id.mul (hg.analyticAt 0).deriv).div (hg.analyticAt 0) hg0

theorem analyticAt_normalizedLogDerivative {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) : AnalyticAt ℂ (normalizedLogDerivative m g) 0 := by
  exact analyticAt_const.add (analyticAt_weightedLogDerivative hg hg0)

/-- A constant germ of the normalized logarithmic derivative forces the entire factor
itself to be constant. -/
theorem eq_zero_value_of_weightedLogDerivative_germ_zero {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0)
    (hq : ∀ᶠ z in 𝓝 (0 : ℂ), weightedLogDerivative g z = 0) :
    ∀ z : ℂ, g z = g 0 := by
  have hgn : ∀ᶠ z in 𝓝 (0 : ℂ), g z ≠ 0 :=
    (hg 0).continuousAt.eventually (isOpen_ne.mem_nhds hg0)
  have hd0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv g z = 0 := by
    filter_upwards [hq.filter_mono nhdsWithin_le_nhds,
      hgn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hgz hzn
    have hz0 : z ≠ 0 := by simpa using hzn
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hgz)).resolve_left hz0
  have hda : AnalyticOnNhd ℂ (deriv g) univ := by
    intro z hz
    exact (hg.analyticAt z).deriv
  have hdeq : deriv g = fun _ => (0 : ℂ) :=
    hda.eq_of_frequently_eq analyticOnNhd_const hd0.frequently
  intro z
  exact is_const_of_deriv_eq_zero hg (fun w => congrFun hdeq w) z 0

/-- Non-monomiality gives the finite-order hypothesis required by local valence. -/
theorem normalizedLogDerivative_finite_order {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    analyticOrderAt (fun z => normalizedLogDerivative m g z -
      normalizedLogDerivative m g 0) 0 ≠ ⊤ := by
  intro htop
  have hq : ∀ᶠ z in 𝓝 (0 : ℂ), weightedLogDerivative g z = 0 := by
    simpa [normalizedLogDerivative] using analyticOrderAt_eq_top.mp htop
  have hgconst := eq_zero_value_of_weightedLogDerivative_germ_zero hg hg0 hq
  apply hnm
  refine ⟨g 0, m, hg0, ?_⟩
  intro z
  rw [hfactor z, hgconst z]
  ring

/-- The actual logarithmic derivative has a bounded finite local valence after
removing the zero at the origin. -/
theorem normalizedLogDerivative_local_valence {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    0 < analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : ℂ,
      {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ normalizedLogDerivative m g z = p}.ncard ≤
        analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 := by
  simpa using analytic_local_valence (analyticAt_normalizedLogDerivative hg hg0 m)
    (normalizedLogDerivative_finite_order hg hg0 hnm hfactor)

/-- Away from zero and the zeros of the factor, the removable extension equals
`z f'(z) / f(z)` for the actual original function. -/
theorem weightedLogDerivative_factor {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hfactor : ∀ z : ℂ, f z = z ^ m * g z)
    {z : ℂ} (hz : z ≠ 0) (hgz : g z ≠ 0) :
    weightedLogDerivative f z = normalizedLogDerivative m g z := by
  have heq : f = fun z => z ^ m * g z := funext hfactor
  have hlog : logDeriv f z = (m : ℂ) / z + logDeriv g z := by
    rw [heq]
    convert! logDeriv_fun_mul z (pow_ne_zero m hz) hgz
      (differentiableAt_id.pow m) (hg z) using 1
    congr 1
    convert! (logDeriv_pow z m).symm using 1
  have hmul := congrArg (fun a : ℂ => z * a) hlog
  simpa [logDeriv_apply, mul_add, ← mul_div_assoc, hz,
    weightedLogDerivative, normalizedLogDerivative] using hmul

theorem deriv_reflection (g : ℂ → ℂ) :
    deriv (reflection g) = reflection (deriv g) := by
  exact deriv_conj_conj

theorem reflection_weightedLogDerivative (g : ℂ → ℂ) :
    reflection (weightedLogDerivative g) = weightedLogDerivative (reflection g) := by
  ext z
  simp [reflection, weightedLogDerivative, deriv_reflection]

/-- The product coordinate can be any nonzero complex number. -/
def reciprocalProduct (g : ℂ → ℂ) (s : ℂ) (z : ℂ) : ℂ :=
  g z * reflection g (s / z)

theorem analyticOnNhd_reciprocalProduct {g : ℂ → ℂ} (hg : Entire g) (s : ℂ) :
    AnalyticOnNhd ℂ (reciprocalProduct g s) ({0}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact ((hg z).mul ((entire_reflection hg (s / z)).comp z
    ((differentiableAt_const s).div differentiableAt_id hz0))).differentiableWithinAt

/-- An entire function nonzero at the origin cannot vanish throughout the
punctured plane. -/
theorem not_eq_zero_on_punctured_plane {g : ℂ → ℂ} (hg : Entire g) (hg0 : g 0 ≠ 0) :
    ¬∀ z : ℂ, z ≠ 0 → g z = 0 := by
  intro hzero
  have hevent : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hzero z (by simpa using hz)
  have heq : g = fun _ => (0 : ℂ) :=
    (hg.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
      analyticOnNhd_const hevent.frequently
  exact hg0 (congrFun heq 0)

theorem analyticOnNhd_reciprocalReflection {g : ℂ → ℂ} (hg : Entire g) (s : ℂ) :
    AnalyticOnNhd ℂ (fun z => reflection g (s / z)) ({0}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact ((entire_reflection hg (s / z)).comp z
    ((differentiableAt_const s).div differentiableAt_id hz0)).differentiableWithinAt

theorem not_reciprocalProduct_identically_zero {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) {s : ℂ} (hs : s ≠ 0) :
    ¬∀ z : ℂ, z ≠ 0 → reciprocalProduct g s z = 0 := by
  intro hzero
  have hal : AnalyticOnNhd ℂ g ({0}ᶜ : Set ℂ) := fun z _ => hg.analyticAt z
  have har := analyticOnNhd_reciprocalReflection hg s
  rcases hal.eq_zero_or_eq_zero_of_mul_eq_zero har
    (fun z hz => hzero z (by simpa using hz)) punctured_plane_preconnected with hl | hr
  · exact not_eq_zero_on_punctured_plane hg hg0 (fun z hz => hl z (by simpa using hz))
  · apply not_eq_zero_on_punctured_plane (entire_reflection hg) (by simpa [reflection] using hg0)
    intro w hw
    have heq : s / (s / w) = w := by field_simp
    simpa only [heq] using hr (s / w) (by simpa using div_ne_zero hs hw)

/-- A constant reciprocal product forces the entire factor to be constant.
The product parameter is an arbitrary complex number, as needed for vertical components. -/
theorem eq_zero_value_of_reciprocalProduct_constant {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (s C : ℂ)
    (hprod : ∀ z : ℂ, z ≠ 0 → reciprocalProduct g s z = C) :
    ∀ z : ℂ, g z = g 0 := by
  have harg : Tendsto (fun z : ℂ => s / z) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    simpa [div_eq_mul_inv] using (tendsto_inv₀_cobounded (α := ℂ)).const_mul s
  have hden : Tendsto (fun z : ℂ => reflection g (s / z))
      (cocompact ℂ) (𝓝 (reflection g 0)) :=
    ((entire_reflection hg) 0).continuousAt.tendsto.comp harg
  have hdenzero : reflection g 0 ≠ 0 := by simpa [reflection] using hg0
  have hquot : Tendsto (fun z : ℂ => C / reflection g (s / z))
      (cocompact ℂ) (𝓝 (C / reflection g 0)) :=
    tendsto_const_nhds.div hden hdenzero
  have heq : g =ᶠ[cocompact ℂ] (fun z : ℂ => C / reflection g (s / z)) := by
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact,
      hden.eventually (isOpen_ne.mem_nhds hdenzero)] with z hz hd
    apply (eq_div_iff hd).mpr
    exact hprod z (by simpa using hz)
  have hlim : Tendsto g (cocompact ℂ) (𝓝 (C / reflection g 0)) :=
    hquot.congr' heq.symm
  intro z
  exact (hg.apply_eq_of_tendsto_cocompact z hlim).trans
    (hg.apply_eq_of_tendsto_cocompact 0 hlim).symm

theorem deriv_reciprocalProduct {g : ℂ → ℂ} (hg : Entire g) (s : ℂ)
    {z : ℂ} (hz : z ≠ 0) :
    deriv (reciprocalProduct g s) z =
      deriv g z * reflection g (s / z) +
        g z * (deriv (reflection g) (s / z) * (-s / z ^ 2)) := by
  have hdiv : HasDerivAt (fun u : ℂ => s / u) (-s / z ^ 2) z := by
    convert! (hasDerivAt_const z s).div (hasDerivAt_id z) hz using 1
    simp
  convert! ((hg z).hasDerivAt.mul
    (((entire_reflection hg (s / z)).hasDerivAt).comp z hdiv)).deriv using 1

/-- Reciprocal symmetry forces the derivative of the reciprocal product to vanish.
Zeros of either factor are included by the analytic identity theorem. -/
theorem reciprocalProduct_constant_of_weighted_symmetry {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) {s : ℂ} (hs : s ≠ 0)
    (hsym : ∀ z : ℂ, z ≠ 0 → g z ≠ 0 → reflection g (s / z) ≠ 0 →
      weightedLogDerivative g z = reflection (weightedLogDerivative g) (s / z)) :
    ∃ C : ℂ, ∀ z : ℂ, z ≠ 0 → reciprocalProduct g s z = C := by
  have hPa := analyticOnNhd_reciprocalProduct hg s
  have hmul : ∀ z ∈ ({0}ᶜ : Set ℂ),
      deriv (reciprocalProduct g s) z * reciprocalProduct g s z = 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    by_cases hPz : reciprocalProduct g s z = 0
    · simp [hPz]
    have hgz : g z ≠ 0 := (mul_ne_zero_iff.mp hPz).1
    have hrgz : reflection g (s / z) ≠ 0 := (mul_ne_zero_iff.mp hPz).2
    have hq := hsym z hz0 hgz hrgz
    rw [reflection_weightedLogDerivative] at hq
    unfold weightedLogDerivative at hq
    field_simp [hz0, hgz, hrgz] at hq
    have hd : deriv (reciprocalProduct g s) z = 0 := by
      rw [deriv_reciprocalProduct hg s hz0]
      field_simp [hz0]
      linear_combination hq
    simp [hd]
  have hder : ∀ z ∈ ({0}ᶜ : Set ℂ), deriv (reciprocalProduct g s) z = 0 := by
    rcases hPa.deriv.eq_zero_or_eq_zero_of_mul_eq_zero hPa hmul
      punctured_plane_preconnected with hd | hP
    · exact hd
    · exact False.elim (not_reciprocalProduct_identically_zero hg hg0 hs
        (fun z hz => hP z (by simpa using hz)))
  obtain ⟨C, hC⟩ := isOpen_compl_singleton.exists_is_const_of_deriv_eq_zero
    punctured_plane_preconnected hPa.differentiableOn hder
  exact ⟨C, fun z hz => hC z (by simpa using hz)⟩

/-- The normalized logarithmic derivative of a non-monomial entire function has
no reciprocal symmetry, even if equality is required only where both factors are nonzero.
This avoids residues and the meromorphic identity theorem. -/
theorem normalizedLogDerivative_no_reciprocal_symmetry {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {s : ℂ} (hs : s ≠ 0) :
    ¬∀ z : ℂ, z ≠ 0 → g z ≠ 0 → reflection g (s / z) ≠ 0 →
      normalizedLogDerivative m g z = reflection (normalizedLogDerivative m g) (s / z) := by
  intro hsym
  have hsymg : ∀ z : ℂ, z ≠ 0 → g z ≠ 0 → reflection g (s / z) ≠ 0 →
      weightedLogDerivative g z = reflection (weightedLogDerivative g) (s / z) := by
    intro z hz hgz hrgz
    simpa [reflection, normalizedLogDerivative] using hsym z hz hgz hrgz
  obtain ⟨C, hC⟩ := reciprocalProduct_constant_of_weighted_symmetry hg hg0 hs hsymg
  have hgconst := eq_zero_value_of_reciprocalProduct_constant hg hg0 s C hC
  apply hnm
  refine ⟨g 0, m, hg0, ?_⟩
  intro z
  rw [hfactor z, hgconst z]
  ring

/-- The local valence and reciprocal exclusion apply to every nonzero,
non-monomial entire function, with its factor obtained from the actual function. -/
theorem exists_normalizedLogDerivative {f : ℂ → ℂ} (hf : Entire f) (hne : f ≠ 0)
    (hnm : ¬IsMonomial f) :
    ∃ (m : ℕ) (g : ℂ → ℂ), Entire g ∧ g 0 ≠ 0 ∧
      (∀ z : ℂ, f z = z ^ m * g z) ∧
      AnalyticAt ℂ (normalizedLogDerivative m g) 0 ∧
      analyticOrderAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 ≠ ⊤ ∧
      (∀ s : ℂ, s ≠ 0 →
        ¬∀ z : ℂ, z ≠ 0 → g z ≠ 0 → reflection g (s / z) ≠ 0 →
          normalizedLogDerivative m g z = reflection (normalizedLogDerivative m g) (s / z)) := by
  obtain ⟨m, g, hg, hg0, hfactor⟩ := entire_factor_at_zero hf hne
  refine ⟨m, g, hg, hg0, hfactor, analyticAt_normalizedLogDerivative hg hg0 m, ?_, ?_⟩
  · simpa using normalizedLogDerivative_finite_order hg hg0 hnm hfactor
  · intro s hs
    exact normalizedLogDerivative_no_reciprocal_symmetry hg hg0 hnm hfactor hs

/-- Conjugation transfers finite local valence to the reflected function with the
same radius and the same cardinality bound. -/
theorem reflection_local_valence {A : ℂ → ℂ} {ε : ℝ} {k : ℕ}
    (hA : ∀ p : ℂ, {z : ℂ | ‖z‖ < ε ∧ A z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ A z = p}.ncard ≤ k) :
    ∀ p : ℂ, {z : ℂ | ‖z‖ < ε ∧ reflection A z = p}.Finite ∧
      {z : ℂ | ‖z‖ < ε ∧ reflection A z = p}.ncard ≤ k := by
  intro p
  obtain ⟨hfinite, hcard⟩ := hA (conj p)
  have hmaps : Set.MapsTo conj {z : ℂ | ‖z‖ < ε ∧ reflection A z = p}
      {z : ℂ | ‖z‖ < ε ∧ A z = conj p} := by
    intro z hz
    refine ⟨by simpa using hz.1, ?_⟩
    have heq := congrArg conj hz.2
    simpa [reflection] using heq
  have hinj : Set.InjOn conj {z : ℂ | ‖z‖ < ε ∧ reflection A z = p} :=
    fun z _ w _ hzw => by simpa using congrArg conj hzw
  exact ⟨Set.Finite.of_injOn hmaps hinj hfinite,
    (Set.ncard_le_ncard_of_injOn conj hmaps hinj hfinite).trans hcard⟩

/-- The small-coordinate escape bound for the actual normalized logarithmic
correspondence is twice its local order. Each estimated set is proved finite. -/
theorem normalizedLogDerivative_small_inverse_pairs {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s p : ℂ, s ≠ 0 →
      (SmallInversePairs (normalizedLogDerivative m g)
        (reflection (normalizedLogDerivative m g)) ε s p).Finite ∧
      (SmallInversePairs (normalizedLogDerivative m g)
        (reflection (normalizedLogDerivative m g)) ε s p).ncard ≤
        2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 := by
  obtain ⟨_, ε, hε, hA⟩ := normalizedLogDerivative_local_valence hg hg0 hnm hfactor
  have hB := reflection_local_valence hA
  refine ⟨ε, hε, ?_⟩
  intro s p hs
  simpa only [two_mul] using small_inverse_pairs_finite_ncard_le
    (normalizedLogDerivative m g) (reflection (normalizedLogDerivative m g)) ε s p hs
    (analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)
    (analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0)
    (hA p).1 (hB p).1 (hA p).2 (hB p).2

/-- For sufficiently small nonzero product coordinate, the complete actual
logarithmic correspondence fiber is finite and bounded by twice the local order. -/
theorem normalizedLogDerivative_small_product_bound {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s p : ℂ, s ≠ 0 → ‖s‖ < ε ^ 2 →
      (InversePairs (normalizedLogDerivative m g)
        (reflection (normalizedLogDerivative m g)) s p).Finite ∧
      (InversePairs (normalizedLogDerivative m g)
        (reflection (normalizedLogDerivative m g)) s p).ncard ≤
        2 * analyticOrderNatAt (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0 := by
  obtain ⟨ε, hε, hsmall⟩ := normalizedLogDerivative_small_inverse_pairs hg hg0 hnm hfactor
  refine ⟨ε, hε, ?_⟩
  intro s p hs hsp
  rw [inverse_pairs_eq_small_of_norm_lt_sq (normalizedLogDerivative m g)
    (reflection (normalizedLogDerivative m g)) ε s p hε hsp]
  exact hsmall s p hs

end MaximumModulus
