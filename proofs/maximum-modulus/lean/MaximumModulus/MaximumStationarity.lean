module

public import MaximumModulus.Basic
public import MaximumModulus.MaximaToFibers
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

open Set Filter
open scoped Topology ComplexConjugate

noncomputable section

namespace MaximumModulus

/-- The derivative of the squared modulus along an actual real parameter. -/
theorem hasDerivAt_normSq {g : ℝ → ℂ} {g' : ℂ} {x : ℝ}
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => Complex.normSq (g t))
      (2 * (conj (g x) * g').re) x := by
  have hre : HasDerivAt (fun t => (g t).re) g'.re x := by
    convert! Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hg using 1
  have him : HasDerivAt (fun t => (g t).im) g'.im x := by
    convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hg using 1
  convert! (hre.mul hre).add (him.mul him) using 1
  simp [Complex.mul_re]
  ring

/-- Rotating a circle maximum has zero first variation. -/
theorem angular_stationarity {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hz : z ∈ MaxPoints f r) :
    (conj (f z) * (z * deriv f z)).im = 0 := by
  let γ : ℂ → ℂ := fun t => z * Complex.exp (t * Complex.I)
  have hγ : HasDerivAt γ (z * Complex.I) 0 := by
    convert! ((Complex.hasDerivAt_exp (0 * Complex.I)).comp 0
      ((hasDerivAt_id (0 : ℂ)).mul_const Complex.I)).const_mul z using 1
    simp
  have hd : HasDerivAt (fun t : ℝ => f (γ t))
      (deriv f z * (z * Complex.I)) 0 := by
    have hf0 : HasDerivAt f (deriv f z) (γ 0) := by
      simpa [γ] using! hf.hasDerivAt
    have h := hf0.comp (0 : ℂ) hγ
    simpa [γ] using! h.comp_ofReal
  have hmax : IsLocalMax (fun t : ℝ => Complex.normSq (f (γ t))) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hnorm : ‖γ (t : ℂ)‖ = r := by
      simp [γ, Complex.norm_exp_ofReal_mul_I, hz.1]
    have hle := hz.2 (γ t) hnorm
    simpa [γ, Complex.normSq_eq_norm_sq] using
      pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hzero := hmax.hasDerivAt_eq_zero (hasDerivAt_normSq hd)
  simp [γ, Complex.mul_re, Complex.mul_im] at hzero ⊢
  nlinarith

/-- Thus the actual logarithmic derivative is real at every maximum point. -/
theorem logarithmic_derivative_im_eq_zero {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hz : z ∈ MaxPoints f r) :
    (z * deriv f z / f z).im = 0 := by
  have h := angular_stationarity hf hz
  rw [Complex.div_im]
  simp [Complex.mul_im] at h
  simp [Complex.mul_re, Complex.mul_im]
  rw [← sub_div]
  rw [show (z.re * (deriv f z).im + z.im * (deriv f z).re) * (f z).re -
      (z.re * (deriv f z).re - z.im * (deriv f z).im) * (f z).im = 0 by
        nlinarith [h]]
  simp

/-- The squared maximum uses the actual values on the circle. -/
def squaredMaximum (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => Complex.normSq (f z)) '' Metric.sphere (0 : ℂ) r)

theorem normSq_le_squaredMaximum {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) :
    Complex.normSq (f z) ≤ squaredMaximum f r := by
  have hcompact := (isCompact_sphere (0 : ℂ) r).image
    (Complex.continuous_normSq.comp hf)
  exact le_csSup hcompact.bddAbove
    ⟨z, by simpa [mem_sphere_iff_norm] using hz, rfl⟩

theorem squaredMaximum_eq_of_maxPoint {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} {z : ℂ} (hz : z ∈ MaxPoints f r) :
    squaredMaximum f r = Complex.normSq (f z) := by
  apply le_antisymm
  · refine csSup_le ⟨_, ⟨z, ?_, rfl⟩⟩ ?_
    · simpa [mem_sphere_iff_norm] using hz.1
    · rintro _ ⟨w, hw, rfl⟩
      have h := hz.2 w (by simpa [mem_sphere_iff_norm] using hw)
      simpa [Complex.normSq_eq_norm_sq] using pow_le_pow_left₀ (norm_nonneg _) h 2
  · exact normSq_le_squaredMaximum hf hz.1

/-- A maximum value of a nonzero entire function on a positive circle is nonzero. -/
theorem value_ne_zero_of_maxPoint {f : ℂ → ℂ} (hf : Entire f) (hne : f ≠ 0)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ MaxPoints f r) : f z ≠ 0 := by
  intro hfz
  have hboundary : EqOn f (fun _ => 0) (frontier (Metric.ball (0 : ℂ) r)) := by
    intro w hw
    have hwn : ‖w‖ = r := by
      simpa [mem_sphere_iff_norm] using Metric.frontier_ball_subset_sphere hw
    have hle := hz.2 w hwn
    simpa [hfz] using hle
  have hball := Complex.eqOn_of_eqOn_frontier Metric.isBounded_ball
    hf.diffContOnCl (differentiable_const (0 : ℂ)).diffContOnCl hboundary
  have hevent : f =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) hball
  exact hne ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    analyticOnNhd_const hevent)

/-- The radial first variation at a circle maximum agrees with the derivative
of the actual squared maximum, whenever that derivative exists. -/
theorem radial_stationarity {f : ℂ → ℂ} (hf : Entire f) {r d : ℝ} (hr : 0 < r)
    (hD : HasDerivAt (squaredMaximum f) d r) {z : ℂ} (hz : z ∈ MaxPoints f r) :
    d = 2 * (conj (f z) * (z * deriv f z)).re / r := by
  let γ : ℂ → ℂ := fun t => t / (r : ℂ) * z
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hγ : HasDerivAt γ (z / (r : ℂ)) (r : ℂ) := by
    convert! ((hasDerivAt_id (r : ℂ)).div_const (r : ℂ)).mul_const z using 1
    simp [div_eq_mul_inv, mul_comm]
  have hf0 : HasDerivAt f (deriv f z) (γ r) := by
    simpa [γ, hr0] using! (hf z).hasDerivAt
  have hd : HasDerivAt (fun t : ℝ => f (γ t))
      (deriv f z * (z / (r : ℂ))) r := by
    exact (hf0.comp (r : ℂ) hγ).comp_ofReal
  have hmin : IsLocalMin
      (fun t : ℝ => squaredMaximum f t - Complex.normSq (f (γ t))) r := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    have hnorm : ‖γ (t : ℂ)‖ = t := by
      simp [γ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, abs_of_pos hr, hz.1, hr.ne']
    have hle := normSq_le_squaredMaximum hf.continuous hnorm
    simpa [γ, hr0, squaredMaximum_eq_of_maxPoint hf.continuous hz] using
      sub_nonneg.mpr hle
  have hzero := hmin.hasDerivAt_eq_zero (hD.sub (hasDerivAt_normSq hd))
  simp only [γ, div_self hr0, one_mul] at hzero
  have hre : (conj (f z) * (deriv f z * (z / (r : ℂ)))).re =
      (conj (f z) * (z * deriv f z)).re / r := by
    rw [show conj (f z) * (deriv f z * (z / (r : ℂ))) =
        (conj (f z) * (z * deriv f z)) / (r : ℂ) by ring]
    simp [Complex.div_re]
    field_simp
  rw [hre] at hzero
  rw [← mul_div_assoc] at hzero
  exact sub_eq_zero.mp hzero

/-- At a differentiability radius all actual maximum points have the same real
weighted logarithmic derivative. The denominator hypothesis is explicit. -/
theorem logarithmic_derivative_eq_of_maxPoint {f : ℂ → ℂ} (hf : Entire f)
    {r d : ℝ} (hr : 0 < r) (hD : HasDerivAt (squaredMaximum f) d r)
    {z : ℂ} (hz : z ∈ MaxPoints f r) (hfz : f z ≠ 0) :
    z * deriv f z / f z = (r * d / (2 * squaredMaximum f r) : ℝ) := by
  have hrad := radial_stationarity hf hr hD hz
  have hns : Complex.normSq (f z) ≠ 0 := by
    simpa using hfz
  rw [squaredMaximum_eq_of_maxPoint hf.continuous hz]
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.div_re]
    rw [← add_div]
    have hprod : (z * deriv f z).re * (f z).re +
        (z * deriv f z).im * (f z).im = (conj (f z) * (z * deriv f z)).re := by
      simp [Complex.mul_re]
      ring
    rw [hprod, hrad]
    field_simp
  · simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
      ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_im] using
      logarithmic_derivative_im_eq_zero (hf z) hz

/-- The common-value assertion needed by the actual maximum-point/fiber map. -/
theorem common_logarithmic_derivative_at_maxPoints {f : ℂ → ℂ}
    (hf : Entire f) (hne : f ≠ 0) {r d : ℝ} (hr : 0 < r)
    (hD : HasDerivAt (squaredMaximum f) d r) :
    ∀ z ∈ MaxPoints f r,
      z * deriv f z / f z = (r * d / (2 * squaredMaximum f r) : ℝ) := by
  intro z hz
  exact logarithmic_derivative_eq_of_maxPoint hf hr hD hz
    (value_ne_zero_of_maxPoint hf hne hr hz)

/-- The fiber correspondence now follows from the actual derivatives and maxima;
the only extra radius condition is differentiability of the actual envelope. -/
theorem actual_maxPoints_mapsTo_inversePairs {f : ℂ → ℂ}
    (hf : Entire f) (hne : f ≠ 0) {r d : ℝ} (hr : 0 < r)
    (hD : HasDerivAt (squaredMaximum f) d r) :
    MapsTo conjugatePair (MaxPoints f r)
      (InversePairs (fun z => z * deriv f z / f z)
        (reflection (fun z => z * deriv f z / f z)) ((r : ℂ) ^ 2)
        (r * d / (2 * squaredMaximum f r) : ℝ)) := by
  exact maxPoints_mapsTo_inversePairs f (fun z => z * deriv f z / f z) r
    (r * d / (2 * squaredMaximum f r))
    (common_logarithmic_derivative_at_maxPoints hf hne hr hD)

end MaximumModulus
