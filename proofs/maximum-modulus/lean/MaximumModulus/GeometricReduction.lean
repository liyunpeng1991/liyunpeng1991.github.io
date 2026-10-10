module

public import MaximumModulus.MaximumEnvelope
public import MaximumModulus.LogDerivative

@[expose] public section

open Set

noncomputable section

namespace MaximumModulus

/-- The geometric fiber-bound contract for actual inverse pairs. The theorem
below uses it as an explicit input; `AllRadii.lean` supplies the proved instance. -/
def PositiveProductFiberBound (q : ℂ → ℂ) (m B : ℕ) : Prop :=
  ∃ S : Set ℝ, S.Countable ∧ ∀ r : ℝ, 0 < r → r ∉ S → ∀ p : ℝ, (m : ℝ) < p →
    (InversePairs q (reflection q) ((r : ℂ) ^ 2) (p : ℂ)).Finite ∧
    (InversePairs q (reflection q) ((r : ℂ) ^ 2) (p : ℂ)).ncard ≤ B

theorem norm_factor_on_circle {f g : ℂ → ℂ} {m : ℕ}
    (hfactor : ∀ z, f z = z ^ m * g z) {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) :
    ‖f z‖ = r ^ m * ‖g z‖ := by
  simp [hfactor z, hz]

/-- Removing the zero at the origin does not change positive-circle maxima. -/
theorem maxPoints_eq_of_factor {f g : ℂ → ℂ} {m : ℕ}
    (hfactor : ∀ z, f z = z ^ m * g z) {r : ℝ} (hr : 0 < r) :
    MaxPoints f r = MaxPoints g r := by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    intro w hw
    have h := hz.2 w hw
    rw [norm_factor_on_circle hfactor hw, norm_factor_on_circle hfactor hz.1] at h
    exact (mul_le_mul_iff_right₀ (pow_pos hr m)).mp h
  · intro hz
    refine ⟨hz.1, ?_⟩
    intro w hw
    rw [norm_factor_on_circle hfactor hw, norm_factor_on_circle hfactor hz.1]
    exact mul_le_mul_of_nonneg_left (hz.2 w hw) (pow_nonneg hr.le m)

theorem factor_nonconstant {f g : ℂ → ℂ} {m : ℕ} (hg0 : g 0 ≠ 0)
    (hnm : ¬IsMonomial f) (hfactor : ∀ z, f z = z ^ m * g z) :
    ¬∃ c : ℂ, ∀ z, g z = c := by
  rintro ⟨c, hc⟩
  apply hnm
  refine ⟨c, m, ?_, ?_⟩
  · simpa [hc 0] using hg0
  · intro z
    rw [hfactor z, hc z]
    ring

/-- This reduction contains all maximum-envelope and radius-selection bridges.
Only the explicitly named geometric fiber estimate is assumed. -/
theorem cofinalBound_of_positiveProductFiberBound {f g : ℂ → ℂ} {m B : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z, f z = z ^ m * g z)
    (hgeom : PositiveProductFiberBound (normalizedLogDerivative m g) m B) :
    CofinalBound f B := by
  obtain ⟨S, hS, hbound⟩ := hgeom
  have hnc := factor_nonconstant hg0 hnm hfactor
  have hgne : g ≠ 0 := by
    intro hzero
    exact hg0 (by simp [hzero])
  intro R hR
  obtain ⟨r, hr, hrS, hdr, hdpos⟩ :=
    exists_positive_envelope_derivative_off_countable hg hnc hR
      (by linarith : R < R + 1) hS
  have hrpos : 0 < r := hR.trans hr.1
  let p : ℝ := (m : ℝ) + r * deriv (squaredMaximum g) r / (2 * squaredMaximum g r)
  have hmaxeq := maxPoints_eq_of_factor hfactor hrpos
  obtain ⟨z₀, hz₀⟩ := maxPoints_nonempty hg.continuous hrpos.le
  have hGpos : 0 < squaredMaximum g r := by
    rw [squaredMaximum_eq_of_maxPoint hg.continuous hz₀, Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr (value_ne_zero_of_maxPoint hg hgne hrpos hz₀)) 2
  have hmp : (m : ℝ) < p := by
    dsimp [p]
    exact lt_add_of_pos_right _ (div_pos (mul_pos hrpos hdpos) (mul_pos (by norm_num) hGpos))
  have hvalue : ∀ z ∈ MaxPoints f r, normalizedLogDerivative m g z = (p : ℂ) := by
    intro z hz
    have hzg : z ∈ MaxPoints g r := by simpa [hmaxeq] using hz
    have hq := logarithmic_derivative_eq_of_maxPoint hg hrpos hdr.hasDerivAt hzg
      (value_ne_zero_of_maxPoint hg hgne hrpos hzg)
    simpa [normalizedLogDerivative, weightedLogDerivative, p] using
      congrArg (fun q : ℂ => (m : ℂ) + q) hq
  obtain ⟨hfinite, hcard⟩ := hbound r hrpos hrS p hmp
  obtain ⟨hmaxfinite, hmaxcard⟩ := maxPoints_finite_ncard_le_inversePairs f
    (normalizedLogDerivative m g) r p hvalue hfinite
  exact ⟨r, hr.1, hmaxfinite, hmaxcard.trans hcard⟩

end MaximumModulus
