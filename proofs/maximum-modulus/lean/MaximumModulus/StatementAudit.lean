module

public import MaximumModulus.AEBridge
public import MaximumModulus.Basic

@[expose] public section

/-!
Independent spelling of the requested statement and of the proved finiteness
target. These bridges check definitions and quantifiers; they do not prove the
all-radii estimate. Its proof is supplied separately by `AllRadii.lean`.
-/

namespace MaximumModulus.StatementAudit

def OriginalMaxPoints (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}

def OriginalRequiredStatement : Prop :=
  ∀ f : ℂ → ℂ,
    Differentiable ℂ f → f ≠ 0 →
    (¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m) →
    ∃ B : ℕ, ∀ R : ℝ, 0 < R →
      ∃ r : ℝ, R < r ∧ (OriginalMaxPoints f r).Finite ∧
        (OriginalMaxPoints f r).ncard ≤ B

theorem statement_correspondence : OriginalRequiredStatement ↔ AllRadiiStatement := Iff.rfl

theorem original_finiteness {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (hnm : ¬∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z : ℂ, f z = c * z ^ m)
    {r : ℝ} (hr : 0 < r) : (OriginalMaxPoints f r).Finite :=
  finite_maxPoints hf hne hnm hr

end MaximumModulus.StatementAudit
