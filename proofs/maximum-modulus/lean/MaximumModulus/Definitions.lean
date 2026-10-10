module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Tendsto

@[expose] public section

/-!
Definitions for the original all-radii problem.

The maximum set uses actual function values. Every cardinality bound in
`GoodRadius` includes a separate finiteness assertion: `Set.ncard` is zero
on infinite sets.
-/

namespace MaximumModulus

def Entire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (m : ℕ), c ≠ 0 ∧ ∀ z, f z = c * z ^ m

def MaxPoints (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}

def GoodRadius (f : ℂ → ℂ) (B : ℕ) (r : ℝ) : Prop :=
  (MaxPoints f r).Finite ∧ (MaxPoints f r).ncard ≤ B

def CofinalBound (f : ℂ → ℂ) (B : ℕ) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧ GoodRadius f B r

/-- The requested theorem statement. Defining it does not prove it. -/
def AllRadiiStatement : Prop :=
  ∀ f : ℂ → ℂ, Entire f → f ≠ 0 → ¬IsMonomial f →
    ∃ B : ℕ, CofinalBound f B

/-- Counting formulation after finiteness has been established. -/
def CountTendsToInfinity (f : ℂ → ℂ) : Prop :=
  Filter.Tendsto (fun r : ℝ => (MaxPoints f r).ncard)
    Filter.atTop Filter.atTop

/-- A growth formulation that treats an infinite maximum set as infinite. -/
def MaximaGrowOnAllRadii (f : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ R : ℝ, 0 < R ∧
    ∀ r : ℝ, R < r → ¬(MaxPoints f r).Finite ∨ N < (MaxPoints f r).ncard

end MaximumModulus
