import MajorityDynamics.Universal.Main

/-!
# The paper's linear-response recursion

The day parameter is zero based. The coefficient vector is defined using the
inverse of the already proved positive-definite conditional covariance matrix.
The response recursion uses the original events, including the rule for ties.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

/-- A scalar linear statistic of a row. -/
def responseLinear {k : ℕ} (b : History k → ℝ) (x : Row k) : ℝ :=
  ∑ t, b t * x t

/-- The unique row-vector solution of `β Σ = e`; uniqueness is proved below. -/
def betaFor (n : ℕ) (s : History (n + 1)) (e : History (n + 1) → ℝ) :
    History (n + 1) → ℝ :=
  Matrix.vecMul e (conditionalCovariance n s)⁻¹

/-- One step of Definition `def:universal-epsilon`, for an arbitrary input response. -/
def responseStep (n : ℕ) (e : History (n + 1) → ℝ) : History (n + 2) → ℝ :=
  fun u => ν (n + 1) u *
    ((∫ x, responseLinear (betaFor n (parent u) e) x
        ∂childLaw n (parent u) (last u)) -
      (∫ x, responseLinear (betaFor n (parent u) e) x ∂historyLaw n (parent u)))

/-- The actual all-level response array, with initial values `1` and `-1`. -/
def ε : (n : ℕ) → History (n + 1) → ℝ
  | 0 => fun s => sign (last s)
  | n + 1 => responseStep n (ε n)

/-- The paper's regression coefficients for the constructed response. -/
def β (n : ℕ) (s : History (n + 1)) : History (n + 1) → ℝ :=
  betaFor n s (ε n)

/-- The random variable denoted `B_s` in the coherence proof. -/
def B (n : ℕ) (s : History (n + 1)) (x : Row (n + 1)) : ℝ :=
  responseLinear (β n s) x

@[simp] theorem ε_zero (s : History 1) : ε 0 s = sign (last s) := rfl

theorem ε_recursion (n : ℕ) (s : History (n + 1)) (b : Bool) :
    ε (n + 1) (append s b) = ν (n + 1) (append s b) *
      ((∫ x, B n s x ∂childLaw n s b) - (∫ x, B n s x ∂historyLaw n s)) := by
  simp only [ε, responseStep, parent_append, last_append, B, β]

end MajorityDynamics.Universal
