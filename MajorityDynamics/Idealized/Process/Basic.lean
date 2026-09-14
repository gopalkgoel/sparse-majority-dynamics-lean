import MajorityDynamics.Local.Template
import MajorityDynamics.Universal.Recursion
import MajorityDynamics.Binomial.ApproximationStatements

/-!
# The exact idealized-process contract (Theorem 5.2)

The level index `n` means paper day `n + 1`. A family is stored on all natural
levels, but the theorem asserts its properties only through the requested day
`D`. Consequently its uniqueness is equality on that same finite prefix.
Sizes are natural numbers, without any constraint that they sum to `N`.
The recursion rounds the actual local template down and keeps its real edge
counts. Every mean constraint uses the actual conditioned binomial row.
-/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process

open Universal Local

structure State (n : ℕ) where
  sizes : Local.Sizes n
  edges : Local.EdgeCounts n

structure StateSymmetric {n : ℕ} (x : State n) : Prop where
  sizes : ∀ s, x.sizes (flip s) = x.sizes s
  edges : ∀ s t, x.edges (flip s) (flip t) = x.edges s t

def TiltSymmetric {n : ℕ} (q : Local.Tilt n) : Prop :=
  ∀ s t, q (flip s) (flip t) = q s t

structure LevelEstimates (N : ℕ) (p : Binomial.Probability) (ell : ℕ)
    {n : ℕ} (x : State n) : Prop where
  sizes : ∀ s, |(x.sizes s : ℝ) - (N : ℝ) * ν n s| ≤
    (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ ell
  edges : ∀ s t,
    |x.edges s t - (p : ℝ) * x.sizes s * x.sizes t *
      (1 + μ n s t / Real.sqrt ((p : ℝ) * N))| ≤
      (p : ℝ) * x.sizes s * x.sizes t * (Real.log (N : ℝ) ^ ell / ((p : ℝ) * N))

def TiltEstimates (N : ℕ) (p : Binomial.Probability) (ell : ℕ)
    {n : ℕ} (q : Local.Tilt n) : Prop :=
  ∀ s t, |(q s t : ℝ) - (logitTilt N p (γ n s t) (ν n t) : ℝ)| ≤
    Real.log (N : ℝ) ^ ell / N

structure Solvable {n : ℕ} (x : State n) (q : Local.Tilt n) : Prop where
  sizes_pos : ∀ s, 0 < x.sizes s
  edges_pos : ∀ s t, 0 < x.edges s t
  conditioning_pos : ∀ s,
    0 < Binomial.eventMass (Local.trials x.sizes s) (q s)
      (Local.historySupport x.sizes s)
  solves : Local.Solves x.sizes x.edges q
  unique : ∀ q' : Local.Tilt n, Local.Solves x.sizes x.edges q' → q' = q

def initialState (N : ℕ) (p : Binomial.Probability) : State 0 where
  sizes _ := N / 2
  edges s t := (p : ℝ) * ((N / 2 : ℕ) : ℝ) *
    (((N / 2 : ℕ) : ℝ) - if s = t then 1 else 0)

def nextState {n : ℕ} (x : State n) (q : Local.Tilt n) : State (n + 1) where
  sizes u := ⌊Local.templateSizes x.sizes q u⌋₊
  edges := Local.templateEdges x.sizes x.edges q

structure Data where
  state : ∀ n : ℕ, State n
  tilt : ∀ n : ℕ, Local.Tilt n

/-- The recursive clauses that determine the finite family. -/
structure Recursion (N : ℕ) (p : Binomial.Probability) (D : ℕ) (a : Data) : Prop where
  initial : a.state 0 = initialState N p
  solvable : ∀ n, n + 1 < D → Solvable (a.state n) (a.tilt n)
  evolution : ∀ n, n + 1 < D → a.state (n + 1) = nextState (a.state n) (a.tilt n)

structure Specification (N : ℕ) (p : Binomial.Probability) (D ell : ℕ)
    (a : Data) : Prop extends Recursion N p D a where
  symmetry : ∀ n, n < D → StateSymmetric (a.state n)
  tilt_symmetry : ∀ n, n + 1 < D → TiltSymmetric (a.tilt n)
  estimates : ∀ n, n < D → LevelEstimates N p ell (a.state n)
  tilt_estimates : ∀ n, n + 1 < D → TiltEstimates N p ell (a.tilt n)

def AgreeThrough (D : ℕ) (a b : Data) : Prop :=
  (∀ n, n < D → a.state n = b.state n) ∧
    ∀ n, n + 1 < D → a.tilt n = b.tilt n

/-- Complete Theorem 5.2, with a natural logarithmic exponent (a permitted
choice of the paper's real exponent). No implicit multiplicative constants
remain in any of the three displayed asymptotic bounds. -/
def IdealizedProcessTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ D : ℕ, 1 ≤ D →
  ∀ T : ℝ, 1 < T → ∃ ell : ℕ, 1 ≤ ell ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : Binomial.Probability, Binomial.Approximation.Density θ T N p →
    ∃ a : Data, Specification N p D ell a ∧
      ∀ b : Data, Recursion N p D b → AgreeThrough D a b

/-- The uniform induction step. Its proof is internal to the idealized-process
argument, and is never accepted as an external input to its closed endpoint.
`ell'` is chosen before `N`, `p`, and the varying approximately universal state.
-/
def OneStepTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → ∀ n ell : ℕ, 1 ≤ ell →
  ∃ ell' : ℕ, ell ≤ ell' ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : Binomial.Probability, Binomial.Approximation.Density θ T N p →
  ∀ x : State n, StateSymmetric x → LevelEstimates N p ell x →
    ∃ q : Local.Tilt n, Solvable x q ∧ TiltSymmetric q ∧
      TiltEstimates N p ell' q ∧ StateSymmetric (nextState x q) ∧
      LevelEstimates N p ell' (nextState x q)

end MajorityDynamics.Idealized.Process
