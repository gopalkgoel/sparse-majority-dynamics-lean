import MajorityDynamics.Idealized.Logit
import MajorityDynamics.Local.RowModel
import MajorityDynamics.Universal.Recursion
import MajorityDynamics.Analysis.GaussianRegularity.Basic

/-!
# Appendix E.3: the exact binomial row-limit contract

`n` means paper day `k = n + 1`. Sizes are natural numbers and do not have to
sum to `N`: they are the paper's eventually positive integer sizes. All
binomial quantities are finite formulas for the existing actual product law;
all Gaussian quantities are integrals against the actual universal row law.
The final proposition does not assume any of its approximation conclusions.
-/

noncomputable section
open Set MeasureTheory Topology
open scoped BigOperators ContDiff

namespace MajorityDynamics.Idealized.RowLimits

open Universal

variable {n : ℕ}

def rowTilt (N : ℕ) (p : Binomial.Probability) (σ : Row (n + 1)) :
    History (n + 1) → Binomial.Probability :=
  fun t => logitTilt N p (σ t) (ν n t)

def sizeVector (sizes : Local.Sizes n) : Row (n + 1) :=
  WithLp.toLp 2 (fun t => (sizes t : ℝ))

def nextImbalance (sizes : Local.Sizes n) : ℝ :=
  imbalance (Fin.last n) (sizeVector sizes)

def shift (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n) : ℝ :=
  (p : ℝ) * nextImbalance sizes / Real.sqrt ((p : ℝ) * N)

def error (ell' N : ℕ) (p : Binomial.Probability) (ξ : ℝ) : ℝ :=
  Real.log (N : ℝ) ^ ell' / Real.sqrt ((p : ℝ) * N) + ξ

structure AdmissibleSizes (N : ℕ) (p : Binomial.Probability) (ell : ℕ)
    (T ξ : ℝ) (s : History (n + 1)) (sizes : Local.Sizes n) : Prop where
  close : ∀ t, |(sizes t : ℝ) - (N : ℝ) * ν n t| ≤
    (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ ell
  history_balance : ∀ r : Fin n,
    |∑ t, historyMatrix s r t * (sizes t : ℝ)| ≤
      ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N)
  decision_balance : |nextImbalance sizes| ≤
    T * (N : ℝ) / Real.sqrt ((p : ℝ) * N)

/-- The original tie rule, with the next-decision threshold shifted by `u`.
The shift is inside the unsigned imbalance, before multiplication by `sign b`.
-/
def shiftedChildEvent (s : History (n + 1)) (b : Bool) (u : ℝ) :
    Set (Row (n + 1)) :=
  historyEvent s ∩ {x | decision (last s) b (imbalance (Fin.last n) x + u)}

@[simp] theorem shiftedChildEvent_zero (s : History (n + 1)) (b : Bool) :
    shiftedChildEvent s b 0 = childEvent s b := by
  simp [shiftedChildEvent, childEvent]

def binomialMass (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (σ : Row (n + 1)) : ℝ :=
  Binomial.eventMass (Local.trials sizes s) (rowTilt N p σ) S

def binomialFirst (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (t : History (n + 1)) (σ : Row (n + 1)) : ℝ :=
  ∑ a ∈ S, Binomial.mass (Local.trials sizes s) (rowTilt N p σ) a *
    Binomial.vector a t

def binomialSecond (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (t t' : History (n + 1)) (σ : Row (n + 1)) : ℝ :=
  ∑ a ∈ S, Binomial.mass (Local.trials sizes s) (rowTilt N p σ) a *
    (Binomial.vector a t * Binomial.vector a t')

def binomialMean (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (t : History (n + 1)) (σ : Row (n + 1)) : ℝ :=
  binomialFirst N p sizes s S t σ / binomialMass N p sizes s S σ

def binomialCovariance (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (t t' : History (n + 1)) (σ : Row (n + 1)) : ℝ :=
  binomialSecond N p sizes s S t t' σ / binomialMass N p sizes s S σ -
    binomialMean N p sizes s S t σ * binomialMean N p sizes s S t' σ

def binomialSplit (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (b : Bool) (σ : Row (n + 1)) : ℝ :=
  binomialMass N p sizes s (Local.childSupport sizes s b) σ /
    binomialMass N p sizes s (Local.historySupport sizes s) σ

def gaussianMass (σ : Row (n + 1)) (A : Set (Row (n + 1))) : ℝ :=
  (rowLaw (ν n) σ A).toReal

def gaussianFirst (σ : Row (n + 1)) (A : Set (Row (n + 1)))
    (t : History (n + 1)) : ℝ := ∫ x in A, x t ∂rowLaw (ν n) σ

def gaussianSecond (σ : Row (n + 1)) (A : Set (Row (n + 1)))
    (t t' : History (n + 1)) : ℝ := ∫ x in A, x t * x t' ∂rowLaw (ν n) σ

def gaussianMean (σ : Row (n + 1)) (A : Set (Row (n + 1)))
    (t : History (n + 1)) : ℝ := gaussianFirst σ A t / gaussianMass σ A

def gaussianCovariance (σ : Row (n + 1)) (A : Set (Row (n + 1)))
    (t t' : History (n + 1)) : ℝ :=
  gaussianSecond σ A t t' / gaussianMass σ A - gaussianMean σ A t * gaussianMean σ A t'

/-- Every binomial quantity appearing in the lemma is globally smooth in the
tilt vector, including the child conditional means (not just split moments).
-/
structure SmoothQuantities (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) : Prop where
  history_mass : ContDiff ℝ ∞ (binomialMass N p sizes s (Local.historySupport sizes s))
  child_mass : ∀ b, ContDiff ℝ ∞ (binomialMass N p sizes s (Local.childSupport sizes s b))
  split : ∀ b, ContDiff ℝ ∞ (binomialSplit N p sizes s b)
  history_mean : ∀ t, ContDiff ℝ ∞ (binomialMean N p sizes s (Local.historySupport sizes s) t)
  child_mean : ∀ b t, ContDiff ℝ ∞ (binomialMean N p sizes s (Local.childSupport sizes s b) t)
  covariance : ∀ t t', ContDiff ℝ ∞
    (binomialCovariance N p sizes s (Local.historySupport sizes s) t t')

/-- The approximation estimates for a fixed next-decision shift. Separating
this record permits the final small-shift clause to use the identical bounds.
-/
structure Estimates (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (u C ε : ℝ) : Prop where
  history_probability : |binomialMass N p sizes s (Local.historySupport sizes s) σ -
    gaussianMass σ (historyEvent s)| ≤ C * ε
  split_probability : ∀ b, |binomialSplit N p sizes s b σ -
    gaussianMass σ (shiftedChildEvent s b u) / gaussianMass σ (historyEvent s)| ≤ C * ε
  history_mean : ∀ t,
    |(binomialMean N p sizes s (Local.historySupport sizes s) t σ - (p : ℝ) * sizes t) /
      Real.sqrt ((p : ℝ) * N) - gaussianMean σ (historyEvent s) t| ≤ C * ε
  child_mean : ∀ b t,
    |(binomialMean N p sizes s (Local.childSupport sizes s b) t σ - (p : ℝ) * sizes t) /
      Real.sqrt ((p : ℝ) * N) - gaussianMean σ (shiftedChildEvent s b u) t| ≤ C * ε
  covariance : ∀ t t',
    |binomialCovariance N p sizes s (Local.historySupport sizes s) t t' σ /
      ((p : ℝ) * N) - gaussianCovariance σ (historyEvent s) t t'| ≤ C * ε

/-- Lemma E.3. The quantifier order enforces exactly the paper's dependence:
`ell'` depends only on day and `ell`; `c₀` only on day, `T`, and `R`.
`C` and `N₀` are uniform over `s`, `p`, `ξ`, sizes, and bounded tilts.
The extra uniformity over the finite history `s` is harmless.
-/
def RowLimitsTheorem : Prop :=
  ∀ n : ℕ, ∃ lower : ℝ → ℝ → ℝ,
    ∀ ell : ℕ, 1 ≤ ell → ∃ ell' : ℕ,
    ∀ (T R : ℝ), 1 < T → 0 < R → 0 < lower T R ∧
      ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
        ∀ (N : ℕ), N₀ ≤ N → ∀ p : Binomial.Probability,
          T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) → (p : ℝ) < T * (N : ℝ) ^ (-θ) →
          ∀ ξ : ℝ, 0 < ξ → ξ ≤ T → ∀ (s : History (n + 1)) (sizes : Local.Sizes n),
            AdmissibleSizes N p ell T ξ s sizes →
            SmoothQuantities N p sizes s ∧
            ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
              lower T R ≤ gaussianMass σ (historyEvent s) ∧
              (∀ b, lower T R ≤ gaussianMass σ (shiftedChildEvent s b (shift N p sizes))) ∧
              |shift N p sizes| ≤ T ∧
              Estimates N p sizes s σ (shift N p sizes) C (error ell' N p ξ) ∧
              (|nextImbalance sizes| ≤ ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N) →
                |shift N p sizes| ≤ ξ ∧ ξ ≤ error ell' N p ξ ∧
                (∀ b, lower T R ≤ gaussianMass σ (childEvent s b)) ∧
                Estimates N p sizes s σ 0 C (error ell' N p ξ))

end MajorityDynamics.Idealized.RowLimits
