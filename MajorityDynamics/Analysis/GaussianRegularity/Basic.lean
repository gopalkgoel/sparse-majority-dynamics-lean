import MajorityDynamics.Analysis.ConditionalGaussian.Basic

/-!
# The exact Appendix E.2 Gaussian regularity contract

The parameters are the mean, the diagonal variance, and the threshold, in that
order. All moments use the actual multivariate Gaussian measure. First and
second raw moments are unnormalized event integrals; conditional moments divide
them by the event probability. The final proposition contains no assumed
regularity or domination premise.
-/

noncomputable section

open Set MeasureTheory
open scoped Matrix NNReal

namespace MajorityDynamics.Analysis.GaussianRegularity

open ConditionalGaussian

abbrev Parameters (d r : ℕ) := (Space d × Space d) × Space r

def positiveVariance {d r : ℕ} (p : Parameters d r) : Prop :=
  ∀ i, 0 < p.1.2 i

def law {d r : ℕ} (p : Parameters d r) : Measure (Space d) :=
  gaussianLaw (Matrix.diagonal (fun i => p.1.2 i)) p.1.1

/-- The paper's weak half-space inequalities, including its zero-row case. -/
def event {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) (u : Space r) : Set (Space d) :=
  {x | ∀ i, -u i ≤ ∑ j, M i j * x j}

def mass {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) (p : Parameters d r) : ℝ :=
  (law p (event M p.2)).toReal

def firstMoment {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) (t : Fin d)
    (p : Parameters d r) : ℝ :=
  ∫ x in event M p.2, x t ∂law p

def secondMoment {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) (t t' : Fin d)
    (p : Parameters d r) : ℝ :=
  ∫ x in event M p.2, x t * x t' ∂law p

def conditionalFirst {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) (t : Fin d)
    (p : Parameters d r) : ℝ :=
  firstMoment M t p / mass M p

def conditionalSecond {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) (t t' : Fin d)
    (p : Parameters d r) : ℝ :=
  secondMoment M t t' p / mass M p

def conditionalCovariance {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) (t t' : Fin d)
    (p : Parameters d r) : ℝ :=
  conditionalSecond M t t' p - conditionalFirst M t p * conditionalFirst M t' p

/-- A single common Lipschitz constant controls all the paper's quantities. -/
structure RegularOn {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ)
    (P : Set (Parameters d r)) : Prop where
  positive_lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ P, c ≤ mass M p
  lipschitz : ∃ L : ℝ≥0,
    LipschitzOnWith L (mass M) P ∧
    (∀ t, LipschitzOnWith L (firstMoment M t) P) ∧
    (∀ t t', LipschitzOnWith L (secondMoment M t t') P) ∧
    (∀ t, LipschitzOnWith L (conditionalFirst M t) P) ∧
    (∀ t t', LipschitzOnWith L (conditionalSecond M t t') P) ∧
    (∀ t t', LipschitzOnWith L (conditionalCovariance M t t') P)

/-- Lemma E.2, with full row rank and compact positive-variance parameter sets.
Allowing dimension zero is a harmless strengthening of the paper's `d ≥ 1`. -/
def GaussianRegularityTheorem : Prop :=
  ∀ (d r : ℕ) (M : Matrix (Fin r) (Fin d) ℝ), M.rank = r →
    ∀ P : Set (Parameters d r), IsCompact P →
      (∀ p ∈ P, positiveVariance p) → RegularOn M P

end MajorityDynamics.Analysis.GaussianRegularity
