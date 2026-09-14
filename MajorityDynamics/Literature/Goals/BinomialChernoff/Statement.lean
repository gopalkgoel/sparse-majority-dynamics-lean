import Mathlib.Probability.Distributions.Binomial
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Accepted scalar Chernoff input for A.2

Source: CKLT21, arXiv:2105.12709v1, Lemma 2.1(i)–(ii), printed p. 3,
https://arxiv.org/pdf/2105.12709v1#page=3, citing Janson, Theorem 1.
This is precisely the equal-parameter binomial specialization of those two
inequalities. The manuscript invokes Chernoff in both A.2 approximation proofs.
No window, moment, uniform asymptotic, or multivariate statement is imported.
The existing `Chernoff.lean` supplies the lower-tail set-Bernoulli formulation
used by the graph-degree proof; this interface also includes the upper tail.
-/

noncomputable section
open MeasureTheory

namespace MajorityDynamics.Literature

def BinomialChernoff : Prop :=
  ∀ (m : ℕ) (q : unitInterval), 0 < (m : ℝ) * q → ∀ t : ℝ, 0 ≤ t →
    (ProbabilityTheory.binomial m q).real {k | (m : ℝ) * q + t ≤ (k : ℝ)} ≤
      Real.exp (-(t ^ 2) / (2 * ((m : ℝ) * q) + 2 * t / 3)) ∧
    (ProbabilityTheory.binomial m q).real {k | (k : ℝ) ≤ (m : ℝ) * q - t} ≤
      Real.exp (-(t ^ 2) / (2 * ((m : ℝ) * q)))


end MajorityDynamics.Literature
