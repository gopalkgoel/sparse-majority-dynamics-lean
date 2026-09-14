import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Accepted Chernoff lower-tail input

Source: CKLT21, arXiv:2105.12709v1, Lemma 2.1(ii), printed p. 3,
https://arxiv.org/pdf/2105.12709v1#page=3, citing Janson, Theorem 1.
This is the equal-parameter specialization for the sum of indicators in a
fixed subfamily of a finite Bernoulli product. `setBernoulli u p` is Mathlib's
actual product law; the count is `(s ∩ selected).ncard`, with `s ⊆ u`.
Its mean is `|s| p`. No graph, degree, union-bound, or asymptotic claim is imported.
The manuscript invokes Chernoff in the proof of `lem:cklt-jumbled`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace MajorityDynamics.Literature

def BernoulliLowerTail : Prop :=
  ∀ (ι : Type) [Fintype ι] (u s : Set ι) (p : unitInterval), s ⊆ u →
    let μ : ℝ := s.ncard * (p : ℝ)
    0 < μ → ∀ t : ℝ, 0 ≤ t →
      setBernoulli u p {selected | ((s ∩ selected).ncard : ℝ) ≤ μ - t} ≤
        ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * μ)))


end MajorityDynamics.Literature
