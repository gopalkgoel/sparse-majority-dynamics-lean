import MajorityDynamics.Literature.Goals.BinomialChernoff.Statement
import MajorityDynamics.Literature.Concentration.BinomialUpperTail

/-!
# L02 — Scalar binomial Chernoff bounds

This proves the existing literature contract: CKLT21, Lemma 2.1(i)–(ii),
https://arxiv.org/abs/2105.12709v1 . The original binomial law, inclusive tail
events, complete parameter range, and exact constants are preserved.

The shared lower-tail module computes the binomial exponential moment and
uses exponential Markov. The upper-tail module proves the Bennett exponent
bound yielding the Bernstein denominator `2 * μ + 2 * t / 3`.
-/

namespace MajorityDynamics.Literature

theorem binomial_chernoff : BinomialChernoff := by
  intro m q hμ t ht
  exact ⟨Concentration.binomial_upper_tail m q hμ t ht,
    Concentration.binomial_lower_tail m q hμ t ht⟩

/-- info: 'MajorityDynamics.Literature.binomial_chernoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms binomial_chernoff

end MajorityDynamics.Literature
