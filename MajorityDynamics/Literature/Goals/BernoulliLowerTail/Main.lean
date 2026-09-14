import MajorityDynamics.Literature.Goals.BernoulliLowerTail.Statement
import MajorityDynamics.Literature.Concentration.BinomialLowerTail
import MajorityDynamics.Literature.Concentration.SetBernoulli

/-!
# L01: Bernoulli subset lower tail

This proves the unchanged CKLT21, Lemma 2.1(ii) specialization recorded in
`Statement.lean`: https://arxiv.org/abs/2105.12709v1 . The selected subset count
has the actual binomial law, whose exponential-moment lower-tail bound is proved in
the shared concentration module. No unfinished literature input is used.
-/

open MeasureTheory ProbabilityTheory

namespace MajorityDynamics.Literature

/-- The Chernoff lower-tail bound for the selected count of a fixed Bernoulli subfamily. -/
theorem bernoulli_lower_tail : BernoulliLowerTail := by
  intro ι _ u s p hsu
  dsimp only
  intro hμ t ht
  change setBernoulli u p {selected | (s ∩ selected).ncard ∈
    {k : ℕ | (k : ℝ) ≤ (s.ncard : ℝ) * p - t}} ≤ _
  rw [Concentration.setBernoulli_inter_ncard_apply u s p hsu
    {k | (k : ℝ) ≤ (s.ncard : ℝ) * p - t}]
  apply (ENNReal.toReal_le_toReal (by simp) (by simp)).mp
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  exact Concentration.binomial_lower_tail s.ncard p hμ t ht

end MajorityDynamics.Literature
