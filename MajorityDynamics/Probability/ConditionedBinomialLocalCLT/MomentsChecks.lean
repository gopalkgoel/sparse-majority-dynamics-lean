import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT

-- The constants precede all varying data. Both moments use actual coordinate
-- expectations under the literal normalized restriction of the product law.
example (d : ℕ) {c U : ℝ} (hc : 0 < c) (hU : 1 ≤ U) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
        (E : Set (Fin d → ℕ)) (s : ℝ),
        c ≤ (Binomial.law η q).real E → 1 ≤ s →
        (∀ i, (η i : ℝ) * (q i : ℝ) ≤ U * s ^ 2) →
        let ρ := ProbabilityTheory.cond (Binomial.law η q) E
        (∀ f : (Fin d → ℕ) → ℝ, Integrable f ρ) ∧
        IsProbabilityMeasure ρ ∧ ∀ t : Fin d → ℝ,
          (∫ x, (∑ i, t i * ((x i : ℝ) - (∫ y, (y i : ℝ) ∂ρ))) ^ 2 ∂ρ) ≤
            C * s ^ 2 * ‖t‖ ^ 2 ∧
          (∫ x, |∑ i, t i * ((x i : ℝ) - (∫ y, (y i : ℝ) ∂ρ))| ^ 3 ∂ρ) ≤
            C * s ^ 3 * ‖t‖ ^ 3 :=
  uniform_directional_moments d hc hU

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.real_exp_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_exp_quadratic

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.binomial_exp_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_exp_integral

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.binomial_centered_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_centered_exp

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.abs_pow_le_exp_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_pow_le_exp_pair

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.binomial_scaled_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_scaled_moment

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.binomial_absolute_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_absolute_moment

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.integrable_cond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.integrable_cond

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.conditional_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.conditional_integral_le

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.raw_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.raw_coordinate

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.mean_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.mean_shift

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.centered_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.centered_coordinate

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.sum_abs_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.sum_abs_pow

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.dot_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.dot_abs_le

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments.directional_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Moments.directional_moment

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.uniform_directional_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_directional_moments

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
