import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Inversion

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
open ConditionedBinomialFourier

example {d : ℕ} (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (z : Fin d → ℤ)
    (hz : ∀ i, (z i : ℝ) = (m : ℝ) * ∫ x, (x i : ℝ) ∂ρ) :
    (Measure.pi (fun _ : Fin m => ρ)).real
      {x | ∀ i, (∑ j, (x j i : ℤ)) = z i} =
      (∫ t in {t : Fin d → ℝ | ∀ i, |t i| ≤ Real.pi},
        ∫ x : Fin m → Fin d → ℕ,
          Complex.exp (Complex.I * ((∑ i, t i *
            ((∑ j, (x j i : ℝ)) - (m : ℝ) * (∫ y, (y i : ℝ) ∂ρ)) : ℝ) : ℂ))
          ∂Measure.pi (fun _ : Fin m => ρ)).re / (2 * Real.pi) ^ d := by
  simpa only [integerSum_event_forall, copyLaw, HighFrequency.cube, centeredChi,
    phase, dot, copySum, mean, Pi.sub_apply] using integerSum_probability ρ m z hz

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integerSum_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integerSum_cast

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integerSum_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integerSum_event_eq

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integral_integer_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_integer_harmonic

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integral_lattice_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_lattice_phase

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integral_translated_copySum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_translated_copySum

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integral_centeredChi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_centeredChi

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integerSum_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integerSum_probability

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integerSum_mean_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integerSum_mean_event

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.integerSum_event_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integerSum_event_forall

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.mean_event_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mean_event_probability

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
