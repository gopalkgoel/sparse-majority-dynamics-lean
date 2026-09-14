import MajorityDynamics.Probability.ConditionedBinomialFourier.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.ConditionedBinomialFourier

-- These are the literal product-copy integral and original probability measure.
example {d : ℕ} (ρ : Measure (Fin d → ℕ)) (m : ℕ) (t : Fin d → ℝ) :
    centeredChi ρ m t =
      ∫ x : Fin m → Fin d → ℕ,
        Complex.exp (Complex.I * ((∑ i, t i *
          ((∑ j, (x j i : ℝ)) - (m : ℝ)*(∫ y, (y i : ℝ) ∂ρ)) : ℝ) : ℂ))
        ∂Measure.pi (fun _ : Fin m => ρ) := rfl

-- The cube uses the sup norm and the exact paper cutoff, with ordinary volume.
example (d N : ℕ) (p δ : ℝ) (t : Fin d → ℝ) :
    t ∈ HighFrequency.region d N p δ ↔
      (∀ i, |t i| ≤ Real.pi) ∧ (N : ℝ)^δ/Real.sqrt ((N : ℝ)^2*p) < ‖t‖ := Iff.rfl

-- Mean-integrality is deliberately absent from the phase/modulus identity.
example {d : ℕ} (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t c : Fin d → ℝ) :
    (∫ x, Complex.exp (Complex.I * ((∑ i, t i *
      ((∑ j, (x j i : ℝ)) - c i) : ℝ) : ℂ))
      ∂Measure.pi (fun _ : Fin m => ρ)) = phase t (-c) * (chi ρ t)^m :=
  translated_copySum_chi ρ m t c

-- Expanded original-input acceptance signature; no internal certificates escape.
example (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) (δ A : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1/2) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability) (m : ℕ),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      (N : ℝ)/T ≤ (m : ℝ) → (m : ℝ) ≤ T*N →
      let ρ := cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
      IsProbabilityMeasure ρ ∧ IsProbabilityMeasure (copyLaw ρ m) ∧
      IntegrableOn (centeredChi ρ m) (HighFrequency.region d N p δ) ∧
      (∀ t ∈ HighFrequency.region d N p δ, ‖centeredChi ρ m t‖ ≤ (N : ℝ)^(-A)) ∧
      ‖∫ t in HighFrequency.region d N p δ, centeredChi ρ m t‖ ≤
        (N : ℝ)^(-A)*((N : ℝ)^2*p)^(-(d : ℝ)/2) :=
  uniform_high_frequency θ hθlo hθhi d hd r M hM strict T hT δ A hδ0 hδ hA

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.intervalChi_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalChi_eq_sum

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.intervalChi_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalChi_norm_le_one

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.intervalConstant_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalConstant_pos

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.intervalChi_norm_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intervalChi_norm_gap

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.phase_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_norm

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.chi_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chi_norm_le_one

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.copyLaw_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copyLaw_probability

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.copySum_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copySum_chi

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.translated_copySum_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms translated_copySum_chi

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.centeredChi_eq_phase_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centeredChi_eq_phase_mul_pow

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.centeredChi_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centeredChi_norm_eq

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.chi_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chi_continuous

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.centeredChi_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centeredChi_continuous

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.chi_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chi_mixture

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.uniformBox_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_integral

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.uniformBox_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_chi

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.exists_abs_eq_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_abs_eq_norm

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.uniformBox_chi_norm_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_chi_norm_gap

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.width_min_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms width_min_lower

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.eventually_length_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_length_sixteen

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.mixture_norm_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixture_norm_gap

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.centeredChi_exp_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centeredChi_exp_of_gap

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.gapConstant_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gapConstant_pos

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.gapConstant_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gapConstant_le_half

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.rectangular_mixture_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rectangular_mixture_gap

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.uniform_global_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_global_gap

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.uniform_high_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_high_frequency

end MajorityDynamics.Probability.ConditionedBinomialFourier
