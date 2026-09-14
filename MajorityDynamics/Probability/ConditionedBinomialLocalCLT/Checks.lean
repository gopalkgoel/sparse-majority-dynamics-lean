import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Main
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.MomentsChecks
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.TaylorChecks
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.InversionChecks

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
open ConditionedBinomialFourier

-- Expanded original-input endpoint: actual law, normalization and event.
example (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability) (m : ℕ),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      (N : ℝ)/T ≤ (m : ℝ) → (m : ℝ) ≤ T*N →
      let ρ := cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
      IsProbabilityMeasure ρ ∧ IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ρ)) ∧
      ∀ z : Fin d → ℤ, (∀ i, (z i : ℝ) = (m : ℝ)*(∫ y, (y i : ℝ) ∂ρ)) →
        c*((N : ℝ)^2*p)^(-(d : ℝ)/2) ≤
          (Measure.pi (fun _ : Fin m => ρ)).real {x | ∀ i, (∑ j, (x j i : ℤ)) = z i} := by
  simpa only [ConditionedBinomialFourier.copyLaw, ConditionedBinomialFourier.mean, ConditionedBinomialFourier.copySum] using
    uniform_local_clt θ hθlo hθhi d hd r M hM strict T hT

-- Expanded original-input endpoint: actual law, normalization and event.
example (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability) (m : ℕ),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      (N : ℝ)/T ≤ (m : ℝ) → (m : ℝ) ≤ T*N →
      let ρ := cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
      IsProbabilityMeasure ρ ∧ IsProbabilityMeasure (Measure.pi (fun _ : Fin m => ρ)) ∧
      ((∃ z : Fin d → ℤ, ∀ i, (z i : ℝ) = (m : ℝ)*(∫ y, (y i : ℝ) ∂ρ)) →
        c*((N : ℝ)^2*p)^(-(d : ℝ)/2) ≤
          (Measure.pi (fun _ : Fin m => ρ)).real {x | (fun i => ∑ j, (x j i : ℝ)) = fun i => (m : ℝ)*(∫ y, (y i : ℝ) ∂ρ)}) := by
  exact uniform_mean_local_clt θ hθlo hθhi d hd r M hM strict T hT

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Geometry.mem_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geometry.mem_cube

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Geometry.partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geometry.partition

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Geometry.partition_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geometry.partition_disjoint

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Geometry.positive_integral_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geometry.positive_integral_lower

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Geometry.fourier_integral_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geometry.fourier_integral_lower

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Scaling.delta_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scaling.delta_exponent

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Scaling.scaled_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scaling.scaled_radius

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Scaling.cube_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scaling.cube_scale

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Scaling.radius_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scaling.radius_eventually

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Scaling.integrated_error_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scaling.integrated_error_eventually

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Scaling.small_gaussian_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scaling.small_gaussian_scale

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.low_point_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_point_error

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.localConstant_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localConstant_pos

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.uniform_atom_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_atom_lower

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.uniform_local_clt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_local_clt

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.uniform_mean_local_clt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_mean_local_clt

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
