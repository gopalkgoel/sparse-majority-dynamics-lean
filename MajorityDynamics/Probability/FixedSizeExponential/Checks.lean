import MajorityDynamics.Probability.FixedSizeExponential.Main

/-!
# Exact endpoint and dependency checks for Lemma C.5

The first examples check the named target and the public law interfaces.  The
expanded example deliberately writes the real-density, integer-size,
signed-weight quantifiers rather than checking only `FixedSizeExponentialTheorem`.
-/

open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.FixedSizeExponential

example : FixedSizeExponentialTheorem := fixed_size_exponential

example :
    ∀ n s : ℕ, s ≤ n →
      IsProbabilityMeasure (fixedSizeMeasure n s) := by
  intro n s hs
  exact fixedSizeMeasure_isProbability hs

example :
    ∀ {n s : ℕ}, 0 < s → s ≤ n → ∀ a : Fin n → ℝ,
      fixedSizeExpectation n s (bitLinear a) = (s : ℝ) / n * ∑ i, a i := by
  intro n s hs0 hsn a
  exact fixedSize_mean hs0 hsn a

example :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ p : ℝ,
          T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ) →
        ∀ a : Fin n → ℝ,
          (∀ i, |a i| ≤ T * Real.log (n : ℝ) / Real.sqrt (p * n)) →
        ∀ s : ℕ,
          T⁻¹ * p * n ≤ (s : ℝ) ∧ (s : ℝ) ≤ T * p * n →
          0 < p ∧ p < 1 ∧ 0 < s ∧ s < n ∧
            (fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
                C₁ * Real.sqrt (p * n) *
                  Real.exp (fixedSizeExpectation n s (bitLinear a) +
                    C₂ * (Real.log n) ^ 2) ∧
              fixedSizeExpectation n s (bitLinear a) =
                (s : ℝ) / n * ∑ i, a i) := by
  exact fixed_size_exponential

example :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ,
        T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ) →
        ∀ a : Fin n → ℝ,
          (∀ i, |a i| ≤ T * Real.log (n : ℝ) / Real.sqrt (p * n)) →
        ∀ s : ℕ,
          T⁻¹ * p * n ≤ (s : ℝ) ∧ (s : ℝ) ≤ T * p * n →
          fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
            Real.exp (fixedSizeExpectation n s (bitLinear a) + C * (Real.log n) ^ 2) := by
  exact fixed_size_exponential_corollary

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.fixedSizeEvent_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedSizeEvent_card

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.conditional_bernoulli_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditional_bernoulli_uniform

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.fixedSize_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedSize_mean

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.bitProduct_mgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bitProduct_mgf

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.fixed_size_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixed_size_exponential

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.fixed_size_exponential_corollary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixed_size_exponential_corollary

example :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ p : ℝ, (T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ)) →
        ∀ a : Fin n → ℝ,
          (∀ i, |a i| ≤ T * Real.log (n : ℝ) / Real.sqrt (p * n)) →
        ∀ s : ℤ, T⁻¹ * p * n ≤ (s : ℝ) → (s : ℝ) ≤ T * p * n →
          0 < p ∧ p < 1 ∧ 0 < s ∧ s < (n : ℤ) ∧ (s.toNat : ℤ) = s ∧
          (fixedSizeExpectation n s.toNat (fun ξ => Real.exp (bitLinear a ξ)) ≤
            C₁ * Real.sqrt (p * n) *
              Real.exp (fixedSizeExpectation n s.toNat (bitLinear a) +
                C₂ * (Real.log n) ^ 2)) ∧
          fixedSizeExpectation n s.toNat (bitLinear a) =
            (s : ℝ) / n * ∑ i, a i := fixed_size_exponential_int

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.fixed_size_exponential_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixed_size_exponential_int

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.conditioning_event_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditioning_event_pos

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.conditional_expectation_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditional_expectation_mul_le

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.fixedSize_mean_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedSize_mean_all

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.binomial_conditioning_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_conditioning_comparison

/-- info: 'MajorityDynamics.Probability.FixedSizeExponential.central_binomial_point_mass_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms central_binomial_point_mass_lower

end MajorityDynamics.Probability.FixedSizeExponential
