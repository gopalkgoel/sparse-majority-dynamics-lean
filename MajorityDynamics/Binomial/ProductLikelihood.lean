import MajorityDynamics.Binomial.ChangingTrials
import MajorityDynamics.Binomial.ProductTruncation

/-! # Common-window likelihood comparison for different product-binomial laws -/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Binomial.Approximation

variable {ι : Type*} [Fintype ι]

def productLikelihoodRemainder (η₀ η₁ : ι → ℕ) (c : ι → ℝ)
    (q₀ q₁ : ι → Probability) (a : ι → ℕ) : ℝ :=
  ∑ i, scalarLikelihoodRemainder (η₀ i) (η₁ i) (c i) (q₀ i) (q₁ i) (a i)

theorem product_changing_trials_log_error (η₀ η₁ : ι → ℕ) (c L : ι → ℝ)
    (q₀ q₁ : ι → Probability)
    (h₀ : ∀ i, c i < η₀ i) (h₁ : ∀ i, c i < η₁ i) (hL : ∀ i, 0 ≤ L i)
    (hL₀ : ∀ i, L i ≤ ((η₀ i : ℝ) - c i) / 2)
    (hL₁ : ∀ i, L i ≤ ((η₁ i : ℝ) - c i) / 2)
    (a b : ι → ℕ) (ha : a ∈ rectangle c L) (hb : b ∈ rectangle c L) :
    |productLikelihoodRemainder η₀ η₁ c q₀ q₁ b -
      productLikelihoodRemainder η₀ η₁ c q₀ q₁ a| ≤
        ∑ i, 4 * L i ^ 2 * (1 / ((η₀ i : ℝ) - c i) + 1 / ((η₁ i : ℝ) - c i)) := by
  rw [productLikelihoodRemainder, productLikelihoodRemainder, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun i _ => changing_trials_log_error (η₀ i) (η₁ i) (c i) (L i)
    (q₀ i) (q₁ i) (h₀ i) (h₁ i) (hL i) (hL₀ i) (hL₁ i) (a i) (b i) (ha i) (hb i)

theorem ambientMass_eq_prod_pointMass (η : ι → ℕ) (q : ι → Probability) (a : ι → ℕ) :
    ambientMass η q a = ∏ i, pointMass (η i) (a i) (q i) := by
  simp only [ambientMass, pointMass, ProbabilityTheory.binomial_real_singleton, closedProbability]

theorem log_ambientMass (η : ι → ℕ) (q : ι → Probability) (a : ι → ℕ)
    (ha : ∀ i, a i ≤ η i) :
    Real.log (ambientMass η q a) = ∑ i, Real.log (pointMass (η i) (a i) (q i)) := by
  rw [ambientMass_eq_prod_pointMass]
  exact Real.log_prod (fun i _ => (pointMass_pos (ha i) (q i)).ne')

theorem productLikelihoodRemainder_eq (η₀ η₁ : ι → ℕ) (c : ι → ℝ)
    (q₀ q₁ : ι → Probability) (a : ι → ℕ)
    (ha₀ : ∀ i, a i ≤ η₀ i) (ha₁ : ∀ i, a i ≤ η₁ i) :
    productLikelihoodRemainder η₀ η₁ c q₀ q₁ a =
      Real.log (ambientMass η₁ q₁ a) - Real.log (ambientMass η₀ q₀ a) -
        ∑ i, scalarTiltDifference (η₀ i) (η₁ i) (c i) (q₀ i) (q₁ i) * ((a i : ℝ) - c i) := by
  rw [log_ambientMass η₁ q₁ a ha₁, log_ambientMass η₀ q₀ a ha₀]
  simp only [productLikelihoodRemainder, scalarLikelihoodRemainder, Finset.sum_sub_distrib]

end MajorityDynamics.Binomial.Approximation
