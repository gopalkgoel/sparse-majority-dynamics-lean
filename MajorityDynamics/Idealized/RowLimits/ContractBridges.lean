import MajorityDynamics.Idealized.RowLimits.Basic

/-! The finite formulas in the E.3 contract are moments of actual conditional
laws, and its Gaussian history mean is §4's existing conditional mean map. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis
variable {n : ℕ}

theorem binomialMean_eq_conditionalMean (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s)))
    (t : History (n + 1)) (σ : Row (n + 1)) :
    binomialMean N p sizes s S t σ =
      Binomial.conditionalMean (Local.trials sizes s) (rowTilt N p σ) S t := by
  simp only [binomialMean, binomialFirst, binomialMass, Binomial.conditionalMean,
    Binomial.expectation, Binomial.conditionalWeight, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem binomialMean_eq_integral (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s)))
    (t : History (n + 1)) (σ : Row (n + 1)) :
    binomialMean N p sizes s S t σ = ∫ a, (a t : ℝ) ∂
      Binomial.conditionalLaw (Local.trials sizes s) (rowTilt N p σ) S := by
  rw [binomialMean_eq_conditionalMean, Binomial.conditionalMean_eq_integral]

theorem binomialMean_eq_rowMean (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s t : History (n + 1)) (σ : Row (n + 1)) :
    binomialMean N p sizes s (Local.historySupport sizes s) t σ =
      Local.rowMean sizes (fun _ => rowTilt N p σ) s t :=
  binomialMean_eq_conditionalMean N p sizes s _ t σ

theorem binomialSplit_eq_splitProbability (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool) (σ : Row (n + 1)) :
    binomialSplit N p sizes s b σ =
      Local.splitProbability sizes (fun _ => rowTilt N p σ) s b := rfl

theorem binomialSplit_eq_conditionalProbability (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool) (σ : Row (n + 1)) :
    binomialSplit N p sizes s b σ =
      (Binomial.conditionalLaw (Local.trials sizes s) (rowTilt N p σ)
        (Local.historySupport sizes s)).real (Binomial.event (Local.childSupport sizes s b)) := by
  exact (Binomial.conditionalLaw_event _ _ _ _ (Local.childSupport_subset sizes s b)).symm

theorem binomialSecond_eq_integral (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s)))
    (t t' : History (n + 1)) (σ : Row (n + 1)) :
    binomialSecond N p sizes s S t t' σ / binomialMass N p sizes s S σ =
      ∫ a, (a t : ℝ) * (a t' : ℝ) ∂
        Binomial.conditionalLaw (Local.trials sizes s) (rowTilt N p σ) S := by
  rw [Binomial.integral_conditionalLaw]
  simp only [binomialSecond, binomialMass, Binomial.expectation,
    Binomial.conditionalWeight, Finset.sum_div, Binomial.point, Binomial.vector]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem gaussianMean_eq_integral (σ : Row (n + 1)) (A : Set (Row (n + 1)))
    (t : History (n + 1)) :
    gaussianMean σ A t =
      ∫ x, x t ∂ConditionalGaussian.condition (rowLaw (ν n) σ) A := by
  simp only [gaussianMean, gaussianFirst, gaussianMass, ConditionalGaussian.condition,
    integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  exact div_eq_inv_mul _ _

theorem gaussianMean_history_eq_meanMap (s : History (n + 1))
    (σ : Row (n + 1)) (t : History (n + 1)) :
    gaussianMean σ (historyEvent s) t = meanMap s (ν n) σ t := by
  rw [gaussianMean_eq_integral, history_condition_eq s (ν n) (ν_positive n)]
  let hreg := ConditionalGaussian.gaussian_conditional_regular _
    (covariance_posDef _ (ν_positive n)) _ (historyCone_nonempty s)
    (historyCone_isOpen s) σ
  let := hreg.probability
  exact (eval_integral_piLp
    (fun j => (hreg.memLp_two.eval_piLp j).integrable (by norm_num)) t).symm

theorem gaussianMean_child_eq_branchMean (s : History (n + 1)) (b : Bool)
    (σ : Row (n + 1)) (t : History (n + 1)) :
    gaussianMean σ (childEvent s b) t = branchMean s (ν n) σ b t := by
  rw [gaussianMean_eq_integral]
  exact (branchMean_coordinate s (ν n) (ν_positive n) σ b t).symm

end MajorityDynamics.Idealized.RowLimits
