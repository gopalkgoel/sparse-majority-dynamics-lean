import MajorityDynamics.Analysis.ConditionalGaussian.Basic

/-!
# Coordinate moments of the natural exponential family

The tilted-measure integral formula identifies the actual first and centered
second moments with normalized weighted integrals. `PartitionFacts` supplies
the probability and second-moment hypotheses used for these identities.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ} {S : Covariance d} {O : Set (Space d)}

/-- Scalar integration against the natural law is normalized weighted integration.
This identity also respects the integral's convention for nonintegrable functions. -/
theorem integral_naturalLaw_eq_integral_div (S : Covariance d) (O : Set (Space d))
    (θ : Space d) (f : Space d → ℝ) :
    (∫ x, f x ∂naturalLaw S O θ) =
      (∫ x in O, f x * weight S θ x) / partition S O θ := by
  rw [naturalLaw, integral_tilted]
  change (∫ x in O, (weight S θ x / partition S O θ) * f x) = _
  rw [← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- The first weighted coordinate moment is integrable. -/
theorem integrable_coord_mul_weight (hp : PartitionFacts S O) (θ : Space d) (i : Fin d) :
    Integrable (fun x => x i * weight S θ x) (volume.restrict O) := by
  let := (hp.natural_regular θ).probability
  have hi : Integrable (fun x : Space d => x i) (naturalLaw S O θ) :=
    ((hp.natural_regular θ).memLp_two.eval_piLp i).integrable (by norm_num)
  have h := (integrable_tilted_iff (hp.integrable_weight θ) (fun x : Space d => x i)).mp hi
  simpa only [weight, smul_eq_mul, mul_comm] using h

/-- The second weighted coordinate moment is integrable. -/
theorem integrable_coord_mul_coord_mul_weight (hp : PartitionFacts S O) (θ : Space d)
    (i j : Fin d) :
    Integrable (fun x => x i * x j * weight S θ x) (volume.restrict O) := by
  have hi : Integrable (fun x : Space d => x i * x j) (naturalLaw S O θ) :=
    ((hp.natural_regular θ).memLp_two.eval_piLp i).integrable_mul
      ((hp.natural_regular θ).memLp_two.eval_piLp j)
  have h := (integrable_tilted_iff (hp.integrable_weight θ)
    (fun x : Space d => x i * x j)).mp hi
  simpa only [weight, smul_eq_mul, mul_comm] using h

/-- Coordinates commute with the Bochner expectation under the natural law. -/
theorem naturalMean_apply_eq_integral (hp : PartitionFacts S O) (θ : Space d) (i : Fin d) :
    naturalMean S O θ i = ∫ x, x i ∂naturalLaw S O θ := by
  let := (hp.natural_regular θ).probability
  exact eval_integral_piLp
    (fun j => ((hp.natural_regular θ).memLp_two.eval_piLp j).integrable (by norm_num)) i

/-- Coordinate formula for the first moment of the natural law. -/
theorem naturalMean_apply_eq_integral_div (hp : PartitionFacts S O) (θ : Space d) (i : Fin d) :
    naturalMean S O θ i =
      (∫ x in O, x i * weight S θ x) / partition S O θ := by
  rw [naturalMean_apply_eq_integral hp]
  exact integral_naturalLaw_eq_integral_div S O θ (fun x => x i)

/-- Coordinate formula for the centered covariance of the natural law. -/
theorem naturalCov_apply_eq_integral_div_sub (hp : PartitionFacts S O) (θ : Space d)
    (i j : Fin d) :
    naturalCov S O θ i j =
      (∫ x in O, x i * x j * weight S θ x) / partition S O θ -
        naturalMean S O θ i * naturalMean S O θ j := by
  let := (hp.natural_regular θ).probability
  change covariance (fun x : Space d => x i) (fun x => x j) (naturalLaw S O θ) = _
  have hlp (k : Fin d) : MemLp (fun x : Space d => x k) 2 (naturalLaw S O θ) :=
    (hp.natural_regular θ).memLp_two.eval_piLp k
  rw [covariance_eq_sub (hlp i) (hlp j)]
  rw [← naturalMean_apply_eq_integral hp θ i, ← naturalMean_apply_eq_integral hp θ j]
  rw [integral_naturalLaw_eq_integral_div]
  rfl

end MajorityDynamics.Analysis.ConditionalGaussian
