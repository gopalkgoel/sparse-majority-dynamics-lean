import MajorityDynamics.Analysis.ConditionalGaussian.WeightedIntegral
import MajorityDynamics.Analysis.ConditionalGaussian.NaturalMoments
import MajorityDynamics.Analysis.ConditionalGaussian.MeanDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Log-partition smoothness and the natural mean

Differentiating raw volume integrals identifies the log-partition gradient
with the expectation under the normalized natural law. Coordinate moment
formulas give smoothness of that mean and identify its derivative with the
centered covariance matrix.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ} {S : Covariance d} {O : Set (Space d)}

private theorem growth_one :
    ∃ C : ℝ, ∃ n : ℕ, ∀ x : Space d, ‖(1 : ℝ)‖ ≤ C * ‖x‖ ^ n :=
  ⟨1, 0, by simp⟩

private theorem growth_coord (i : Fin d) :
    ∃ C : ℝ, ∃ n : ℕ, ∀ x : Space d, ‖x i‖ ≤ C * ‖x‖ ^ n :=
  ⟨1, 1, fun x => by simpa using PiLp.norm_apply_le x i⟩

/-- The raw partition function is smooth in every natural parameter. -/
theorem contDiff_partition (hS : S.PosDef) (O : Set (Space d)) :
    ContDiff ℝ ∞ (partition S O) := by
  change ContDiff ℝ ∞ (fun θ => ∫ x in O, weight S θ x)
  simpa only [one_mul] using
    contDiff_weightedIntegral hS O continuous_const (growth_one (d := d))

/-- Strict positivity allows the smooth logarithm of the partition function. -/
theorem contDiff_logPartition (hS : S.PosDef) (hp : PartitionFacts S O) :
    ContDiff ℝ ∞ (logPartition S O) :=
  (contDiff_partition hS O).log (fun θ => (hp.partition_pos θ).ne')

/-- Each mean coordinate is a smooth weighted moment divided by a positive
partition function. -/
theorem contDiff_naturalMean (hS : S.PosDef) (hp : PartitionFacts S O) :
    ContDiff ℝ ∞ (naturalMean S O) := by
  apply contDiff_euclidean.mpr
  intro i
  have hi := (contDiff_weightedIntegral hS O (EuclideanSpace.proj i).continuous
    (growth_coord i)).div (contDiff_partition hS O) (fun θ => (hp.partition_pos θ).ne')
  change ContDiff ℝ ∞ (fun θ => (∫ x in O, x i * weight S θ x) / partition S O θ) at hi
  simpa only [← naturalMean_apply_eq_integral_div hp] using hi

/-- The log-partition gradient is the mean of the actual normalized natural law. -/
theorem hasGradientAt_logPartition (hS : S.PosDef) (hp : PartitionFacts S O)
    (θ : Space d) : HasGradientAt (logPartition S O) (naturalMean S O θ) θ := by
  have hprob := (hp.natural_regular θ).probability
  have hi : Integrable id (naturalLaw S O θ) :=
    (hp.natural_regular θ).memLp_two.integrable (by norm_num)
  have hint : Integrable (fun x => weight S θ x • innerSL ℝ x) (volume.restrict O) := by
    simpa only [one_mul] using
      integrable_weighted_derivative hS O continuous_const (growth_one (d := d)) θ
  have hder : HasFDerivAt (partition S O)
      (∫ x in O, weight S θ x • innerSL ℝ x) θ := by
    change HasFDerivAt (fun η => ∫ x in O, weight S η x) _ θ
    simpa only [one_mul] using
      hasFDerivAt_weightedIntegral hS O continuous_const (growth_one (d := d)) θ
  rw [hasGradientAt_iff_hasFDerivAt]
  apply (hder.log (hp.partition_pos θ).ne').congr_fderiv
  ext y
  simp only [smul_apply, smul_eq_mul, InnerProductSpace.toDual_apply_apply]
  rw [ContinuousLinearMap.integral_apply hint]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hmean : ⟪naturalMean S O θ, y⟫ = ∫ x, ⟪x, y⟫ ∂(naturalLaw S O θ) := by
    simpa only [naturalMean, mean, id_eq, real_inner_comm] using (integral_inner hi y).symm
  rw [hmean, naturalLaw, integral_tilted]
  simp only [weight, partition, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

/-- The complete calculus interface from established raw partition facts. -/
theorem logPartitionFacts_of_partitionFacts (hS : S.PosDef) (hp : PartitionFacts S O) :
    LogPartitionFacts S O where
  smooth_logPartition := contDiff_logPartition hS hp
  smooth_naturalMean := contDiff_naturalMean hS hp
  hasGradientAt := hasGradientAt_logPartition hS hp
  hasFDerivAt := hasFDerivAt_naturalMean hS hp

/-- Smoothness, the gradient identity, and the centered-covariance derivative
for any positive-definite covariance and nonempty open conditioning set. -/
theorem logPartitionFacts (hS : S.PosDef) (hne : O.Nonempty) (hO : IsOpen O) :
    LogPartitionFacts S O :=
  logPartitionFacts_of_partitionFacts hS (partitionFacts hS hne hO)

end MajorityDynamics.Analysis.ConditionalGaussian
