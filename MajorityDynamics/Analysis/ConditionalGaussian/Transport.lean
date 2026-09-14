import MajorityDynamics.Analysis.ConditionalGaussian.Basic

/-!
# Transport from the natural-parameter law to the actual Gaussian

These are conditional reductions: `LawBridge` and the partition/calculus facts
are explicit inputs. They do not assert those inputs or complete `CoreTheorem`.
The equality of probability laws transports both centered moments, and the
chain rule preserves the order of the covariance factors in the Jacobian.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ} {S : Covariance d} {O : Set (Space d)}

instance gaussianLaw_probability (S : Covariance d) (γ : Space d) :
    IsProbabilityMeasure (gaussianLaw S γ) := by
  unfold gaussianLaw
  infer_instance

theorem matrixCLM_inner_pos {A : Covariance d} (hA : A.PosDef)
    {v : Space d} (hv : v ≠ 0) : 0 < ⟪matrixCLM A v, v⟫ := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  apply hA.dotProduct_mulVec_pos
  intro h
  apply hv
  ext i
  exact congrFun h i

theorem condition_eq_zero_of_mass_zero {μ : Measure (Space d)}
    (h : μ O = 0) : condition μ O = 0 := by
  simp only [condition, Measure.restrict_eq_zero.mpr h, smul_zero]

theorem mass_pos_of_condition_probability {μ : Measure (Space d)}
    [IsProbabilityMeasure (condition μ O)] : 0 < μ O := by
  by_contra h
  have hzero : condition μ O = 0 :=
    condition_eq_zero_of_mass_zero (le_antisymm (le_of_not_gt h) bot_le)
  have hmass := measure_univ (μ := condition μ O)
  simp [hzero] at hmass

theorem conditional_regular_of_lawBridge
    (hp : PartitionFacts S O) (hb : LawBridge S O) (γ : Space d) :
    RegularOn (conditionalLaw S O γ) O := by
  rw [← hb γ]
  exact hp.natural_regular _

theorem conditionalMean_eq_naturalMean (hb : LawBridge S O) (γ : Space d) :
    conditionalMean S O γ = naturalMean S O (naturalParameter S γ) := by
  unfold conditionalMean naturalMean
  rw [hb γ]

theorem conditionalCov_eq_naturalCov (hb : LawBridge S O) (γ : Space d) :
    conditionalCov S O γ = naturalCov S O (naturalParameter S γ) := by
  unfold conditionalCov naturalCov
  rw [hb γ]

theorem conditionalMean_eq_comp (hb : LawBridge S O) :
    conditionalMean S O = naturalMean S O ∘ naturalParameter S :=
  funext (conditionalMean_eq_naturalMean hb)

theorem conditionalMean_contDiff (hb : LawBridge S O) (hc : LogPartitionFacts S O) :
    ContDiff ℝ ∞ (conditionalMean S O) := by
  rw [conditionalMean_eq_comp hb]
  exact hc.smooth_naturalMean.comp (matrixCLM S⁻¹).contDiff

theorem conditionalMean_hasFDerivAt (hb : LawBridge S O)
    (hc : LogPartitionFacts S O) (γ : Space d) :
    HasFDerivAt (conditionalMean S O) (jacobian S O γ) γ := by
  have h := (hc.hasFDerivAt (naturalParameter S γ)).comp γ (matrixCLM S⁻¹).hasFDerivAt
  simpa only [← conditionalMean_eq_comp hb, jacobian, conditionalCov_eq_naturalCov hb,
    naturalParameter] using h

theorem naturalParameter_bijective (hS : S.PosDef) :
    Function.Bijective (naturalParameter S) :=
  matrixCLM_bijective S⁻¹ hS.inv.isUnit

theorem jacobian_bijective (hS : S.PosDef) (γ : Space d)
    (hC : (conditionalCov S O γ).PosDef) : Function.Bijective (jacobian S O γ) :=
  (matrixCLM_bijective _ hC.isUnit).comp (matrixCLM_bijective _ hS.inv.isUnit)

end MajorityDynamics.Analysis.ConditionalGaussian
