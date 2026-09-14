import MajorityDynamics.Analysis.ConditionalGaussian.Transport
import MajorityDynamics.Analysis.GradientInverse
import MajorityDynamics.Analysis.ConditionalGaussian.Conditioning
import MajorityDynamics.Analysis.ConditionalGaussian.GaussianDensity
import MajorityDynamics.Analysis.ConditionalGaussian.LawBridge
import MajorityDynamics.Analysis.ConditionalGaussian.LogPartition
import MajorityDynamics.Analysis.ConditionalGaussian.Coercivity
import MajorityDynamics.Analysis.ConditionalGaussian.Surjectivity

/-!
# Assembly of the conditional-mean bijection

Source: `thm:orthant-bijection`. The conditional reduction exposes the measure
and calculus inputs, then `core` supplies their checked proofs to close the
exact `CoreTheorem`. The cone corollary is absent from this module's dependencies.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

/-- Assemble D.2 from the precise conditioning, law, calculus and range facts.
Every assumption is explicit; no analytic statement is installed as an axiom. -/
theorem coreResult_of_facts (S : Covariance d) (hS : S.PosDef)
    (O : Set (Space d)) (hO : IsOpen O) (hconv : Convex ℝ O)
    (hconditioning : ConditioningTheorem) (hp : PartitionFacts S O)
    (hb : LawBridge S O) (hc : LogPartitionFacts S O) (hs : MeanSurjective S O) :
    CoreResult S O := by
  have hreg (γ : Space d) := conditional_regular_of_lawBridge hp hb γ
  have hmean (γ : Space d) : conditionalMean S O γ ∈ O :=
    (hconditioning d (conditionalLaw S O γ) O hO hconv (hreg γ)).1
  have hcov (γ : Space d) : (conditionalCov S O γ).PosDef :=
    (hconditioning d (conditionalLaw S O γ) O hO hconv (hreg γ)).2
  have hnCov (θ : Space d) : (naturalCov S O θ).PosDef :=
    (hconditioning d (naturalLaw S O θ) O hO hconv (hp.natural_regular θ)).2
  have hGinj : Function.Injective (naturalMean S O) :=
    injective_of_hasFDerivAt_pos hc.hasFDerivAt
      (fun θ _ hv => matrixCLM_inner_pos (hnCov θ) hv)
  have hinj : Function.Injective (conditionalMean S O) := by
    rw [conditionalMean_eq_comp hb]
    exact hGinj.comp (naturalParameter_bijective hS).1
  have hsurj : ∀ y ∈ O, ∃ γ, conditionalMean S O γ = y := by
    intro y hy
    obtain ⟨θ, hθ⟩ := hs y hy
    obtain ⟨γ, hγ⟩ := (naturalParameter_bijective hS).2 θ
    refine ⟨γ, ?_⟩
    rw [conditionalMean_eq_naturalMean hb, hγ]
    exact hθ
  have hderiv (γ : Space d) : ∃ e : Space d ≃L[ℝ] Space d,
      HasFDerivAt (conditionalMean S O) (e : Space d →L[ℝ] Space d) γ := by
    have hbij := jacobian_bijective hS γ (hcov γ)
    refine ⟨ContinuousLinearEquiv.ofBijective (jacobian S O γ)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), ?_⟩
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact conditionalMean_hasFDerivAt hb hc γ
  refine {
    mass_pos := ?_
    mass_lt_top := fun γ => measure_lt_top (gaussianLaw S γ) O
    probability := fun γ => (hreg γ).probability
    moments := fun γ => (hreg γ).memLp_two
    mean_mem := hmean
    covariance_posDef := hcov
    smooth := conditionalMean_contDiff hb hc
    hasFDerivAt := conditionalMean_hasFDerivAt hb hc
    derivative_bijective := fun γ => jacobian_bijective hS γ (hcov γ)
    strong_bijection := exists_strongBijection_of_hasFDerivAt hO
      (conditionalMean_contDiff hb hc) (fun γ _ => hmean γ) hinj hsurj hderiv }
  intro γ
  let : IsProbabilityMeasure (condition (gaussianLaw S γ) O) := (hreg γ).probability
  exact mass_pos_of_condition_probability (μ := gaussianLaw S γ)

/-- The closed conditional-mean theorem: every analytic input is proved. -/
theorem core : CoreTheorem := by
  intro d _hd S hS O hne hO hconv
  have hp := partitionFacts hS hne hO
  have hb := lawBridge S hS O hO.measurableSet (gaussianDensityFormula S hS) hp
  have hc := logPartitionFacts hS hne hO
  apply coreResult_of_facts S hS O hO hconv conditioning hp hb hc
  exact meanSurjective_of_coerciveAt S O hc
    (fun _ hy => coerciveAt_of_partitionFacts S O hO hp hy)

end MajorityDynamics.Analysis.ConditionalGaussian
