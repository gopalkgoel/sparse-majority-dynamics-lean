import MajorityDynamics.Universal.Splitting
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! # Bit-complement transport of actual Gaussian laws and conditional means -/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis
open scoped RealInnerProductSpace Matrix

namespace MajorityDynamics.Universal

variable {k n : ℕ}

def rowFlipIsometry (k : ℕ) : Row k ≃ₗᵢ[ℝ] Row k :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (flipEquiv k)

@[simp] theorem rowFlipIsometry_apply (x : Row k) : rowFlipIsometry k x = rowFlip x := rfl

abbrev rowFlipCLM (k : ℕ) : Row k →L[ℝ] Row k :=
  (rowFlipIsometry k).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rowFlipCLM_apply (x : Row k) : rowFlipCLM k x = rowFlip x := rfl

theorem rowFlip_continuous : Continuous (rowFlip : Row k → Row k) :=
  (rowFlipIsometry k).continuous

theorem rowFlip_measurable : Measurable (rowFlip : Row k → Row k) :=
  rowFlip_continuous.measurable

/-- Coordinate permutation preserves the diagonal Gaussian when variances are symmetric. -/
theorem rowLaw_map_flip (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t)
    (hf : ∀ t, ν (flip t) = ν t) (γ : Row (n + 1)) :
    (rowLaw ν γ).map rowFlip = rowLaw ν (rowFlip γ) := by
  change (multivariateGaussian γ (covariance ν)).map (rowFlipCLM (n + 1)) =
    multivariateGaussian (rowFlip γ) (covariance ν)
  have hS := (covariance_posDef ν hν).posSemidef
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp
    · exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis
    (EuclideanSpace.basisFun (History (n + 1)) ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have he (i : History (n + 1)) :
        (fun u => ⟪(EuclideanSpace.basisFun (History (n + 1)) ℝ).toBasis i, u⟫) ∘
          rowFlipCLM (n + 1) = fun u => u (flip i) := by
      ext u
      simp [PiLp.inner_apply]
    simp_rw [he, covariance_eval_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS]
    have hinj : Function.Injective (@flip (n + 1)) := (flipEquiv (n + 1)).injective
    simp [covariance, Matrix.diagonal, hf, hinj.eq_iff]
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

/-- Normalized restriction commutes with the coordinate permutation. -/
theorem condition_map_flip (ρ : Measure (Row k)) (B : Set (Row k)) (hB : MeasurableSet B) :
    ConditionalGaussian.condition (ρ.map rowFlip) B =
      (ConditionalGaussian.condition ρ (rowFlip ⁻¹' B)).map rowFlip := by
  rw [ConditionalGaussian.condition, ConditionalGaussian.condition,
    Measure.map_apply rowFlip_measurable hB, Measure.restrict_map rowFlip_measurable hB,
    Measure.map_smul]

theorem mean_map_flip (ρ : Measure (Row k)) :
    ConditionalGaussian.mean (ρ.map rowFlip) = rowFlip (ConditionalGaussian.mean ρ) := by
  unfold ConditionalGaussian.mean
  rw [integral_map rowFlip_measurable.aemeasurable (by fun_prop)]
  exact (rowFlipIsometry k).toContinuousLinearEquiv.integral_comp_comm id

theorem historyCone_preimage_flip (s : History (n + 1)) :
    rowFlip ⁻¹' historyCone (flip s) = historyCone s := by
  ext x
  exact rowFlip_mem_historyCone s x

theorem childCone_preimage_flip (s : History (n + 1)) (b : Bool) :
    rowFlip ⁻¹' childCone (flip s) (!b) = childCone s b := by
  ext x
  exact rowFlip_mem_childCone s b x

theorem meanMap_flip (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (hf : ∀ t, ν (flip t) = ν t) (γ : Row (n + 1)) :
    meanMap (flip s) ν (rowFlip γ) = rowFlip (meanMap s ν γ) := by
  change ConditionalGaussian.mean
      (ConditionalGaussian.condition (rowLaw ν (rowFlip γ)) (historyCone (flip s))) = _
  rw [← rowLaw_map_flip ν hν hf γ,
    condition_map_flip _ _ (historyCone_isOpen _).measurableSet,
    historyCone_preimage_flip, mean_map_flip]
  rfl

theorem branchProbability_flip (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (hf : ∀ t, ν (flip t) = ν t) (γ : Row (n + 1)) (b : Bool) :
    branchProbability (flip s) ν (rowFlip γ) (!b) = branchProbability s ν γ b := by
  simp only [branchProbability, Measure.real, ← rowLaw_map_flip ν hν hf γ,
    Measure.map_apply rowFlip_measurable (childCone_isOpen _ _).measurableSet,
    Measure.map_apply rowFlip_measurable (historyCone_isOpen _).measurableSet,
    childCone_preimage_flip, historyCone_preimage_flip]

theorem branchMean_flip (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (hf : ∀ t, ν (flip t) = ν t) (γ : Row (n + 1)) (b : Bool) :
    branchMean (flip s) ν (rowFlip γ) (!b) = rowFlip (branchMean s ν γ b) := by
  unfold branchMean
  rw [← rowLaw_map_flip ν hν hf γ,
    condition_map_flip _ _ (childCone_isOpen _ _).measurableSet,
    childCone_preimage_flip, mean_map_flip]

end MajorityDynamics.Universal
