import MajorityDynamics.Analysis.ConditionalGaussian.WeightedIntegral
import MajorityDynamics.Analysis.ConditionalGaussian.NaturalMoments
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The derivative of the natural mean is its centered covariance

Coordinate means are quotients of weighted partition integrals. Differentiating
these quotients gives the centered second moments, and evaluation on the
standard orthonormal basis identifies the resulting operator with `matrixCLM`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace Topology

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

private theorem hasFDerivAt_of_coordinate_derivatives {f : Space d → Space d}
    {f' : Space d →L[ℝ] Space d} {θ : Space d}
    (h : ∀ i, HasFDerivAt (fun η => f η i)
      ((PiLp.proj 2 (fun _ : Fin d => ℝ) i).comp f') θ) : HasFDerivAt f f' θ := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).comp_hasFDerivAt_iff.mp
  apply hasFDerivAt_pi''
  exact h

private theorem matrixCLM_basisFun_apply (A : Covariance d) (i j : Fin d) :
    matrixCLM A (EuclideanSpace.basisFun (Fin d) ℝ j) i = A i j := by
  rw [EuclideanSpace.basisFun_apply]
  change (A *ᵥ Pi.single j 1) i = A i j
  simp [Matrix.mulVec_single]

/-- The Fréchet derivative of the natural mean is the centered covariance
matrix, acting on Euclidean space. -/
theorem hasFDerivAt_naturalMean {S : Covariance d} (hS : S.PosDef)
    {O : Set (Space d)} (hp : PartitionFacts S O) (θ : Space d) :
    HasFDerivAt (naturalMean S O) (matrixCLM (naturalCov S O θ)) θ := by
  have hconst : ∃ C : ℝ, ∃ n : ℕ, ∀ x : Space d, ‖(1 : ℝ)‖ ≤ C * ‖x‖ ^ n :=
    ⟨1, 0, by simp⟩
  have hden : HasFDerivAt (partition S O)
      (∫ x in O, weight S θ x • innerSL ℝ x) θ := by
    change HasFDerivAt (fun η => ∫ x in O, weight S η x) _ θ
    simpa only [one_mul] using
      hasFDerivAt_weightedIntegral hS O (f := fun _ => 1) continuous_const hconst θ
  have hden_int : Integrable (fun x => weight S θ x • innerSL ℝ x) (volume.restrict O) := by
    simpa only [one_mul] using
      integrable_weighted_derivative hS O (f := fun _ => 1) continuous_const hconst θ
  have hden_basis (j : Fin d) :
      (∫ x in O, weight S θ x • innerSL ℝ x) (EuclideanSpace.basisFun (Fin d) ℝ j) =
        ∫ x in O, x j * weight S θ x := by
    rw [ContinuousLinearMap.integral_apply hden_int]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_basisFun_real,
        smul_eq_mul, mul_comm]
  apply hasFDerivAt_of_coordinate_derivatives
  intro i
  have hcoord : Continuous (fun x : Space d => x i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).continuous
  have hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x : Space d, ‖x i‖ ≤ C * ‖x‖ ^ n := by
    refine ⟨1, 1, fun x => ?_⟩
    simpa only [one_mul, pow_one] using PiLp.norm_apply_le x i
  have hnum := hasFDerivAt_weightedIntegral hS O hcoord hgrowth θ
  have hnum_int := integrable_weighted_derivative hS O hcoord hgrowth θ
  have hnum_basis (j : Fin d) :
      (∫ x in O, (x i * weight S θ x) • innerSL ℝ x)
          (EuclideanSpace.basisFun (Fin d) ℝ j) =
        ∫ x in O, x i * x j * weight S θ x := by
    rw [ContinuousLinearMap.integral_apply hnum_int]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_basisFun_real,
        smul_eq_mul]
      ring
  have hquot := hnum.mul
    ((hasDerivAt_inv (hp.partition_pos θ).ne').comp_hasFDerivAt θ hden)
  have hfun : (fun η => naturalMean S O η i) =
      (fun η => ∫ x in O, x i * weight S η x) * ((fun t : ℝ => t⁻¹) ∘ partition S O) := by
    funext η
    simpa only [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv] using
      naturalMean_apply_eq_integral_div hp η i
  rw [hfun]
  convert! hquot using 1
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro j
  change ((PiLp.proj 2 (fun _ : Fin d => ℝ) i).comp (matrixCLM (naturalCov S O θ)))
      (EuclideanSpace.basisFun (Fin d) ℝ j) =
    ((∫ x in O, x i * weight S θ x) •
        (-(partition S O θ ^ 2)⁻¹ • (∫ x in O, weight S θ x • innerSL ℝ x)) +
      (partition S O θ)⁻¹ • (∫ x in O, (x i * weight S θ x) • innerSL ℝ x))
        (EuclideanSpace.basisFun (Fin d) ℝ j)
  simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    add_apply, smul_apply, smul_eq_mul]
  rw [matrixCLM_basisFun_apply, hden_basis, hnum_basis,
    naturalCov_apply_eq_integral_div_sub hp,
    naturalMean_apply_eq_integral_div hp, naturalMean_apply_eq_integral_div hp]
  field_simp
  ring

end MajorityDynamics.Analysis.ConditionalGaussian
