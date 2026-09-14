import MajorityDynamics.Analysis.ConditionalGaussian.Basic

/-!
# Equality of the Gaussian and natural-parameter conditional laws

Source: `latest/main.tex`, `thm:orthant-bijection`. Completing the square
identifies the Gaussian density with a positive constant times the natural
exponential weight. The constant cancels on normalizing the restriction.
The density formula and partition bounds are explicit inputs to this bridge;
no calculus or core theorem is imported.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

/-- Completing the square in natural coordinates. -/
theorem exponent_zero_sub (S : Covariance d) (hS : S.PosDef) (γ x : Space d) :
    exponent S 0 (x - γ) =
      exponent S (naturalParameter S γ) x + exponent S 0 γ := by
  have hsym : IsSelfAdjoint (matrixCLM S⁻¹) :=
    hS.inv.isHermitian.isSelfAdjoint.map _
  have hcross : ⟪γ, matrixCLM S⁻¹ x⟫ = ⟪matrixCLM S⁻¹ γ, x⟫ :=
    (hsym.isSymmetric γ x).symm
  simp only [exponent, naturalParameter, map_sub, inner_sub_left, inner_sub_right,
    inner_zero_left, hcross, real_inner_comm x (matrixCLM S⁻¹ γ)]
  ring

/-- Translation of the centered weight separates a positive parameter-only factor. -/
theorem weight_zero_sub (S : Covariance d) (hS : S.PosDef) (γ x : Space d) :
    weight S 0 (x - γ) = weight S 0 γ * weight S (naturalParameter S γ) x := by
  rw [weight, exponent_zero_sub S hS, Real.exp_add]
  exact mul_comm _ _

private theorem condition_withDensity_exp_mul (O : Set (Space d))
    (hO : MeasurableSet O) (f : Space d → ℝ) (c : ℝ) (hc : 0 < c)
    (hint : Integrable (fun x => Real.exp (f x)) (volume.restrict O))
    (hpos : 0 < ∫ x in O, Real.exp (f x)) :
    condition (volume.withDensity (fun x => ENNReal.ofReal (c * Real.exp (f x)))) O =
      (volume.restrict O).tilted f := by
  have hcZ : 0 < c * ∫ x in O, Real.exp (f x) := mul_pos hc hpos
  have hmass :
      volume.withDensity (fun x => ENNReal.ofReal (c * Real.exp (f x))) O =
        ENNReal.ofReal (c * ∫ x in O, Real.exp (f x)) := by
    rw [withDensity_apply _ hO,
      ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul c)
        (ae_of_all _ (fun x => (mul_pos hc (Real.exp_pos (f x))).le)),
      integral_const_mul]
  rw [condition, hmass, restrict_withDensity hO, ← ENNReal.ofReal_inv_of_pos hcZ,
    ← withDensity_smul' _ _ (by simp), Measure.tilted]
  congr 1
  ext x
  simp only [Pi.smul_apply, smul_eq_mul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hcZ.le)]
  congr 1
  field_simp

/-- Equality of the actual conditional Gaussian law and its natural-parameter law. -/
theorem lawBridge (S : Covariance d) (hS : S.PosDef) (O : Set (Space d))
    (hO : MeasurableSet O) (hDensity : GaussianDensityFormula S)
    (hPartition : PartitionFacts S O) : LawBridge S O := by
  obtain ⟨c, hc, hdensity⟩ := hDensity
  intro γ
  have hfactor : 0 < c * weight S 0 γ := mul_pos hc (Real.exp_pos _)
  have hρ : gaussianLaw S γ = volume.withDensity
      (fun x => ENNReal.ofReal
        ((c * weight S 0 γ) * Real.exp (exponent S (naturalParameter S γ) x))) := by
    rw [hdensity γ]
    congr 1
    ext x
    rw [weight_zero_sub S hS, mul_assoc]
    rfl
  unfold conditionalLaw
  rw [hρ, condition_withDensity_exp_mul O hO _ _ hfactor
    (hPartition.integrable_weight (naturalParameter S γ))
    (hPartition.partition_pos (naturalParameter S γ))]
  rfl

end MajorityDynamics.Analysis.ConditionalGaussian
