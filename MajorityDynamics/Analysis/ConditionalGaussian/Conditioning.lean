import MajorityDynamics.Analysis.ConditionalGaussian.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Conditioning on an open convex set

The mean belongs to the open set by strict hyperplane separation. Absolute
continuity rules out concentration on a hyperplane, so every nonzero linear
functional has positive variance. These arguments apply to any probability
law with finite second moment; they do not use Gaussian structure.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace Topology

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

/-- The expectation of an integrable random vector supported in an open convex
set lies in that set, including when the law is singular. -/
theorem mean_mem_of_isOpen_of_convex (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (O : Set (Space d)) (hO : IsOpen O) (hconv : Convex ℝ O)
    (hmass : ν O = 1) (hint : Integrable id ν) : mean ν ∈ O := by
  by_contra hmean
  obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hconv hO hmean
  have hae : ∀ᵐ x ∂ν, x ∈ O := (mem_ae_iff_prob_eq_one hO.measurableSet).mpr hmass
  have hLint : Integrable (fun x => L x) ν := L.integrable_comp hint
  have hpos : ∀ᵐ x ∂ν, 0 < L (mean ν) - L x :=
    hae.mono fun x hx => sub_pos.mpr (hL x hx)
  have hi : Integrable (fun x => L (mean ν) - L x) ν :=
    (integrable_const _).sub hLint
  have hz : (∫ x, L (mean ν) - L x ∂ν) = 0 := by
    rw [integral_sub (integrable_const _) hLint]
    simp only [integral_const, probReal_univ, one_smul]
    rw [show (∫ x, L x ∂ν) = L (mean ν) from L.integral_comp_comm hint]
    exact sub_self _
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (hpos.mono fun _ hx => hx.le) hi).mp hz
  obtain ⟨x, hx, hxeq⟩ := (hpos.and hzero).exists
  exact (ne_of_gt hx) hxeq

/-- Every proper real linear level set has zero Euclidean volume. -/
theorem volume_inner_level_eq_zero (v : Space d) (hv : v ≠ 0) (a : ℝ) :
    volume {x : Space d | ⟪v, x⟫ = a} = 0 := by
  let L : Space d →L[ℝ] ℝ := innerSL ℝ v
  let H : AffineSubspace ℝ (Space d) :=
    (affineSpan ℝ ({a} : Set ℝ)).comap L.toLinearMap.toAffineMap
  have hH : H ≠ ⊤ := by
    intro htop
    have hx (x : Space d) : L x = a := by
      have hm : x ∈ H := by rw [htop]; trivial
      simpa [H] using hm
    have ha : a = 0 := by simpa using (hx 0).symm
    have hself : ⟪v, v⟫ = 0 := by simpa [L, ha] using hx v
    exact hv (inner_self_eq_zero.mp hself)
  change volume ((fun x : Space d => ⟪v, x⟫) ⁻¹' {a}) = 0
  simpa [H, L, AffineSubspace.coe_comap] using Measure.addHaar_affineSubspace volume H hH

/-- Under an absolutely continuous probability law, a nonzero linear
functional cannot have zero centered variance. -/
theorem covarianceBilin_self_pos (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (hlp : MemLp id 2 ν) (hac : ν ≪ volume) (v : Space d) (hv : v ≠ 0) :
    0 < covarianceBilin ν v v := by
  apply lt_of_le_of_ne (covarianceBilin_self_nonneg v)
  intro hz
  have hvar : Var[fun x : Space d => ⟪v, x⟫; ν] = 0 := by
    rw [← covarianceBilin_self hlp]
    exact hz.symm
  have hae := ae_eq_integral_of_variance_eq_zero (hlp.const_inner v) hvar
  have hnull : ν {x : Space d | ⟪v, x⟫ = ν[fun x => ⟪v, x⟫]} = 0 :=
    hac (volume_inner_level_eq_zero v hv _)
  have hne : ∀ᵐ x ∂ν, ⟪v, x⟫ ≠ ν[fun x => ⟪v, x⟫] := by
    simpa only [ae_iff, not_not] using hnull
  obtain ⟨x, heq, hne⟩ := (hae.and hne).exists
  exact hne heq

/-- The centered bilinear covariance is represented by `covMatrix`. -/
theorem covarianceBilin_eq_covMatrix (ν : Measure (Space d)) [IsFiniteMeasure ν]
    (hlp : MemLp id 2 ν) (x y : Space d) :
    covarianceBilin ν x y = ∑ i, ∑ j, x i * y j * covMatrix ν i j := by
  have hid : (fun ω : Space d => WithLp.toLp 2 (fun i => ω i)) = id := rfl
  have h := covarianceBilin_apply_pi (μ := ν) (X := fun i ω => ω i)
    (fun i => hlp.eval_piLp i) x y
  simpa only [hid, Measure.map_id, covMatrix] using h

/-- Positive definiteness of the centered covariance needs only absolute
continuity, probability normalization, and a finite second moment. -/
theorem covMatrix_posDef (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (hlp : MemLp id 2 ν) (hac : ν ≪ volume) : (covMatrix ν).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, covMatrix] using
      (covariance_comm (X := fun x : Space d => x i) (Y := fun x => x j) (μ := ν)).symm
  · intro x hx
    let v : Space d := WithLp.toLp 2 x
    have hv : v ≠ 0 := by simpa [v] using hx
    have hpos := covarianceBilin_self_pos ν hlp hac v hv
    rw [covarianceBilin_eq_covMatrix ν hlp] at hpos
    have heq : star x ⬝ᵥ (covMatrix ν *ᵥ x) =
        ∑ i, ∑ j, v i * v j * covMatrix ν i j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum, v]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rwa [heq]

/-- Generic open-set conditioning, in the shared interface. -/
theorem conditioning : ConditioningTheorem := by
  intro d ν O hopen hconv hν
  let := hν.probability
  exact ⟨mean_mem_of_isOpen_of_convex ν O hopen hconv hν.mass
      (hν.memLp_two.integrable (by norm_num)),
    covMatrix_posDef ν hν.memLp_two hν.absolutelyContinuous⟩

/-- Normalizing a restriction of positive finite mass gives a probability law. -/
theorem condition_isProbabilityMeasure (μ : Measure (Space d)) (O : Set (Space d))
    (hpos : 0 < μ O) (hfinite : μ O < ∞) : IsProbabilityMeasure (condition μ O) := by
  constructor
  simp only [condition, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfinite.ne

/-- The normalized restriction assigns full mass to its conditioning set. -/
theorem condition_self (μ : Measure (Space d)) (O : Set (Space d))
    (hpos : 0 < μ O) (hfinite : μ O < ∞) : condition μ O O = 1 := by
  simp only [condition, Measure.smul_apply, Measure.restrict_apply_self, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfinite.ne

/-- Every finite moment survives normalization of a restriction of positive mass. -/
theorem memLp_condition {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (μ : Measure (Space d)) (O : Set (Space d)) {f : Space d → E}
    (hf : MemLp f p μ) (hpos : 0 < μ O) : MemLp f p (condition μ O) := by
  exact (hf.restrict O).smul_measure (ENNReal.inv_ne_top.mpr hpos.ne')

/-- Normalized restriction preserves absolute continuity. -/
theorem condition_absolutelyContinuous (μ : Measure (Space d)) (O : Set (Space d))
    (hac : μ ≪ volume) : condition μ O ≪ volume := by
  exact ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac).smul_left _

/-- A convenient constructor for the generic conditioning theorem's input. -/
theorem regularOn_condition (μ : Measure (Space d)) (O : Set (Space d))
    (hlp : MemLp id 2 μ) (hac : μ ≪ volume) (hpos : 0 < μ O) (hfinite : μ O < ∞) :
    RegularOn (condition μ O) O where
  probability := condition_isProbabilityMeasure μ O hpos hfinite
  memLp_two := memLp_condition μ O hlp hpos
  mass := condition_self μ O hpos hfinite
  absolutelyContinuous := condition_absolutelyContinuous μ O hac

end MajorityDynamics.Analysis.ConditionalGaussian
