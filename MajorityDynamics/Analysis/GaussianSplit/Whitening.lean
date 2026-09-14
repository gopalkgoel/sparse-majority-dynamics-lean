import MajorityDynamics.Analysis.GaussianSplit.WhiteningBasic
import MajorityDynamics.Analysis.GaussianSplit.Main
import MajorityDynamics.Analysis.ConditionalGaussian.Main

/-!
# Transport of the Gaussian split theorem through an affine Gaussian model

The standard-Gaussian regression argument applies to the actual multivariate
Gaussian after whitening. All conditioning events and centered covariances are
transported through the same affine map.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder

namespace MajorityDynamics.Analysis.GaussianSplit

open ConditionalGaussian

variable {d m : ℕ}

theorem affineHistory_measurable (h : Fin m → Space d) (c : Fin m → ℝ) :
    MeasurableSet (affineHistory h c) := by
  simp only [affineHistory, ofPred_forall]
  exact MeasurableSet.iInter fun i => isOpen_lt continuous_const
    (continuous_const.add (continuous_const.inner continuous_id)) |>.measurableSet

def whiteningMap (S : Covariance d) (γ : Space d) (x : Space d) : Space d :=
  γ + matrixCLM (CFC.sqrt S) x

def whiteningCoeff (S : Covariance d) (a : Space d) : Space d :=
  (matrixCLM (CFC.sqrt S)).adjoint a

theorem whiteningMap_continuous (S : Covariance d) (γ : Space d) :
    Continuous (whiteningMap S γ) :=
  continuous_const.add (matrixCLM _).continuous

theorem linear_whiteningMap (S : Covariance d) (γ a x : Space d) :
    linear a (whiteningMap S γ x) = linear a γ + linear (whiteningCoeff S a) x := by
  simp only [linear, whiteningMap, inner_add_right, whiteningCoeff,
    ContinuousLinearMap.adjoint_inner_left]

theorem whiteningMap_law (S : Covariance d) (γ : Space d) :
    (stdGaussian (Space d)).map (whiteningMap S γ) = gaussianLaw S γ := rfl

theorem condition_map_preimage (ρ : Measure (Space d)) (f : Space d → Space d)
    (hf : Measurable f) (E : Set (Space d)) (hE : MeasurableSet E) :
    condition (ρ.map f) E = (condition ρ (f ⁻¹' E)).map f := by
  rw [condition, condition, Measure.map_smul, Measure.restrict_map hf hE,
    Measure.map_apply hf hE]

theorem covarianceBilin_whiteningMap (ρ : Measure (Space d)) [IsProbabilityMeasure ρ]
    (hρ : MemLp id 2 ρ) (S : Covariance d) (γ a b : Space d) :
    covarianceBilin (ρ.map (whiteningMap S γ)) a b =
      covarianceBilin ρ (whiteningCoeff S a) (whiteningCoeff S b) := by
  let : IsProbabilityMeasure (ρ.map (matrixCLM (CFC.sqrt S))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have he : whiteningMap S γ = (fun x : Space d => γ + x) ∘ matrixCLM (CFC.sqrt S) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    covarianceBilin_map_const_add, covarianceBilin_map hρ]
  rfl

theorem integral_linear_whiteningMap (ρ : Measure (Space d)) [IsProbabilityMeasure ρ]
    (hρ : MemLp id 2 ρ) (S : Covariance d) (γ a : Space d) :
    (∫ x, linear a x ∂ρ.map (whiteningMap S γ)) =
      linear a γ + ∫ x, linear (whiteningCoeff S a) x ∂ρ := by
  rw [integral_map (whiteningMap_continuous S γ).measurable.aemeasurable
    (continuous_const.inner continuous_id).aestronglyMeasurable]
  simp_rw [linear_whiteningMap]
  rw [integral_add (integrable_const _) ((hρ.const_inner _).integrable (by norm_num))]
  simp

theorem stdGaussian_condition_regular (E : Set (Space d))
    (hE : 0 < stdGaussian (Space d) E) :
    RegularOn (condition (stdGaussian (Space d)) E) E := by
  apply regularOn_condition _ _ IsGaussian.memLp_two_id _ hE (measure_lt_top _ _)
  simpa only [gaussianLaw, multivariateGaussian_zero_one] using
    gaussianLaw_absolutelyContinuous (1 : Covariance d) Matrix.PosDef.one (0 : Space d)

theorem affineHistory_projection (h : Fin m → Space d) (c : Fin m → ℝ) :
    let V := Submodule.span ℝ (Set.range h)
    V.starProjection ⁻¹' affineHistory h c = affineHistory h c := by
  dsimp only
  let V := Submodule.span ℝ (Set.range h)
  have hi (i : Fin m) (x : Space d) :
      linear (h i) (V.starProjection x) = linear (h i) x := by
    have hm : h i ∈ V := Submodule.subset_span (Set.mem_range_self i)
    change ⟪h i, V.starProjection x⟫ = ⟪h i, x⟫
    rw [← V.inner_starProjection_left_eq_right,
      V.starProjection_eq_self_iff.mpr hm]
  ext x
  change (∀ i, 0 < c i + linear (h i) (V.starProjection x)) ↔ _
  simp_rw [hi]
  rfl

/-- Affine transport discharges every standard-Gaussian input of the split argument. -/
theorem affine_positive_split_of_standard
    (hStandard : StandardSplitTheorem) : AffineSplitTheorem := by
  intro d m S _hS γ h c a z q hE hC hzero hpos
  let w := whiteningMap S γ
  let h' : Fin m → Space d := fun i => whiteningCoeff S (h i)
  let c' : Fin m → ℝ := fun i => c i + linear (h i) γ
  let A := affineHistory h' c'
  let V := Submodule.span ℝ (Set.range h')
  let ρ := stdGaussian (Space d)
  let C := A ∩ {x | 0 < (q + linear z γ) + linear (whiteningCoeff S z) x}
  have hw : Measurable w := (whiteningMap_continuous S γ).measurable
  have hA : MeasurableSet A := affineHistory_measurable h' c'
  have hpreE : w ⁻¹' affineHistory h c = A := by
    ext x
    simp only [Set.mem_preimage, affineHistory, Set.mem_ofPred_eq, w,
      linear_whiteningMap, A, h', c', add_assoc]
  have hpreC : w ⁻¹' (affineHistory h c ∩ {x | 0 < q + linear z x}) = C := by
    rw [Set.preimage_inter, hpreE]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      w, linear_whiteningMap, C, add_assoc]
  have hAmass : 0 < ρ A := by
    rw [← hpreE, ← Measure.map_apply hw (affineHistory_measurable h c)]
    exact hE
  have hCmeas : MeasurableSet (affineHistory h c ∩ {x | 0 < q + linear z x}) :=
    (affineHistory_measurable h c).inter
      (isOpen_lt continuous_const (continuous_const.add
        (continuous_const.inner continuous_id))).measurableSet
  have hCmass : 0 < ρ C := by
    rw [← hpreC, ← Measure.map_apply hw hCmeas]
    exact hC
  have hregA := stdGaussian_condition_regular A hAmass
  have hregC := stdGaussian_condition_regular C hCmass
  let : IsProbabilityMeasure (condition ρ A) := hregA.probability
  let : IsProbabilityMeasure (condition ρ C) := hregC.probability
  have hmapA : condition (gaussianLaw S γ) (affineHistory h c) =
      (condition ρ A).map w := by
    rw [← whiteningMap_law S γ, condition_map_preimage _ _ hw _
      (affineHistory_measurable h c), hpreE]
  have hmapC : condition (gaussianLaw S γ)
      (affineHistory h c ∩ {x | 0 < q + linear z x}) =
      (condition ρ C).map w := by
    rw [← whiteningMap_law S γ, condition_map_preimage _ _ hw _ hCmeas, hpreC]
  have hcov (b : Space d) :
      covarianceBilin (condition (gaussianLaw S γ) (affineHistory h c)) a b =
        covarianceBilin (condition ρ A) (whiteningCoeff S a) (whiteningCoeff S b) := by
    rw [hmapA]
    exact covarianceBilin_whiteningMap _ hregA.memLp_two S γ a b
  have hker : V ≤ LinearMap.ker
      (covarianceBilin (condition ρ A) (whiteningCoeff S a)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    change covarianceBilin (condition ρ A) (whiteningCoeff S a) (h' i) = 0
    exact (hcov (h i)).symm.trans (hzero i)
  have hproj : V.starProjection ⁻¹' A = A := affineHistory_projection h' c'
  have hstd := hStandard d V A hA
  dsimp only at hstd
  rw [hproj] at hstd
  have hinc := hstd hAmass.ne'
    (fun v hv => covarianceBilin_self_pos _ hregA.memLp_two
      hregA.absolutelyContinuous v hv)
    (whiteningCoeff S a) (whiteningCoeff S z) (q + linear z γ)
    (fun v hv => hker hv) ((hcov z) ▸ hpos)
  change 0 < (∫ x, linear (whiteningCoeff S a) x ∂condition ρ C) -
    (∫ x, linear (whiteningCoeff S a) x ∂condition ρ A) at hinc
  rw [hmapC, hmapA, integral_linear_whiteningMap _ hregC.memLp_two S γ a,
    integral_linear_whiteningMap _ hregA.memLp_two S γ a]
  linarith

/-- Closed Gaussian positive split for affine histories and actual multivariate laws. -/
theorem affine_positive_split : AffineSplitTheorem :=
  affine_positive_split_of_standard standard_positive_split

end MajorityDynamics.Analysis.GaussianSplit
