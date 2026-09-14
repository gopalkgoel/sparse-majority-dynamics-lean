import MajorityDynamics.Analysis.GaussianSplit.Tails
import MajorityDynamics.Analysis.GaussianSplit.Conditioning

/-!
# Conditional means after Gaussian residual decomposition

This is Step 4 of `thm:coherence`: a positive multiple of an independent
centered Gaussian residual has positive mean after the upper-threshold split,
while the remaining independent centered residual has zero mean on both events.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MajorityDynamics.Analysis.GaussianSplit

variable {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]

/-- The strict increase in mean after the upper child event, given the two
independent residuals supplied by Gaussian orthogonal projection. -/
theorem residual_mean_increase (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (Z : Ω → H) (X Y : Ω → ℝ)
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hXlp : MemLp X 2 ρ) (hYlp : MemLp Y 2 ρ)
    (hXmean : ∫ x, X x ∂ρ = 0)
    (hXind : IndepFun X (fun x => (Y x, Z x)) ρ)
    (hYind : IndepFun Z Y ρ)
    (v : ℝ≥0) (hv : v ≠ 0) (hYlaw : ρ.map Y = gaussianReal 0 v)
    {E : Set H} {U : H → ℝ} (hE : MeasurableSet E)
    (hEp : ρ (Z ⁻¹' E) ≠ 0) (hU : Measurable U)
    (c α : ℝ) (hα : 0 < α) :
    0 < (∫ x, c + α * Y x + X x
      ∂cond ρ {x | Z x ∈ E ∧ U (Z x) < Y x}) -
      ∫ x, c + α * Y x + X x ∂cond ρ (Z ⁻¹' E) := by
  let C : Set Ω := {x | Z x ∈ E ∧ U (Z x) < Y x}
  have htail := indep_gaussian_threshold_integral_pos ρ Z Y hZ hY hYind
    v hv hYlaw hE hEp.bot_lt hU
  have hCp : ρ C ≠ 0 := by
    intro hzero
    change 0 < ∫ x in C, Y x ∂ρ at htail
    rw [Measure.restrict_zero_set hzero, integral_zero_measure] at htail
    exact (lt_irrefl 0) htail
  let : IsProbabilityMeasure (cond ρ C) := cond_isProbabilityMeasure hCp
  let : IsProbabilityMeasure (cond ρ (Z ⁻¹' E)) := cond_isProbabilityMeasure hEp
  have hYpos : 0 < ∫ x, Y x ∂cond ρ C :=
    indep_gaussian_threshold_conditional_mean_pos ρ Z Y hZ hY hYind
      v hv hYlaw hE hEp.bot_lt hU
  have hXC : ∫ x, X x ∂cond ρ C = 0 := by
    let G : Set (ℝ × H) := {p | p.2 ∈ E ∧ U p.2 < p.1}
    have hG : MeasurableSet G := (hE.preimage measurable_snd).inter
      (measurableSet_lt (hU.comp measurable_snd) measurable_fst)
    exact integral_cond_preimage_eq_zero_of_indepFun hXind hX (hY.prodMk hZ)
      hG hCp hXmean
  have hXE : ∫ x, X x ∂cond ρ (Z ⁻¹' E) = 0 :=
    integral_cond_preimage_eq_zero_of_indepFun
      (hXind.comp measurable_id measurable_snd) hX hZ hE hEp hXmean
  have hYmean : ∫ x, Y x ∂ρ = 0 := by
    rw [← integral_map (f := fun y : ℝ => y) hY.aemeasurable
      measurable_id.aestronglyMeasurable, hYlaw]
    exact integral_id_gaussianReal
  have hYE : ∫ x, Y x ∂cond ρ (Z ⁻¹' E) = 0 :=
    integral_cond_preimage_eq_zero_of_indepFun hYind.symm hY hZ hE hEp hYmean
  have hXiC : Integrable X (cond ρ C) := (memLp_cond hXlp hCp).integrable (by norm_num)
  have hYiC : Integrable Y (cond ρ C) := (memLp_cond hYlp hCp).integrable (by norm_num)
  have hXiE : Integrable X (cond ρ (Z ⁻¹' E)) :=
    (memLp_cond hXlp hEp).integrable (by norm_num)
  have hYiE : Integrable Y (cond ρ (Z ⁻¹' E)) :=
    (memLp_cond hYlp hEp).integrable (by norm_num)
  have hmeanC : (∫ x, c + α * Y x + X x ∂cond ρ C) =
      c + α * ∫ x, Y x ∂cond ρ C := by
    rw [integral_add (f := fun x => c + α * Y x) (g := X)
      ((integrable_const c).add (hYiC.const_mul α)) hXiC,
      integral_add (f := fun _ => c) (g := fun x => α * Y x)
        (integrable_const c) (hYiC.const_mul α), integral_const_mul, hXC]
    simp
  have hmeanE : (∫ x, c + α * Y x + X x ∂cond ρ (Z ⁻¹' E)) = c := by
    rw [integral_add (f := fun x => c + α * Y x) (g := X)
      ((integrable_const c).add (hYiE.const_mul α)) hXiE,
      integral_add (f := fun _ => c) (g := fun x => α * Y x)
        (integrable_const c) (hYiE.const_mul α), integral_const_mul, hXE, hYE]
    simp
  change 0 < (∫ x, c + α * Y x + X x ∂cond ρ C) -
    ∫ x, c + α * Y x + X x ∂cond ρ (Z ⁻¹' E)
  rw [hmeanC, hmeanE, add_sub_cancel_left]
  exact mul_pos hα hYpos

end MajorityDynamics.Analysis.GaussianSplit
