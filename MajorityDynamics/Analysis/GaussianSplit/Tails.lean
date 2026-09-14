import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

/-!
# Strict positivity of centered Gaussian tails

These are the scalar and product-measure facts used in Step 4 of the proof of
`thm:coherence` in `latest/main.tex`. Thresholds may depend measurably on the
history; no bound or moment assumption on the threshold is required.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MajorityDynamics.Analysis.GaussianSplit

/-- Every finite upper truncation of a nondegenerate centered normal has a
strictly positive first moment. -/
theorem gaussian_tail_integral_pos (v : ℝ≥0) (hv : v ≠ 0) (u : ℝ) :
    0 < ∫ y in Ioi u, y ∂gaussianReal 0 v := by
  let : Measure.IsOpenPosMeasure (gaussianReal 0 v) :=
    (gaussianReal_absolutelyContinuous' 0 hv).isOpenPosMeasure
  have hi : Integrable (fun y : ℝ => y) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  by_cases hu : 0 ≤ u
  · refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi.restrict).2 ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).2
        (ae_of_all _ (fun y hy => le_trans hu hy.le))
    · have heq : Function.support (fun y : ℝ => y) ∩ Ioi u = Ioi u := by
        ext y
        simp only [mem_inter_iff, Function.mem_support, mem_Ioi, ne_eq]
        exact ⟨And.right, fun hy => ⟨ne_of_gt (lt_of_le_of_lt hu hy), hy⟩⟩
      rw [heq]
      exact isOpen_Ioi.measure_pos _ nonempty_Ioi
  · have hun : u < 0 := lt_of_not_ge hu
    have hn : 0 < ∫ y in Iic u, -y ∂gaussianReal 0 v := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi.neg.restrict).2 ?_
      · exact (ae_restrict_iff' measurableSet_Iic).2
          (ae_of_all _ (fun y hy => neg_nonneg.mpr (le_trans hy hun.le)))
      · have heq : Function.support (fun y : ℝ => -y) ∩ Iic u = Iic u := by
          ext y
          simp only [mem_inter_iff, Function.mem_support, mem_Iic, neg_ne_zero]
          exact ⟨And.right, fun hy => ⟨ne_of_lt (lt_of_le_of_lt hy hun), hy⟩⟩
        change 0 < (gaussianReal 0 v) (Function.support (fun y : ℝ => -y) ∩ Iic u)
        rw [heq]
        exact lt_of_lt_of_le (isOpen_Iio.measure_pos _
          nonempty_Iio)
          (measure_mono Iio_subset_Iic_self)
    have hsum := integral_add_compl (μ := gaussianReal 0 v) (s := Iic u)
      measurableSet_Iic hi
    simp only [compl_Iic, integral_id_gaussianReal] at hsum
    rw [integral_neg] at hn
    linarith

variable {H : Type*} [MeasurableSpace H]

/-- A history event followed by a threshold comparison with the residual. -/
def thresholdEvent (E : Set H) (U : H → ℝ) : Set (H × ℝ) :=
  {p | p.1 ∈ E ∧ U p.1 < p.2}

theorem measurableSet_thresholdEvent {E : Set H} {U : H → ℝ}
    (hE : MeasurableSet E) (hU : Measurable U) :
    MeasurableSet (thresholdEvent E U) :=
  (hE.preimage measurable_fst).inter (measurableSet_lt (hU.comp measurable_fst) measurable_snd)

/-- Integrating over an independent Gaussian residual leaves the positive scalar
tail function on the history space. -/
theorem gaussian_threshold_integral (η : Measure H) [IsFiniteMeasure η]
    (v : ℝ≥0) {E : Set H} {U : H → ℝ}
    (hE : MeasurableSet E) (hU : Measurable U) :
    (∫ p in thresholdEvent E U, p.2 ∂η.prod (gaussianReal 0 v)) =
      ∫ h in E, (∫ y in Ioi (U h), y ∂gaussianReal 0 v) ∂η := by
  have hi : Integrable (fun y : ℝ => y) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  rw [← integral_indicator (measurableSet_thresholdEvent hE hU),
    integral_prod _ ((hi.comp_snd η).indicator (measurableSet_thresholdEvent hE hU)),
    ← integral_indicator hE]
  apply integral_congr_ae
  filter_upwards with h
  by_cases hh : h ∈ E
  · rw [Set.indicator_of_mem hh, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with y
    simp [Set.indicator, thresholdEvent, hh]
  · simp [thresholdEvent, hh]

/-- Positive-mass history events preserve strict positivity of a centered
Gaussian residual above an arbitrary measurable history-dependent threshold. -/
theorem gaussian_threshold_integral_pos (η : Measure H) [IsFiniteMeasure η]
    (v : ℝ≥0) (hv : v ≠ 0) {E : Set H} {U : H → ℝ}
    (hE : MeasurableSet E) (hEp : 0 < η E) (hU : Measurable U) :
    0 < ∫ p in thresholdEvent E U, p.2 ∂η.prod (gaussianReal 0 v) := by
  have hi : Integrable (fun y : ℝ => y) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  let f : H × ℝ → ℝ := (thresholdEvent E U).indicator (fun p => p.2)
  have hfi : Integrable f (η.prod (gaussianReal 0 v)) :=
    (hi.comp_snd η).indicator (measurableSet_thresholdEvent hE hU)
  have hinner (h : H) : (∫ y, f (h, y) ∂gaussianReal 0 v) =
      E.indicator (fun h => ∫ y in Ioi (U h), y ∂gaussianReal 0 v) h := by
    by_cases hh : h ∈ E
    · rw [Set.indicator_of_mem hh, ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with y
      simp [Set.indicator, f, thresholdEvent, hh]
    · simp [f, thresholdEvent, hh]
  rw [← integral_indicator (measurableSet_thresholdEvent hE hU)]
  change 0 < ∫ p, f p ∂η.prod (gaussianReal 0 v)
  rw [integral_prod _ hfi]
  refine (integral_pos_iff_support_of_nonneg ?_ hfi.integral_prod_left).2 ?_
  · intro h
    change 0 ≤ ∫ y, f (h, y) ∂gaussianReal 0 v
    rw [hinner]
    exact Set.indicator_nonneg (fun h _ => (gaussian_tail_integral_pos v hv (U h)).le) h
  · have hs : Function.support (fun h => ∫ y, f (h, y) ∂gaussianReal 0 v) = E := by
      ext h
      rw [Function.mem_support, hinner]
      by_cases hh : h ∈ E
      · simp [hh, ne_of_gt (gaussian_tail_integral_pos v hv (U h))]
      · simp [hh]
    rwa [hs]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The product-law positivity statement pulled back to jointly independent
random variables on the original probability space. -/
theorem indep_gaussian_threshold_integral_pos (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (Z : Ω → H) (Y : Ω → ℝ) (hZ : Measurable Z) (hY : Measurable Y)
    (hZY : IndepFun Z Y ρ) (v : ℝ≥0) (hv : v ≠ 0)
    (hLaw : ρ.map Y = gaussianReal 0 v) {E : Set H} {U : H → ℝ}
    (hE : MeasurableSet E) (hEp : 0 < ρ (Z ⁻¹' E)) (hU : Measurable U) :
    0 < ∫ x in {x | Z x ∈ E ∧ U (Z x) < Y x}, Y x ∂ρ := by
  have hmap : ρ.map (fun x => (Z x, Y x)) = (ρ.map Z).prod (gaussianReal 0 v) := by
    rw [hZY.map_prod_eq_prod_map_map hZ.aemeasurable hY.aemeasurable, hLaw]
  have hp := gaussian_threshold_integral_pos (ρ.map Z) v hv hE
    (by rwa [Measure.map_apply hZ hE]) hU
  rw [← hmap, setIntegral_map (measurableSet_thresholdEvent hE hU)
    measurable_snd.aestronglyMeasurable (hZ.prodMk hY).aemeasurable] at hp
  exact hp

/-- Normalizing a positive, finite-mass truncated first moment preserves its
strict sign. This also establishes the conditioning event has nonzero mass. -/
theorem conditional_integral_pos_of_setIntegral_pos (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (f : Ω → ℝ) (C : Set Ω) (hp : 0 < ∫ x in C, f x ∂ρ) :
    0 < ∫ x, f x ∂ProbabilityTheory.cond ρ C := by
  have hC : ρ C ≠ 0 := by
    intro hzero
    rw [Measure.restrict_zero_set hzero, integral_zero_measure] at hp
    exact (lt_irrefl 0) hp
  change 0 < ∫ x, f x ∂(ρ C)⁻¹ • ρ.restrict C
  rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  exact mul_pos (inv_pos.mpr (ENNReal.toReal_pos hC (measure_ne_top _ _))) hp

/-- The positive conditional mean of the Gaussian residual used by coherence. -/
theorem indep_gaussian_threshold_conditional_mean_pos (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (Z : Ω → H) (Y : Ω → ℝ) (hZ : Measurable Z) (hY : Measurable Y)
    (hZY : IndepFun Z Y ρ) (v : ℝ≥0) (hv : v ≠ 0)
    (hLaw : ρ.map Y = gaussianReal 0 v) {E : Set H} {U : H → ℝ}
    (hE : MeasurableSet E) (hEp : 0 < ρ (Z ⁻¹' E)) (hU : Measurable U) :
    0 < ∫ x, Y x ∂ProbabilityTheory.cond ρ {x | Z x ∈ E ∧ U (Z x) < Y x} :=
  conditional_integral_pos_of_setIntegral_pos ρ Y _
    (indep_gaussian_threshold_integral_pos ρ Z Y hZ hY hZY v hv hLaw hE hEp hU)

end MajorityDynamics.Analysis.GaussianSplit
