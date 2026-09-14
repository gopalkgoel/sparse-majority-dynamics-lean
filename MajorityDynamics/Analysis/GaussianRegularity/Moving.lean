import MajorityDynamics.Analysis.GaussianRegularity.Threshold
import MajorityDynamics.Analysis.GaussianRegularity.Conditional
import MajorityDynamics.Analysis.GaussianRegularity.Domain
import MajorityDynamics.Analysis.ConditionalGaussian.GaussianDensity

/-! # Moving moments from fixed-region regularity

This file proves the exact polynomial translation formulas, and transfers
fixed-region regularity to the original varying thresholds. The fixed-region
analytic estimate is an explicit intermediate hypothesis, never an axiom.
-/

noncomputable section
open MeasureTheory Set

namespace MajorityDynamics.Analysis.GaussianRegularity
open ConditionalGaussian
variable {d r : ℕ}

def shiftParameters (R : Space r →L[ℝ] Space d) (p : Parameters d r) : Parameters d r :=
  ((p.1.1 + R p.2, p.1.2), p.2)

def fixedMass (M : Matrix (Fin r) (Fin d) ℝ) (p : Parameters d r) : ℝ :=
  ∫ _x in event M 0, (1 : ℝ) ∂law p

def fixedFirst (M : Matrix (Fin r) (Fin d) ℝ) (t : Fin d) (p : Parameters d r) : ℝ :=
  ∫ x in event M 0, x t ∂law p

def fixedSecond (M : Matrix (Fin r) (Fin d) ℝ) (t t' : Fin d)
    (p : Parameters d r) : ℝ := ∫ x in event M 0, x t * x t' ∂law p

/-- Every first and second coordinate moment is integrable on every region. -/
theorem integrableOn_law_coordinate (p : Parameters d r) (E : Set (Space d)) (t : Fin d) :
    IntegrableOn (fun x : Space d => x t) E (law p) := by
  exact ((gaussianLaw_memLp_two _ _).eval_piLp t).integrable (by norm_num) |>.integrableOn

theorem integrableOn_law_coordinate_mul (p : Parameters d r) (E : Set (Space d))
    (t t' : Fin d) : IntegrableOn (fun x : Space d => x t * x t') E (law p) := by
  exact ((gaussianLaw_memLp_two _ _).eval_piLp t).integrable_mul
    ((gaussianLaw_memLp_two _ _).eval_piLp t') |>.integrableOn

theorem mass_eq_shift (M : Matrix (Fin r) (Fin d) ℝ)
    (R : Space r →L[ℝ] Space d)
    (hR : (rectangularCLM M).comp R = ContinuousLinearMap.id ℝ (Space r))
    (p : Parameters d r) : mass M p = fixedMass M (shiftParameters R p) :=
  mass_translate M R hR p

theorem firstMoment_eq_shift (M : Matrix (Fin r) (Fin d) ℝ)
    (R : Space r →L[ℝ] Space d)
    (hR : (rectangularCLM M).comp R = ContinuousLinearMap.id ℝ (Space r))
    (p : Parameters d r) (t : Fin d) :
    firstMoment M t p = fixedFirst M t (shiftParameters R p) -
      R p.2 t * fixedMass M (shiftParameters R p) := by
  let : IsProbabilityMeasure (law (shiftParameters R p)) := by
    unfold law gaussianLaw
    infer_instance
  rw [firstMoment_translate M R hR p t]
  change (∫ y in event M 0, y t - R p.2 t ∂law (shiftParameters R p)) = _
  rw [integral_sub (integrableOn_law_coordinate _ _ t) (integrable_const _)]
  simp [fixedFirst, fixedMass, integral_const, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem secondMoment_eq_shift (M : Matrix (Fin r) (Fin d) ℝ)
    (R : Space r →L[ℝ] Space d)
    (hR : (rectangularCLM M).comp R = ContinuousLinearMap.id ℝ (Space r))
    (p : Parameters d r) (t t' : Fin d) :
    secondMoment M t t' p = fixedSecond M t t' (shiftParameters R p) -
      R p.2 t * fixedFirst M t' (shiftParameters R p) -
      R p.2 t' * fixedFirst M t (shiftParameters R p) +
      (R p.2 t * R p.2 t') * fixedMass M (shiftParameters R p) := by
  let : IsProbabilityMeasure (law (shiftParameters R p)) := by
    unfold law gaussianLaw
    infer_instance
  rw [secondMoment_translate M R hR p t t']
  change (∫ y in event M 0, (y t - R p.2 t) * (y t' - R p.2 t')
    ∂law (shiftParameters R p)) = _
  have hfirst := integrableOn_law_coordinate (shiftParameters R p) (event M 0)
  have hsecond := integrableOn_law_coordinate_mul (shiftParameters R p) (event M 0) t t'
  calc
    _ = ∫ y in event M 0, y t * y t' - R p.2 t * y t' - R p.2 t' * y t +
        R p.2 t * R p.2 t' ∂law (shiftParameters R p) := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := by
      have hsub₁ := integral_sub hsecond ((hfirst t').const_mul (R p.2 t))
      have hsub₂ := integral_sub (hsecond.sub ((hfirst t').const_mul (R p.2 t)))
        ((hfirst t).const_mul (R p.2 t'))
      have hadd := integral_add ((hsecond.sub ((hfirst t').const_mul (R p.2 t))).sub
        ((hfirst t).const_mul (R p.2 t'))) (integrable_const (R p.2 t * R p.2 t'))
      simp only [Pi.sub_apply] at hsub₁ hsub₂ hadd
      rw [hadd, hsub₂, hsub₁]
      simp only [fixedSecond, fixedFirst, fixedMass, integral_const_mul, integral_const,
        smul_eq_mul, mul_one]
      ring

/-- The remaining analytic input concerns a fixed integration region only. -/
structure FixedRawRegularity (M : Matrix (Fin r) (Fin d) ℝ) : Prop where
  mass : LocallyLipschitzOn {p | positiveVariance p} (fixedMass M)
  first : ∀ t, LocallyLipschitzOn {p | positiveVariance p} (fixedFirst M t)
  second : ∀ t t', LocallyLipschitzOn {p | positiveVariance p} (fixedSecond M t t')

private theorem locallyLipschitzOn_smooth_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : LocallyLipschitzOn U f) (g : E → E)
    (hg : ContDiff ℝ 1 g) (hmaps : MapsTo g U U) :
    LocallyLipschitzOn U (fun x => f (g x)) := by
  intro x hx
  obtain ⟨K, V, hV, hfV⟩ := hf (hmaps hx)
  rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds (hmaps hx))] at hV
  obtain ⟨K', W, hW, hgW⟩ := hg.locallyLipschitz x
  refine ⟨K * K', W ∩ g ⁻¹' V, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds
      (Filter.inter_mem hW (hg.continuous.continuousAt.preimage_mem_nhds hV))
  · exact hfV.comp (hgW.mono inter_subset_left)
      ((mapsTo_preimage _ _).mono_left inter_subset_right)

/-- All three raw moving-event families inherit the fixed-region estimates. -/
theorem moving_raw_regular (M : Matrix (Fin r) (Fin d) ℝ) (hM : M.rank = r)
    (hfixed : FixedRawRegularity M) :
    LocallyLipschitzOn {p | positiveVariance p} (mass M) ∧
    (∀ t, LocallyLipschitzOn {p | positiveVariance p} (firstMoment M t)) ∧
    (∀ t t', LocallyLipschitzOn {p | positiveVariance p} (secondMoment M t t')) := by
  obtain ⟨R, hR⟩ := exists_matrix_threshold_rightInverse M hM
  have hshift : ContDiff ℝ 1 (shiftParameters R) := by unfold shiftParameters; fun_prop
  have hmaps : MapsTo (shiftParameters R) {p | positiveVariance p}
      {p | positiveVariance p} := fun _ hp => hp
  have hm := locallyLipschitzOn_smooth_comp (isOpen_positiveVariance d r)
    hfixed.mass _ hshift hmaps
  have hf := fun t => locallyLipschitzOn_smooth_comp (isOpen_positiveVariance d r)
    (hfixed.first t) _ hshift hmaps
  have hs := fun t t' => locallyLipschitzOn_smooth_comp (isOpen_positiveVariance d r)
    (hfixed.second t t') _ hshift hmaps
  have hc : ∀ t : Fin d, LocallyLipschitzOn {p : Parameters d r | positiveVariance p}
      (fun p => R p.2 t) := fun t =>
    (show ContDiff ℝ 1 (fun p : Parameters d r => R p.2 t) by fun_prop).locallyLipschitz.locallyLipschitzOn
  have hmul {f g : Parameters d r → ℝ}
      (hf : LocallyLipschitzOn {p | positiveVariance p} f)
      (hg : LocallyLipschitzOn {p | positiveVariance p} g) :
      LocallyLipschitzOn {p | positiveVariance p} (fun p => f p * g p) :=
    locallyLipschitzOn_binary hf hg (fun z => z.1 * z.2)
      (fun _ _ => contDiffAt_fst.mul contDiffAt_snd)
  have hsub {f g : Parameters d r → ℝ}
      (hf : LocallyLipschitzOn {p | positiveVariance p} f)
      (hg : LocallyLipschitzOn {p | positiveVariance p} g) :
      LocallyLipschitzOn {p | positiveVariance p} (fun p => f p - g p) :=
    locallyLipschitzOn_binary hf hg (fun z => z.1 - z.2)
      (fun _ _ => contDiffAt_fst.sub contDiffAt_snd)
  refine ⟨?_, ?_, ?_⟩
  · change LocallyLipschitzOn _ (fun p => mass M p)
    simp_rw [mass_eq_shift M R hR]
    exact hm
  · intro t
    change LocallyLipschitzOn _ (fun p => firstMoment M t p)
    simp_rw [firstMoment_eq_shift M R hR]
    exact hsub (hf t) (hmul (hc t) hm)
  · intro t t'
    have h := locallyLipschitzOn_binary
      (hsub (hsub (hs t t') (hmul (hc t) (hf t'))) (hmul (hc t') (hf t)))
      (hmul (hmul (hc t) (hc t')) hm) (fun z => z.1 + z.2)
      (fun _ _ => contDiffAt_fst.add contDiffAt_snd)
    change LocallyLipschitzOn _ (fun p => secondMoment M t t' p)
    simp_rw [secondMoment_eq_shift M R hR]
    exact h

end MajorityDynamics.Analysis.GaussianRegularity
