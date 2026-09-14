import MajorityDynamics.Probability.ConditionedBinomialBox.Mixture
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace MajorityDynamics.Probability.ConditionedBinomialFourier
variable {d : ℕ}

def dot (t x : Fin d → ℝ) : ℝ := ∑ i, t i * x i

def phase (t x : Fin d → ℝ) : ℂ := Complex.exp (Complex.I * (dot t x : ℂ))

@[simp] theorem phase_norm (t x : Fin d → ℝ) : ‖phase t x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_sub (t x c : Fin d → ℝ) :
    phase t (x-c) = phase t (-c) * phase t x := by
  have h : dot t (x-c) = dot t (-c) + dot t x := by
    simp only [dot, Pi.sub_apply, Pi.neg_apply, mul_sub, mul_neg,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  simp only [phase, h, Complex.ofReal_add, mul_add, Complex.exp_add]

def chi (ρ : Measure (Fin d → ℕ)) (t : Fin d → ℝ) : ℂ :=
  ∫ x, phase t (fun i => (x i : ℝ)) ∂ρ

theorem phase_integrable (ρ : Measure (Fin d → ℕ)) [IsFiniteMeasure ρ]
    (t : Fin d → ℝ) : Integrable (fun x : Fin d → ℕ => phase t (fun i => (x i : ℝ))) ρ := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => (phase_norm _ _).le

theorem chi_norm_le_one (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (t : Fin d → ℝ) : ‖chi ρ t‖ ≤ 1 := by
  simpa [chi] using norm_integral_le_of_norm_le_const
    (μ := ρ) (Filter.Eventually.of_forall fun x : Fin d → ℕ => (phase_norm t (fun i => (x i : ℝ))).le)

def copyLaw (ρ : Measure (Fin d → ℕ)) (m : ℕ) : Measure (Fin m → Fin d → ℕ) :=
  Measure.pi (fun _ : Fin m => ρ)

instance copyLaw_probability (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ] (m : ℕ) :
    IsProbabilityMeasure (copyLaw ρ m) := by unfold copyLaw; infer_instance

def copySum {m : ℕ} (x : Fin m → Fin d → ℕ) : Fin d → ℝ := fun i => ∑ j, (x j i : ℝ)

def mean (ρ : Measure (Fin d → ℕ)) : Fin d → ℝ := fun i => ∫ x, (x i : ℝ) ∂ρ

def centeredChi (ρ : Measure (Fin d → ℕ)) (m : ℕ) (t : Fin d → ℝ) : ℂ :=
  ∫ x, phase t (copySum x - (fun i => (m:ℝ) * mean ρ i)) ∂copyLaw ρ m

theorem phase_copySum {m : ℕ} (t : Fin d → ℝ) (x : Fin m → Fin d → ℕ) :
    phase t (copySum x) = ∏ j, phase t (fun i => (x j i : ℝ)) := by
  have h : dot t (copySum x) = ∑ j, dot t (fun i => (x j i : ℝ)) := by
    simp only [dot, copySum, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [phase, h, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

theorem copySum_chi (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t : Fin d → ℝ) :
    (∫ x, phase t (copySum x) ∂copyLaw ρ m) = (chi ρ t)^m := by
  simp_rw [phase_copySum]
  simpa [copyLaw, chi] using integral_fintype_prod_eq_pow
    (ι := Fin m) (μ := ρ) (fun x : Fin d → ℕ => phase t (fun i => (x i : ℝ)))

theorem translated_copySum_chi (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t c : Fin d → ℝ) :
    (∫ x, phase t (copySum x-c) ∂copyLaw ρ m) = phase t (-c) * (chi ρ t)^m := by
  simp_rw [phase_sub]
  rw [integral_const_mul, copySum_chi]

theorem centeredChi_eq_phase_mul_pow (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t : Fin d → ℝ) :
    centeredChi ρ m t = phase t (-(fun i => (m:ℝ)*mean ρ i)) * (chi ρ t)^m :=
  translated_copySum_chi ρ m t _

theorem centeredChi_norm_eq (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t : Fin d → ℝ) : ‖centeredChi ρ m t‖ = ‖chi ρ t‖^m := by
  rw [centeredChi_eq_phase_mul_pow, norm_mul, phase_norm, one_mul, norm_pow]

theorem phase_continuous (x : Fin d → ℝ) : Continuous (fun t => phase t x) := by
  unfold phase dot
  fun_prop

theorem chi_continuous (ρ : Measure (Fin d → ℕ)) [IsFiniteMeasure ρ] : Continuous (chi ρ) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t
    exact (measurable_of_countable _).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall fun x => (phase_norm _ _).le
  · exact integrable_const 1
  · exact Filter.Eventually.of_forall fun x => phase_continuous _

theorem centeredChi_continuous (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) : Continuous (centeredChi ρ m) := by
  change Continuous (fun t => centeredChi ρ m t)
  simp_rw [centeredChi_eq_phase_mul_pow]
  exact (phase_continuous _).mul ((chi_continuous ρ).pow m)

theorem chi_mixture (μ ν : Measure (Fin d → ℕ)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (t : Fin d → ℝ) :
    chi (ENNReal.ofReal β • μ + ENNReal.ofReal (1-β) • ν) t =
      (β : ℂ) * chi μ t + ((1-β : ℝ) : ℂ) * chi ν t := by
  unfold chi
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure]
  · simp [ENNReal.toReal_ofReal hβ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hβ1),
      Complex.real_smul]
  · exact (phase_integrable μ t).smul_measure ENNReal.ofReal_ne_top
  · exact (phase_integrable ν t).smul_measure ENNReal.ofReal_ne_top

end MajorityDynamics.Probability.ConditionedBinomialFourier
