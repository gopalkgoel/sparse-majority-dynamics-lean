import MajorityDynamics.Probability.ConditionedBinomialFourier.Characteristic
import MajorityDynamics.Probability.ConditionedBinomialFourier.GapScale

noncomputable section
open MeasureTheory

namespace MajorityDynamics.Probability.ConditionedBinomialFourier

/-- A literal probability-measure mixture transfers the component's Fourier gap. -/
theorem mixture_norm_gap {d : ℕ} (μ ν : Measure (Fin d → ℕ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {β u : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (t : Fin d → ℝ)
    (hgap : ‖chi μ t‖ ≤ 1-u) :
    ‖chi (ENNReal.ofReal β • μ + ENNReal.ofReal (1-β) • ν) t‖ ≤ 1-β*u := by
  rw [chi_mixture μ ν hβ0 hβ1]
  calc
    ‖(β : ℂ)*chi μ t + ((1-β : ℝ) : ℂ)*chi ν t‖ ≤
        ‖(β : ℂ)*chi μ t‖ + ‖((1-β : ℝ) : ℂ)*chi ν t‖ := norm_add_le _ _
    _ = β*‖chi μ t‖+(1-β)*‖chi ν t‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hβ0, abs_of_nonneg (sub_nonneg.mpr hβ1)]
    _ ≤ β*(1-u)+(1-β)*1 := add_le_add
      (mul_le_mul_of_nonneg_left hgap hβ0)
      (mul_le_mul_of_nonneg_left (chi_norm_le_one ν t) (sub_nonneg.mpr hβ1))
    _ = 1-β*u := by ring

/-- The actual iid centered-sum integral inherits exponential amplification. -/
theorem centeredChi_exp_of_gap {d : ℕ} (ρ : Measure (Fin d → ℕ))
    [IsProbabilityMeasure ρ] (m : ℕ) (t : Fin d → ℝ) {u : ℝ}
    (hgap : ‖chi ρ t‖ ≤ 1-u) :
    ‖centeredChi ρ m t‖ ≤ Real.exp (-u*(m : ℝ)) := by
  rw [centeredChi_norm_eq]
  exact pow_le_exp_of_gap m (norm_nonneg _) hgap

end MajorityDynamics.Probability.ConditionedBinomialFourier
