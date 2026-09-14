import MajorityDynamics.Binomial.GaussianWeights

/-! # The exact logit parameter stays close to the reference density -/

noncomputable section
namespace MajorityDynamics.Binomial.Approximation

theorem gaussian_logistic_formula (p : Probability) (t : ℝ) :
    (Idealized.logistic (logOdds p + t) : ℝ) =
      (p : ℝ) * Real.exp t / (1 - (p : ℝ) + (p : ℝ) * Real.exp t) := by
  have hp := p.property.1
  have hpc := sub_pos.mpr p.property.2
  have hden : 0 < 1 - (p : ℝ) + (p : ℝ) * Real.exp t := by positivity
  simp only [Idealized.logistic, Real.exp_add, Idealized.exp_logOdds]
  field_simp

theorem gaussian_logistic_error (p : Probability) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    |(Idealized.logistic (logOdds p + t) : ℝ) - p| ≤ 4 * (p : ℝ) * |t| ∧
      (Idealized.logistic (logOdds p + t) : ℝ) ≤ 2 * p := by
  have hp := p.property.1
  have hp1 := p.property.2
  have hpc := sub_pos.mpr hp1
  have he : |Real.exp t - 1| ≤ 2 * |t| := Real.abs_exp_sub_one_le (ht.trans (by norm_num))
  let den := 1 - (p : ℝ) + (p : ℝ) * Real.exp t
  have hd : 1 / 2 ≤ den := by
    have helo := (abs_le.mp he).1
    have hmul := mul_le_mul_of_nonneg_left helo hp.le
    dsimp [den]
    nlinarith [abs_nonneg t]
  have hd0 : 0 < den := by linarith
  have heq : (Idealized.logistic (logOdds p + t) : ℝ) - p =
      (p : ℝ) * (1 - (p : ℝ)) * (Real.exp t - 1) / den := by
    rw [gaussian_logistic_formula]
    dsimp [den]
    field_simp
    ring
  have herr : |(Idealized.logistic (logOdds p + t) : ℝ) - p| ≤ 4 * (p : ℝ) * |t| := by
    rw [heq, abs_div, abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hpc, abs_of_pos hd0]
    apply (div_le_iff₀ hd0).mpr
    have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hp.le hpc.le)
    have hpos : 0 ≤ (p : ℝ) * |t| := mul_nonneg hp.le (abs_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hd hpos]
  refine ⟨herr, ?_⟩
  have h := (abs_le.mp herr).2
  nlinarith

end MajorityDynamics.Binomial.Approximation
