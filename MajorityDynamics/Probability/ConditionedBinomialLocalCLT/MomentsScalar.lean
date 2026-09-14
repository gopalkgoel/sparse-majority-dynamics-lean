import MajorityDynamics.Binomial.ProductTruncation
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT

theorem real_exp_quadratic {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp t ≤ 1 + t + t ^ 2 := by
  have h := Complex.exp_bound_sq 0 (t : ℂ) (by simpa using ht)
  have he : Complex.exp (t : ℂ) - 1 - (t : ℂ) =
      ((Real.exp t - 1 - t : ℝ) : ℂ) := by simp
  simp only [zero_add, Complex.exp_zero, smul_eq_mul, mul_one, norm_one, one_mul,
    Complex.norm_real, Real.norm_eq_abs] at h
  rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  linarith [(le_abs_self (Real.exp t - 1 - t)).trans h]

theorem binomial_exp_integral (n : ℕ) (q : Binomial.Probability) (t : ℝ) :
    (∫ k, Real.exp (t * (k : ℝ)) ∂binomial n (Binomial.closedProbability q)) =
      (1 - (q : ℝ) + (q : ℝ) * Real.exp t) ^ n := by
  rw [integral_binomial, add_comm (1 - (q : ℝ)), add_pow]
  apply Finset.sum_congr (by ext k; simp)
  intro k _
  simp only [smul_eq_mul, Binomial.closedProbability]
  rw [mul_pow, ← Real.exp_nat_mul]
  ring

theorem binomial_centered_exp (n : ℕ) (q : Binomial.Probability) {t : ℝ}
    (ht : |t| ≤ 1) :
    (∫ k, Real.exp (t * ((k : ℝ) - n * (q : ℝ)))
      ∂binomial n (Binomial.closedProbability q)) ≤
        Real.exp ((n : ℝ) * (q : ℝ) * t ^ 2) := by
  have hbase : 0 ≤ 1 - (q : ℝ) + (q : ℝ) * Real.exp t := by
    exact add_nonneg (sub_nonneg.mpr q.property.2.le)
      (mul_nonneg q.property.1.le (Real.exp_pos _).le)
  have hstep : 1 - (q : ℝ) + (q : ℝ) * Real.exp t ≤
      Real.exp ((q : ℝ) * (t + t ^ 2)) := by
    have hmul := mul_le_mul_of_nonneg_left (real_exp_quadratic ht) q.property.1.le
    have he := Real.add_one_le_exp ((q : ℝ) * (t + t ^ 2))
    nlinarith
  have hpow := pow_le_pow_left₀ hbase hstep n
  have heq : (fun k : ℕ => Real.exp (t * ((k : ℝ) - n * (q : ℝ)))) =
      fun k : ℕ => Real.exp (-(t * n * (q : ℝ))) * Real.exp (t * (k : ℝ)) := by
    funext k
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, binomial_exp_integral]
  calc
    _ ≤ Real.exp (-(t * n * (q : ℝ))) *
        Real.exp ((q : ℝ) * (t + t ^ 2)) ^ n :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) * (q : ℝ) * t ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem abs_pow_le_exp_pair (x : ℝ) (k : ℕ) :
    |x| ^ k ≤ (k.factorial : ℝ) * (Real.exp x + Real.exp (-x)) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
  have hk : (0 : ℝ) < k.factorial := by positivity
  have h' := (div_le_iff₀ hk).mp h
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at h' ⊢
    nlinarith [Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)] at h' ⊢
    nlinarith [Real.exp_pos x]

theorem binomial_scaled_moment (n : ℕ) (q : Binomial.Probability)
    (s : ℝ) (hs : 1 ≤ s) (hmean : (n : ℝ) * (q : ℝ) ≤ s ^ 2) (k : ℕ) :
    (∫ x, |((x : ℝ) - n * (q : ℝ)) / s| ^ k
      ∂binomial n (Binomial.closedProbability q)) ≤
        2 * (k.factorial : ℝ) * Real.exp 1 := by
  have hs0 : 0 < s := by linarith
  have ht : |s⁻¹| ≤ 1 := by rw [abs_of_pos (inv_pos.mpr hs0)]; exact inv_le_one_of_one_le₀ hs
  have hplus := binomial_centered_exp n q ht
  have hminus := binomial_centered_exp n q (t := -s⁻¹) (by simpa using ht)
  have hp : (n : ℝ) * (q : ℝ) * s⁻¹ ^ 2 ≤ 1 := by
    calc
      _ ≤ s ^ 2 * s⁻¹ ^ 2 := mul_le_mul_of_nonneg_right hmean (sq_nonneg _)
      _ = 1 := by field_simp
  have hm : (n : ℝ) * (q : ℝ) * (-s⁻¹) ^ 2 ≤ 1 := by simpa using hp
  have hplus' := hplus.trans (Real.exp_le_exp.mpr hp)
  have hminus' := hminus.trans (Real.exp_le_exp.mpr hm)
  calc
    _ ≤ ∫ x, (k.factorial : ℝ) *
        (Real.exp (((x : ℝ) - n * (q : ℝ)) / s) +
          Real.exp (-(((x : ℝ) - n * (q : ℝ)) / s)))
          ∂binomial n (Binomial.closedProbability q) :=
      integral_mono (integrable_binomial _) (integrable_binomial _)
        (fun x => abs_pow_le_exp_pair _ _)
    _ = (k.factorial : ℝ) *
        ((∫ x, Real.exp (s⁻¹ * ((x : ℝ) - n * (q : ℝ)))
          ∂binomial n (Binomial.closedProbability q)) +
         (∫ x, Real.exp (-s⁻¹ * ((x : ℝ) - n * (q : ℝ)))
          ∂binomial n (Binomial.closedProbability q))) := by
      rw [integral_const_mul, integral_add (integrable_binomial _) (integrable_binomial _)]
      congr 2 <;> apply integral_congr_ae <;> filter_upwards [] with x <;>
        congr 1 <;> simp [div_eq_mul_inv, mul_comm]
    _ ≤ 2 * (k.factorial : ℝ) * Real.exp 1 := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hplus' hminus')
        (show (0 : ℝ) ≤ k.factorial by positivity)
      nlinarith

theorem binomial_absolute_moment (n : ℕ) (q : Binomial.Probability)
    (s : ℝ) (hs : 1 ≤ s) (hmean : (n : ℝ) * (q : ℝ) ≤ s ^ 2) (k : ℕ) :
    (∫ x, |(x : ℝ) - n * (q : ℝ)| ^ k
      ∂binomial n (Binomial.closedProbability q)) ≤
        (2 * (k.factorial : ℝ) * Real.exp 1) * s ^ k := by
  have hs0 : 0 < s := by linarith
  have heq : (fun x : ℕ => |(x : ℝ) - n * (q : ℝ)| ^ k) =
      fun x : ℕ => s ^ k * |((x : ℝ) - n * (q : ℝ)) / s| ^ k := by
    funext x
    rw [abs_div, abs_of_pos hs0, div_pow]
    field_simp
  rw [heq, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (binomial_scaled_moment n q s hs hmean k)
    (pow_nonneg hs0.le k)
  nlinarith

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
