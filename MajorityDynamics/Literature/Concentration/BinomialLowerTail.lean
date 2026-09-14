import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Binomial exponential moments and lower tails

The concentration bound is the lower-tail half of CKLT21, Lemma 2.1(ii):
https://arxiv.org/abs/2105.12709v1 . The proof below is the exponential-moment
argument for the actual Mathlib binomial measure. It does not assume a
concentration theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace MajorityDynamics.Literature.Concentration

lemma binomial_mgf (m : ℕ) (q : unitInterval) (a : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (binomial m q) a =
      ((q : ℝ) * Real.exp a + (1 - q)) ^ m := by
  rw [mgf, integral_binomial, add_pow]
  rw [show Finset.Iic m = Finset.range (m + 1) by ext k; simp]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [smul_eq_mul, mul_pow]
  rw [show a * (k : ℝ) = (k : ℝ) * a by ring, Real.exp_nat_mul]
  ring

lemma binomial_mgf_le (m : ℕ) (q : unitInterval) (a : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (binomial m q) a ≤
      Real.exp ((m : ℝ) * q * (Real.exp a - 1)) := by
  rw [binomial_mgf]
  calc
    ((q : ℝ) * Real.exp a + (1 - q)) ^ m ≤
        (Real.exp ((q : ℝ) * (Real.exp a - 1))) ^ m := by
      apply pow_le_pow_left₀
      · exact add_nonneg (mul_nonneg q.property.1 (Real.exp_nonneg _))
          (sub_nonneg.mpr q.property.2)
      · nlinarith [Real.add_one_le_exp ((q : ℝ) * (Real.exp a - 1))]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma exp_neg_sub_one_add_le_sq {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a) - 1 + a ≤ a ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => x ^ 2 / 2 - Real.exp (-x) + 1 - x
  have hd (x : ℝ) : HasDerivAt f (x + Real.exp (-x) - 1) x := by
    dsimp [f]
    convert! ((((hasDerivAt_id x).pow 2).div_const 2).sub
      (((hasDerivAt_id x).neg).exp)).add_const 1 |>.sub (hasDerivAt_id x) using 1
    simp
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      linarith [Real.add_one_le_exp (-x)]
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) ha ha
  dsimp [f] at h
  simp only [neg_zero, Real.exp_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at h
  linarith

lemma binomial_lower_tail (m : ℕ) (q : unitInterval)
    (hμ : 0 < (m : ℝ) * q) (t : ℝ) (ht : 0 ≤ t) :
    (binomial m q).real {k | (k : ℝ) ≤ (m : ℝ) * q - t} ≤
      Real.exp (-(t ^ 2) / (2 * ((m : ℝ) * q))) := by
  let μ : ℝ := (m : ℝ) * q
  have hμ' : 0 < μ := hμ
  have h := measure_le_le_exp_mul_mgf (μ - t)
    (show -(t / μ) ≤ 0 from neg_nonpos.mpr (div_nonneg ht hμ'.le))
    (integrable_binomial (n := m) (p := q) (fun k : ℕ => Real.exp (-(t / μ) * k)))
  refine h.trans ?_
  calc
    Real.exp (-(-(t / μ)) * (μ - t)) *
        mgf (fun k : ℕ => (k : ℝ)) (binomial m q) (-(t / μ)) ≤
        Real.exp (-(-(t / μ)) * (μ - t)) *
          Real.exp (μ * (Real.exp (-(t / μ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (binomial_mgf_le m q (-(t / μ)))
        (Real.exp_nonneg _)
    _ = Real.exp ((t / μ) * (μ - t) + μ * (Real.exp (-(t / μ)) - 1)) := by
      rw [← Real.exp_add]; simp
    _ ≤ Real.exp (-(t ^ 2) / (2 * μ)) := by
      apply Real.exp_le_exp.mpr
      have hb := mul_le_mul_of_nonneg_left
        (exp_neg_sub_one_add_le_sq (show 0 ≤ t / μ by positivity)) hμ'.le
      have he : (t / μ) * (μ - t) + μ * (Real.exp (-(t / μ)) - 1) =
          μ * (Real.exp (-(t / μ)) - 1 + t / μ) - t ^ 2 / μ := by
        field_simp
        ring
      rw [he]
      calc
        _ ≤ μ * ((t / μ) ^ 2 / 2) - t ^ 2 / μ := sub_le_sub_right hb _
        _ = _ := by field_simp; ring

end MajorityDynamics.Literature.Concentration
