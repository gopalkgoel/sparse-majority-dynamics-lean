import MajorityDynamics.Literature.Concentration.BinomialLowerTail
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Binomial upper tail with the Bernstein denominator

This is CKLT21, Lemma 2.1(i), https://arxiv.org/abs/2105.12709v1 .
The exponential-moment bound gives the Bennett exponent. The elementary
inequality below bounds that exponent by the stated Bernstein expression,
retaining the exact coefficient `2 / 3`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace MajorityDynamics.Literature.Concentration

lemma log_one_add_ge_rational {x : ℝ} (hx : 0 ≤ x) :
    3 * x * (x + 6) / (2 * (x + 3) ^ 2) ≤ Real.log (1 + x) := by
  let f : ℝ → ℝ := fun z => Real.log (1 + z) - 3 * z * (z + 6) / (2 * (z + 3) ^ 2)
  have hd (z : ℝ) (hz : 0 ≤ z) :
      HasDerivAt f (z ^ 2 * (z + 9) / ((1 + z) * (z + 3) ^ 3)) z := by
    have h1 : 1 + z ≠ 0 := by positivity
    have h3 : z + 3 ≠ 0 := by positivity
    dsimp [f]
    convert! (((hasDerivAt_id z).const_add 1).log h1).sub
      ((((hasDerivAt_id z).const_mul 3).mul ((hasDerivAt_id z).add_const 6)).div
        (((hasDerivAt_id z).add_const 3).pow 2 |>.const_mul 2)
        (by positivity : 2 * (z + 3) ^ 2 ≠ 0)) using 1
    simp only [id_eq, Pi.mul_apply, Pi.pow_apply]
    field_simp
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : 0 ≤ z := interior_subset hz
      rw [(hd z hz').deriv]
      positivity
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  simpa [f] using h

lemma bennett_lower_bound {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / (2 + 2 * x / 3) ≤ (1 + x) * Real.log (1 + x) - x := by
  let f : ℝ → ℝ := fun z => (1 + z) * Real.log (1 + z) - z -
    3 * z ^ 2 / (2 * (z + 3))
  have hd (z : ℝ) (hz : 0 ≤ z) : HasDerivAt f
      (Real.log (1 + z) - 3 * z * (z + 6) / (2 * (z + 3) ^ 2)) z := by
    have h1 : 1 + z ≠ 0 := by positivity
    have h3 : z + 3 ≠ 0 := by positivity
    dsimp [f]
    convert! ((((hasDerivAt_id z).const_add 1).mul
      (((hasDerivAt_id z).const_add 1).log h1)).sub (hasDerivAt_id z)).sub
      ((((hasDerivAt_id z).pow 2).const_mul 3).div
        (((hasDerivAt_id z).add_const 3).const_mul 2)
        (by positivity : 2 * (z + 3) ≠ 0)) using 1
    simp only [id_eq, Pi.pow_apply]
    field_simp
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : 0 ≤ z := interior_subset hz
      rw [(hd z hz').deriv]
      exact sub_nonneg.mpr (log_one_add_ge_rational hz')
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  dsimp [f] at h
  simp only [add_zero, Real.log_one, mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div] at h
  have he : x ^ 2 / (2 + 2 * x / 3) = 3 * x ^ 2 / (2 * (x + 3)) := by
    field_simp
    ring
  rw [he]
  linarith

lemma binomial_upper_tail (m : ℕ) (q : unitInterval)
    (hμ : 0 < (m : ℝ) * q) (t : ℝ) (ht : 0 ≤ t) :
    (binomial m q).real {k | (m : ℝ) * q + t ≤ (k : ℝ)} ≤
      Real.exp (-(t ^ 2) / (2 * ((m : ℝ) * q) + 2 * t / 3)) := by
  let μ : ℝ := (m : ℝ) * q
  have hμ' : 0 < μ := hμ
  let x : ℝ := t / μ
  have hx : 0 ≤ x := by positivity
  have h1 : 0 < 1 + x := by positivity
  have ha : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have h := measure_ge_le_exp_mul_mgf (μ + t) ha
    (integrable_binomial (n := m) (p := q)
      (fun k : ℕ => Real.exp (Real.log (1 + x) * k)))
  refine h.trans ?_
  calc
    Real.exp (-Real.log (1 + x) * (μ + t)) *
        mgf (fun k : ℕ => (k : ℝ)) (binomial m q) (Real.log (1 + x)) ≤
        Real.exp (-Real.log (1 + x) * (μ + t)) *
          Real.exp (μ * (Real.exp (Real.log (1 + x)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (binomial_mgf_le m q (Real.log (1 + x)))
        (Real.exp_nonneg _)
    _ = Real.exp (-(μ * ((1 + x) * Real.log (1 + x) - x))) := by
      rw [← Real.exp_add, Real.exp_log h1]
      congr 1
      dsimp [x]
      field_simp
      ring
    _ ≤ Real.exp (-(t ^ 2) / (2 * μ + 2 * t / 3)) := by
      apply Real.exp_le_exp.mpr
      calc
        -(μ * ((1 + x) * Real.log (1 + x) - x)) ≤
            -(μ * (x ^ 2 / (2 + 2 * x / 3))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left (bennett_lower_bound hx) hμ'.le)
        _ = _ := by
          dsimp [x]
          field_simp

end MajorityDynamics.Literature.Concentration
