import MajorityDynamics.Literature.Concentration.BinomialUpperTail

/-!
# The unreduced binomial Bennett exponent

For sparse graph discrepancy one must retain the logarithm in the Chernoff
exponent; the Bernstein simplification loses the entropy of unbalanced pairs.
This proof uses the same exact binomial MGF as the checked scalar Chernoff
theorem, before its final analytic simplification. Mathematical source:
Chernoff (1952), https://doi.org/10.1214/aoms/1177729330 .
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace MajorityDynamics.Literature.RandomGraph

lemma binomial_bennett (m : ℕ) (q : unitInterval)
    (hμ : 0 < (m : ℝ) * q) (t : ℝ) (ht : 0 ≤ t) :
    (binomial m q).real {k | (m : ℝ) * q + t ≤ (k : ℝ)} ≤
      Real.exp (-((m : ℝ) * q *
        ((1 + t / ((m : ℝ) * q)) * Real.log (1 + t / ((m : ℝ) * q)) -
          t / ((m : ℝ) * q)))) := by
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
      exact mul_le_mul_of_nonneg_left
        (Concentration.binomial_mgf_le m q (Real.log (1 + x))) (Real.exp_nonneg _)
    _ = Real.exp (-(μ * ((1 + x) * Real.log (1 + x) - x))) := by
      rw [← Real.exp_add, Real.exp_log h1]
      congr 1
      dsimp [x]
      field_simp
      ring

end MajorityDynamics.Literature.RandomGraph
