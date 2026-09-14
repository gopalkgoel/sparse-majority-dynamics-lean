import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-! # Superpolynomial decay of a Gaussian in the logarithm -/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Analysis

/-- Explicit eventual power bounds, including any fixed prefactor. -/
theorem log_tail_eventually_le_power (A C a : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      A * Real.exp (-((Real.log n) ^ 2) / C) ≤ (n : ℝ) ^ (-a) := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hn
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (C * (|a| + |Real.log A|))] with n hn1 hl1 hl
  simp only [Function.comp_apply] at hl1 hl
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hl0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hdom : Real.log A + a * Real.log n ≤ (Real.log n) ^ 2 / C := by
    apply (le_div_iff₀ hC).mpr
    have h1 := mul_le_mul_of_nonneg_right hl hl0
    have h2 := mul_le_mul_of_nonneg_right (le_abs_self a) hl0
    have h3 := mul_le_mul_of_nonneg_left hl1 (abs_nonneg (Real.log A))
    have h4 := le_abs_self (Real.log A)
    nlinarith [mul_le_mul_of_nonneg_left h2 hC.le,
      mul_le_mul_of_nonneg_left h3 hC.le, mul_le_mul_of_nonneg_left h4 hC.le]
  rw [← Real.exp_log hA, ← Real.exp_add, Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith

end MajorityDynamics.Analysis
