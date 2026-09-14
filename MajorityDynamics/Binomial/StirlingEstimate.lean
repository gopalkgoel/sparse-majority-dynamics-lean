import MajorityDynamics.Binomial.ApproximationStatements
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Quantitative Stirling input for A.2 point probabilities

Derives a global `1/(12n)` logarithmic remainder from Mathlib's checked
stepwise Robbins bound and Stirling limit. No external axiom is introduced.
-/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Binomial.Approximation

theorem log_stirling_error {n : ℕ} (hn : 0 < n) :
    |Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)| ≤ 1 / (12 * n) := by
  let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (k + 1)) - 1 / (12 * (k + 1))
  have hf : Monotone f := by
    apply monotone_nat_of_le_succ
    intro k
    have hs := Stirling.log_stirlingSeq_sdiff_le (k + 1)
    have hid : (1 : ℝ) / (12 * (k + 1)) - 1 / (12 * (k + 1 + 1)) =
        1 / (12 * (k + 1) * (k + 1 + 1)) := by
      field_simp
      ring
    dsimp [f]
    simp only [Nat.cast_add, Nat.cast_one] at hs ⊢
    linarith
  have hlim : Tendsto f atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    have hlog := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (tendsto_add_atTop_nat 1)).log (by positivity : Real.sqrt Real.pi ≠ 0)
    have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / (12 * (k + 1))) atTop (𝓝 0) := by
      simp only [one_div]
      apply tendsto_inv_atTop_zero.comp
      exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num)
    simpa [f] using hlog.sub hinv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hupper := hf.ge_of_tendsto hlim k
  have hlower := Real.log_le_log (Real.sqrt_pos.mpr Real.pi_pos)
    (Stirling.sqrt_pi_le_stirlingSeq (Nat.succ_ne_zero k))
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  dsimp [f] at hupper
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  linarith

def stirlingMain (n : ℕ) : ℝ :=
  Real.log (Real.sqrt Real.pi) + 1 / 2 * Real.log (2 * n) + n * Real.log (n / Real.exp 1)

theorem log_factorial_error {n : ℕ} (hn : 0 < n) :
    |Real.log (n.factorial : ℝ) - stirlingMain n| ≤ 1 / (12 * n) := by
  have h := log_stirling_error hn
  rw [Stirling.log_stirlingSeq_formula] at h
  convert h using 1
  dsimp [stirlingMain]
  congr 1
  ring

def binomialLogMain (m k : ℕ) (q : Probability) : ℝ :=
  stirlingMain m - stirlingMain k - stirlingMain (m - k) +
    k * Real.log (q : ℝ) + (m - k : ℕ) * Real.log (1 - (q : ℝ))

/-- A nonasymptotic logarithmic point bound for the actual binomial law.
The central-window Gaussian approximation still requires Taylor estimates. -/
theorem log_pointMass_error {m k : ℕ} (hk : 0 < k) (hkm : k < m) (q : Probability) :
    |Real.log (pointMass m k q) - binomialLogMain m k q| ≤
      1 / (12 * m) + 1 / (12 * k) + 1 / (12 * (m - k : ℕ)) := by
  have hm : 0 < m := hk.trans hkm
  have hr : 0 < m - k := Nat.sub_pos_of_lt hkm
  have hchoose : 0 < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkm.le
  have hq := q.property.1
  have hqc := sub_pos.mpr q.property.2
  have hlog : Real.log (pointMass m k q) = Real.log (m.factorial : ℝ) -
      Real.log (k.factorial : ℝ) - Real.log ((m - k).factorial : ℝ) +
      k * Real.log (q : ℝ) + (m - k : ℕ) * Real.log (1 - (q : ℝ)) := by
    rw [pointMass, ProbabilityTheory.binomial_real_singleton]
    change Real.log ((m.choose k : ℝ) * (q : ℝ) ^ k * (1 - (q : ℝ)) ^ (m - k)) = _
    rw [Real.log_mul (mul_pos hchoose (pow_pos hq _)).ne' (pow_pos hqc _).ne',
      Real.log_mul hchoose.ne' (pow_pos hq _).ne', Real.log_pow, Real.log_pow,
      Nat.cast_choose ℝ hkm.le, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hlog]
  have heq : Real.log (m.factorial : ℝ) - Real.log (k.factorial : ℝ) -
      Real.log ((m - k).factorial : ℝ) + k * Real.log (q : ℝ) +
      (m - k : ℕ) * Real.log (1 - (q : ℝ)) - binomialLogMain m k q =
      (Real.log (m.factorial : ℝ) - stirlingMain m) -
      (Real.log (k.factorial : ℝ) - stirlingMain k) -
      (Real.log ((m - k).factorial : ℝ) - stirlingMain (m - k)) := by
    dsimp [binomialLogMain]
    ring
  rw [heq]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add (log_factorial_error hm) (log_factorial_error hk)) (log_factorial_error hr))

/-- Convert the logarithmic estimate into a relative error for actual point
probabilities. This bound holds at every interior lattice point. -/
theorem pointMass_relative_error {m k : ℕ} (hk : 0 < k) (hkm : k < m) (q : Probability) :
    |pointMass m k q - Real.exp (binomialLogMain m k q)| ≤
      2 * (1 / (12 * m) + 1 / (12 * k) + 1 / (12 * (m - k : ℕ))) *
        Real.exp (binomialLogMain m k q) := by
  have hm : 0 < m := hk.trans hkm
  have hr : 0 < m - k := Nat.sub_pos_of_lt hkm
  have hbound (n : ℕ) (hn : 0 < n) : (1 : ℝ) / (12 * n) ≤ 1 / 12 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 12 * n)).mpr
    linarith
  have he := log_pointMass_error hk hkm q
  have hsmall : |Real.log (pointMass m k q) - binomialLogMain m k q| ≤ 1 := by
    linarith [hbound m hm, hbound k hk, hbound (m - k) hr]
  have hp : 0 < pointMass m k q := by
    rw [pointMass, ProbabilityTheory.binomial_real_singleton]
    have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm.le
    exact mul_pos (mul_pos hc (pow_pos q.property.1 _))
      (pow_pos (sub_pos.mpr q.property.2) _)
  have hid : pointMass m k q - Real.exp (binomialLogMain m k q) =
      (Real.exp (Real.log (pointMass m k q) - binomialLogMain m k q) - 1) *
        Real.exp (binomialLogMain m k q) := by
    rw [sub_mul, ← Real.exp_add, sub_add_cancel, Real.exp_log hp, one_mul]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (Real.abs_exp_sub_one_le hsmall).trans (mul_le_mul_of_nonneg_left he (by norm_num))

end MajorityDynamics.Binomial.Approximation
