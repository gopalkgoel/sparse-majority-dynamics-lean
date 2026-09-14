import MajorityDynamics.Combinatorics.ZeroSumCounting.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The exponential-scale bookkeeping

With `x = √(np)`, `R = ⌊C x⌋₊`, `q = 2R+1 = |J|`, `m = n/2`, the combinatorial core gives
`|Z| ≥ (q^m/(2mR+1))²`. Here we show that this is at least `exp(-K n) x^n` for

  `K = K(T,C) = 5 + 3 log(2CT+1) + |log C|`

and every `n ≥ 1`, `0 ≤ x ≤ T n`. The chain is

  `(q^m/(2mR+1))² ≥ (Cx)^n / (n² (2Cx+1)³)`   (`q ≥ Cx`, `q ≥ 1`, `n ≤ 2m+1`, `2mR+1 ≤ n(2Cx+1)`)

and `n² (2Cx+1)³ ≤ (2CT+1)³ n⁵ ≤ (2CT+1)³ e^{5n} ≤ e^{Kn} C^n` (`n ≤ eⁿ`, and the base
`(2CT+1)³ e^{|log C|} C ≥ (2CT+1)³ ≥ 1`). The losses from the parity block, the fiber
denominator, and the constant `C` are all polynomial or `C^{±n}`, hence absorbed into `Kn`
for every `n ≥ 1`; no separate threshold is needed for this step.
-/

noncomputable section

namespace MajorityDynamics.Combinatorics.ZeroSumCounting

/-- The rate `K(T,C) = 5 + 3 log(2CT+1) + |log C|` of Lemma A.11. -/
def zeroSumRate (T C : ℝ) : ℝ := 5 + 3 * Real.log (2 * C * T + 1) + |Real.log C|

theorem zeroSumRate_pos {T C : ℝ} (hT : 1 < T) (hC : 0 < C) : 0 < zeroSumRate T C := by
  unfold zeroSumRate
  have h1 : 0 < Real.log (2 * C * T + 1) := Real.log_pos (by nlinarith)
  have h2 := abs_nonneg (Real.log C)
  linarith

theorem natCast_le_exp (n : ℕ) : (n : ℝ) ≤ Real.exp n := by
  linarith [Real.add_one_le_exp (n : ℝ)]

/-- `1 ≤ e^{|log C|} C`. -/
theorem one_le_exp_abs_log_mul {C : ℝ} (hC : 0 < C) : 1 ≤ Real.exp |Real.log C| * C := by
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (|Real.log C| + Real.log C) :=
        Real.exp_le_exp.mpr (by linarith [neg_abs_le (Real.log C)])
    _ = Real.exp |Real.log C| * C := by rw [Real.exp_add, Real.exp_log hC]

/-- `e^{K n} C^n = e^{5n} ((2CT+1)³ e^{|log C|} C)^n`. -/
theorem exp_rate_mul {T C : ℝ} (hT : 1 < T) (hC : 0 < C) (n : ℕ) :
    Real.exp (zeroSumRate T C * n) * C ^ n =
      Real.exp (5 * n) * ((2 * C * T + 1) ^ 3 * (Real.exp |Real.log C| * C)) ^ n := by
  have ha : 0 < 2 * C * T + 1 := by nlinarith
  have h1 : ((2 * C * T + 1) ^ 3) ^ n = Real.exp ((n : ℝ) * (3 * Real.log (2 * C * T + 1))) := by
    rw [Real.exp_nat_mul, show (3 : ℝ) * Real.log (2 * C * T + 1) =
      Real.log ((2 * C * T + 1) ^ 3) by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  have h2 : Real.exp |Real.log C| ^ n = Real.exp ((n : ℝ) * |Real.log C|) :=
    (Real.exp_nat_mul _ _).symm
  rw [mul_pow, mul_pow, h1, h2, ← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  unfold zeroSumRate
  ring

/-- `n² (2Cx+1)³ ≤ e^{K n} C^n` for `n ≥ 1` and `0 ≤ x ≤ T n`. -/
theorem poly_le_exp_rate {T C : ℝ} (hT : 1 < T) (hC : 0 < C) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx0 : 0 ≤ x) (hxT : x ≤ T * n) :
    (n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3 ≤ Real.exp (zeroSumRate T C * n) * C ^ n := by
  set a : ℝ := 2 * C * T + 1 with ha
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha1 : 1 ≤ a := by nlinarith
  have hCx : 0 ≤ C * x := mul_nonneg hC.le hx0
  have h1 : 2 * C * x + 1 ≤ a * n := by
    have := mul_le_mul_of_nonneg_left hxT hC.le
    nlinarith
  have h2 : (n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3 ≤ a ^ 3 * (n : ℝ) ^ 5 := by
    have : (2 * C * x + 1) ^ 3 ≤ (a * n) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    calc (n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3 ≤ (n : ℝ) ^ 2 * (a * n) ^ 3 := by gcongr
      _ = a ^ 3 * (n : ℝ) ^ 5 := by ring
  have h3 : (n : ℝ) ^ 5 ≤ Real.exp (5 * n) := by
    calc (n : ℝ) ^ 5 ≤ (Real.exp n) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg n) (natCast_le_exp n) 5
      _ = Real.exp (5 * n) := by
          rw [← Real.exp_nat_mul]
          norm_num
  have hbase : a ^ 3 ≤ (a ^ 3 * (Real.exp |Real.log C| * C)) ^ n := by
    have hb1 : a ^ 3 ≤ a ^ 3 * (Real.exp |Real.log C| * C) := by
      have := one_le_exp_abs_log_mul hC
      nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ a) 3]
    have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha1
    calc a ^ 3 ≤ a ^ 3 * (Real.exp |Real.log C| * C) := hb1
      _ ≤ (a ^ 3 * (Real.exp |Real.log C| * C)) ^ n :=
          le_self_pow₀ (ha3.trans hb1) (by omega)
  rw [exp_rate_mul hT hC n]
  calc (n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3 ≤ a ^ 3 * (n : ℝ) ^ 5 := h2
    _ ≤ a ^ 3 * Real.exp (5 * n) := by gcongr
    _ = Real.exp (5 * n) * a ^ 3 := by ring
    _ ≤ Real.exp (5 * n) * (a ^ 3 * (Real.exp |Real.log C| * C)) ^ n := by gcongr

/-- The analytic bridge: `e^{-Kn} xⁿ ≤ ((2R+1)^{n/2} / (2 (n/2) R + 1))²` with `R = ⌊Cx⌋₊`. -/
theorem exp_bound {T C : ℝ} (hT : 1 < T) (hC : 0 < C) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx0 : 0 ≤ x) (hxT : x ≤ T * n) :
    Real.exp (-zeroSumRate T C * n) * x ^ n ≤
      ((2 * (⌊C * x⌋₊ : ℝ) + 1) ^ (n / 2) / (2 * ((n / 2 : ℕ) : ℝ) * ⌊C * x⌋₊ + 1)) ^ 2 := by
  set R : ℝ := (⌊C * x⌋₊ : ℝ) with hR
  set m : ℝ := ((n / 2 : ℕ) : ℝ) with hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCx : 0 ≤ C * x := mul_nonneg hC.le hx0
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hRle : R ≤ C * x := Nat.floor_le hCx
  have hRgt : C * x < R + 1 := Nat.lt_floor_add_one _
  set q : ℝ := 2 * R + 1 with hq
  have hq1 : 1 ≤ q := by linarith
  have hqCx : C * x ≤ q := by linarith
  have hqle : q ≤ 2 * C * x + 1 := by linarith
  have hm1 : 2 * m ≤ n := by
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    rw [hm]
    exact_mod_cast this
  have hm2 : (n : ℝ) ≤ 2 * m + 1 := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    rw [hm]
    exact_mod_cast this
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set D : ℝ := 2 * m * R + 1 with hD
  have hD1 : 1 ≤ D := by nlinarith
  have hDle : D ≤ n * (2 * C * x + 1) := by nlinarith
  -- the core ratio dominates `(Cx)^n / (n² (2Cx+1)³)`
  have hpow : (C * x) ^ n ≤ q ^ (2 * (n / 2)) * q := by
    calc (C * x) ^ n ≤ q ^ n := pow_le_pow_left₀ hCx hqCx n
      _ ≤ q ^ (2 * (n / 2) + 1) := pow_le_pow_right₀ hq1 (by omega)
      _ = q ^ (2 * (n / 2)) * q := pow_succ _ _
  have hnum : (C * x) ^ n * D ^ 2 ≤ q ^ (2 * (n / 2)) * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3) := by
    have hD2 : D ^ 2 ≤ ((n : ℝ) * (2 * C * x + 1)) ^ 2 := pow_le_pow_left₀ (by linarith) hDle 2
    have hq0 : 0 ≤ q ^ (2 * (n / 2)) := by positivity
    calc (C * x) ^ n * D ^ 2 ≤ (q ^ (2 * (n / 2)) * q) * ((n : ℝ) * (2 * C * x + 1)) ^ 2 :=
          mul_le_mul hpow hD2 (by positivity) (by positivity)
      _ = q ^ (2 * (n / 2)) * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 2 * q) := by ring
      _ ≤ q ^ (2 * (n / 2)) * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 2 * (2 * C * x + 1)) := by
          gcongr
      _ = q ^ (2 * (n / 2)) * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3) := by ring
  have hcore : (C * x) ^ n / ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3) ≤ (q ^ (n / 2) / D) ^ 2 := by
    rw [div_pow, ← pow_mul, mul_comm (n / 2) 2, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [hnum]
  -- the exponential factor absorbs the polynomial losses
  have hpoly := poly_le_exp_rate hT hC n hn x hx0 hxT
  have hexp : Real.exp (-zeroSumRate T C * n) * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3) ≤ C ^ n := by
    calc Real.exp (-zeroSumRate T C * n) * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3)
        ≤ Real.exp (-zeroSumRate T C * n) * (Real.exp (zeroSumRate T C * n) * C ^ n) := by
          gcongr
      _ = C ^ n := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
  have hleft : Real.exp (-zeroSumRate T C * n) * x ^ n ≤
      (C * x) ^ n / ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3) := by
    rw [le_div_iff₀ (by positivity), mul_pow]
    calc Real.exp (-zeroSumRate T C * n) * x ^ n * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3)
        = (Real.exp (-zeroSumRate T C * n) * ((n : ℝ) ^ 2 * (2 * C * x + 1) ^ 3)) * x ^ n := by
          ring
      _ ≤ C ^ n * x ^ n := by gcongr
  exact hleft.trans hcore

end MajorityDynamics.Combinatorics.ZeroSumCounting
