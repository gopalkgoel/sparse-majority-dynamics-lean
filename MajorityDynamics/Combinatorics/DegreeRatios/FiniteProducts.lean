import MajorityDynamics.Combinatorics.DegreeRatios.LogBounds
import Mathlib.Data.Nat.Choose.Cast

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Combinatorics.DegreeRatios

def logFalling (N a : ℕ) : ℝ :=
  Real.log (N.factorial : ℝ) - Real.log ((N - a).factorial : ℝ)

theorem logFalling_eq_sum {N a : ℕ} (ha : a ≤ N) :
    logFalling N a = ∑ i ∈ Finset.range a, Real.log (N - i : ℕ) := by
  induction a with
  | zero => simp [logFalling]
  | succ a ih =>
    have hrec : (N - a).factorial = (N - a) * (N - (a + 1)).factorial := by
      have hid : N - a = (N - (a + 1)) + 1 := by omega
      conv_lhs => rw [hid, Nat.factorial_succ]
      rw [← hid]
    have hn : 0 < N - a := by omega
    have hlog : Real.log ((N - a).factorial : ℝ) =
        Real.log (N - a : ℕ) + Real.log ((N - (a + 1)).factorial : ℝ) := by
      rw [hrec, Nat.cast_mul, Real.log_mul (by exact_mod_cast hn.ne') (by positivity)]
    rw [Finset.sum_range_succ, ← ih (by omega)]
    dsimp [logFalling]
    linarith

/-- A deliberately coarse bound: constant errors suffice for C.3, so no
second-order cancellation between the factorial products is needed. -/
theorem logFalling_error {N a : ℕ} (hN : 0 < N) (ha : 2 * a ≤ N) :
    |logFalling N a - (a : ℝ) * Real.log N| ≤ 2 * (a : ℝ) ^ 2 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have har : 2 * (a : ℝ) ≤ N := by exact_mod_cast ha
  have hsum : logFalling N a - (a : ℝ) * Real.log N =
      ∑ i ∈ Finset.range a, (Real.log (N - i : ℕ) - Real.log N) := by
    rw [logFalling_eq_sum (by omega), Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ Finset.range a, |Real.log (N - i : ℕ) - Real.log N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range a, (2 * (a : ℝ) / N) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < a := Finset.mem_range.mp hi
      have hir : (i : ℝ) ≤ a := by exact_mod_cast hi'.le
      have hsub : 0 < N - i := by omega
      have hx : |(i : ℝ) / N| ≤ 1 / 2 := by
        rw [abs_of_nonneg (by positivity), div_le_iff₀ hNr]
        linarith
      have hid : Real.log (N - i : ℕ) - Real.log N =
          Real.log (1 - (i : ℝ) / N) := by
        rw [← Real.log_div (by exact_mod_cast hsub.ne') hNr.ne', Nat.cast_sub (by omega)]
        congr 1
        field_simp
      rw [hid]
      calc
        _ ≤ 2 * |(i : ℝ) / N| := abs_log_one_sub_le hx
        _ = 2 * (i : ℝ) / N := by rw [abs_of_nonneg (by positivity)]; ring
        _ ≤ 2 * (a : ℝ) / N := by gcongr
    _ = 2 * (a : ℝ) ^ 2 / N := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem log_choose_eq {N m : ℕ} (hm : m ≤ N) :
    Real.log (N.choose m : ℝ) = Real.log (N.factorial : ℝ) -
      Real.log (m.factorial : ℝ) - Real.log ((N - m).factorial : ℝ) := by
  rw [Nat.cast_choose ℝ hm, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

/-- Exact factorial identity for the inverse degree-removal quotient. -/
theorem log_choose_removal {N m h d : ℕ} (hm : m ≤ N) (hh : h ≤ N)
    (hdm : d ≤ m) (hdh : d ≤ h) (hrest : h - d ≤ N - m) :
    Real.log ((N.choose m : ℝ) / ((N - h).choose (m - d) : ℝ)) =
      logFalling N h - logFalling m d - logFalling (N - m) (h - d) := by
  have hr : m - d ≤ N - h := by omega
  have hp : (0 : ℝ) < N.choose m := by exact_mod_cast Nat.choose_pos hm
  have hpr : (0 : ℝ) < (N - h).choose (m - d) := by exact_mod_cast Nat.choose_pos hr
  have hid : N - h - (m - d) = N - m - (h - d) := by omega
  rw [Real.log_div hp.ne' hpr.ne', log_choose_eq hm, log_choose_eq hr, hid]
  dsimp [logFalling]
  ring

def removalMain (N m h d : ℕ) : ℝ :=
  (h : ℝ) * Real.log N - (d : ℝ) * Real.log m -
    ((h : ℝ) - d) * Real.log (N - m : ℕ)

theorem log_choose_removal_error {N m h d : ℕ}
    (hm : 0 < m) (hmN : m < N) (hdh : d ≤ h)
    (hh : 2 * h ≤ N) (hd : 2 * d ≤ m) (hr : 2 * (h - d) ≤ N - m) :
    |Real.log ((N.choose m : ℝ) / ((N - h).choose (m - d) : ℝ)) -
      removalMain N m h d| ≤
      2 * (h : ℝ) ^ 2 / N + 2 * (d : ℝ) ^ 2 / m +
        2 * (h - d : ℕ) ^ 2 / (N - m : ℕ) := by
  have h1 := logFalling_error (hm.trans hmN) hh
  have h2 := logFalling_error hm hd
  have h3 := logFalling_error (Nat.sub_pos_of_lt hmN) hr
  rw [log_choose_removal hmN.le (by omega) (by omega) hdh (by omega)]
  have hid : logFalling N h - logFalling m d - logFalling (N - m) (h - d) -
      removalMain N m h d =
      (logFalling N h - (h : ℝ) * Real.log N) -
      (logFalling m d - (d : ℝ) * Real.log m) -
      (logFalling (N - m) (h - d) - (h - d : ℕ) * Real.log (N - m : ℕ)) := by
    rw [Nat.cast_sub hdh]
    dsimp [removalMain]
    ring
  rw [hid]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add h1 h2) h3)

theorem removalMain_density {N m h d : ℕ} (hm : 0 < m) (hmN : m < N) :
    removalMain N m h d =
      -(d : ℝ) * Real.log ((m : ℝ) / N) -
        ((h : ℝ) - d) * Real.log (1 - (m : ℝ) / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hm.trans hmN
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hNr : (0 : ℝ) < (N - m : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hmN
  have hid : 1 - (m : ℝ) / N = (N - m : ℕ) / (N : ℝ) := by
    rw [Nat.cast_sub hmN.le]
    field_simp
  rw [hid, Real.log_div hmr.ne' hN.ne', Real.log_div hNr.ne' hN.ne']
  dsimp [removalMain]
  ring

theorem removalMain_double {N m h d : ℕ} (hm : 0 < m) (hmN : m < N) :
    removalMain (2 * N) (2 * m) (2 * h) (2 * d) = 2 * removalMain N m h d := by
  rw [removalMain_density (by omega : 0 < 2 * m) (by omega : 2 * m < 2 * N),
    removalMain_density hm hmN]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (hm.trans hmN).ne'
  have hid : ((2 * m : ℕ) : ℝ) / (2 * N : ℕ) = (m : ℝ) / N := by
    push_cast
    field_simp
  rw [hid]
  push_cast
  ring

end MajorityDynamics.Combinatorics.DegreeRatios
