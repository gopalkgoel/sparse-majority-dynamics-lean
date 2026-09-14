import MajorityDynamics.Idealized.LinearResponse.UniformBudget

/-! Finite stopping and amplification budgets, independent of a proportional
density exponent. For s = sqrt(pN), choose t = s^(1/4) and stop at the first
response a >= t^(-3). Then a < t, so the terminal nonlinear centering error
remains small. These finite lemmas do not assert a graph-trajectory theorem. -/
noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay

/-- First crossing of a geometric response scale, with the crucial upper
bound supplied by the preceding subcritical step. -/
theorem first_geometric_crossing (f : ℕ → ℝ) (H : ℕ) {s b : ℝ}
    (hs : 0 < s) (h0 : f 0 < b) (hH : b ≤ f H)
    (hstep : ∀ j, f (j + 1) = s * f j) :
    ∃ j : ℕ, 0 < j ∧ j ≤ H ∧ b ≤ f j ∧ f j < s * b ∧
      ∀ i < j, f i < b := by
  classical
  have hex : ∃ j, b ≤ f j := ⟨H, hH⟩
  let j := Nat.find hex
  have hj : b ≤ f j := Nat.find_spec hex
  have hmin : ∀ i < j, f i < b := by
    intro i hi
    exact lt_of_not_ge (Nat.find_min hex hi)
  have hj0 : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz] at hj
    linarith
  refine ⟨j, hj0, Nat.find_min' hex hH, hj, ?_, hmin⟩
  have hprev := hmin (j - 1) (by omega)
  have heq : j = (j - 1) + 1 := by omega
  calc
    f j = s * f (j - 1) := by conv_lhs => rw [heq]; rw [hstep]
    _ < s * b := mul_lt_mul_of_pos_left hprev hs

/-- In the stopping window t^-3 <= a <= t, division by the useful signal
min(a,1) does not destroy the inverse-scale error. This includes both small
terminal shifts and terminal shifts growing without bound. -/
theorem stopping_window_error {t a e : ℝ} (ht : 1 ≤ t) (ha : 0 < a)
    (halo : 1 ≤ a * t ^ 3) (hahi : a ≤ t) (he : 0 ≤ e) :
    ((1 + a + a ^ 2) / t ^ 4 + a * e) / min a 1 ≤ 3 / t + t * e := by
  have ht0 : 0 < t := by linarith
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have hmin : 0 < min a 1 := lt_min ha (by norm_num)
  apply (div_le_iff₀ hmin).mpr
  rcases le_total a 1 with ha1 | h1a
  · rw [min_eq_left ha1]
    have hsq : a ^ 2 ≤ a := by nlinarith
    have hat3 : a ≤ a * t ^ 3 := by nlinarith
    have hnumer : 1 + a + a ^ 2 ≤ 3 * a * t ^ 3 := by nlinarith
    have hratio : (1 + a + a ^ 2) / t ^ 4 ≤ 3 / t * a := by
      apply (div_le_iff₀ (pow_pos ht0 4)).mpr
      calc
        _ ≤ 3 * a * t ^ 3 := hnumer
        _ = _ := by field_simp
    have herr : a * e ≤ t * e * a := by
      have h := mul_le_mul_of_nonneg_right ht (mul_nonneg ha.le he)
      nlinarith only [h]
    nlinarith
  · rw [min_eq_right h1a, mul_one]
    have hsq : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha.le hahi 2
    have ht2 : t ^ 2 ≤ t ^ 3 := by nlinarith [sq_nonneg (t - 1)]
    have ht13 : t ≤ t ^ 3 := by nlinarith [sq_nonneg (t - 1)]
    have hnumer : 1 + a + a ^ 2 ≤ 3 * t ^ 3 := by linarith
    have hratio : (1 + a + a ^ 2) / t ^ 4 ≤ 3 / t := by
      apply (div_le_iff₀ (pow_pos ht0 4)).mpr
      calc
        _ ≤ 3 * t ^ 3 := hnumer
        _ = _ := by field_simp
    exact add_le_add hratio (mul_le_mul_of_nonneg_right hahi he)

end MajorityDynamics.Idealized.CriticalDay
