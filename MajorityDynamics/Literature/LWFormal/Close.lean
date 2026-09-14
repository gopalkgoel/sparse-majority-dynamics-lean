import Mathlib.Tactic

set_option autoImplicit true

/-!
# Relative closeness `x = x'(1 ± ξ)` and its calculus
-/

namespace LW

open Finset

/-- `x = x'(1 ± ξ)`. -/
def Close (x x' ξ : ℝ) : Prop := |x - x'| ≤ ξ * |x'|

/-- `|log(x/x')| ≤ ξ` (both positive). -/
def LogClose (x x' ξ : ℝ) : Prop := 0 < x ∧ 0 < x' ∧ |Real.log (x / x')| ≤ ξ

namespace Close

theorem mono {x x' a b : ℝ} (h : Close x x' a) (hab : a ≤ b) : Close x x' b :=
  h.trans (mul_le_mul_of_nonneg_right hab (abs_nonneg _))

theorem refl (x : ℝ) {a : ℝ} (ha : 0 ≤ a) : Close x x a := by
  simp only [Close, sub_self, abs_zero]; positivity

theorem abs_le {x x' a : ℝ} (h : Close x x' a) : |x| ≤ (1 + a) * |x'| := by
  have := abs_sub_abs_le_abs_sub x x'
  unfold Close at h; linarith

theorem abs_ge {x x' a : ℝ} (h : Close x x' a) : (1 - a) * |x'| ≤ |x| := by
  have := abs_sub_abs_le_abs_sub x' x
  rw [abs_sub_comm] at this
  unfold Close at h; linarith

theorem le_of_nonneg {x x' a : ℝ} (h : Close x x' a) (hx' : 0 ≤ x') : x ≤ (1 + a) * x' := by
  unfold Close at h; rw [abs_of_nonneg hx'] at h
  have := le_abs_self (x - x'); linarith

theorem ge_of_nonneg {x x' a : ℝ} (h : Close x x' a) (hx' : 0 ≤ x') : (1 - a) * x' ≤ x := by
  unfold Close at h; rw [abs_of_nonneg hx'] at h
  have := neg_abs_le (x - x'); linarith

theorem nonneg {x x' a : ℝ} (h : Close x x' a) (hx' : 0 ≤ x') (ha : a ≤ 1) : 0 ≤ x := by
  have := h.ge_of_nonneg hx'; nlinarith

theorem pos {x x' a : ℝ} (h : Close x x' a) (hx' : 0 < x') (ha : a < 1) : 0 < x := by
  have := h.ge_of_nonneg hx'.le; nlinarith

theorem const_mul {x x' a : ℝ} (c : ℝ) (h : Close x x' a) : Close (c * x) (c * x') a := by
  unfold Close at *
  rw [← mul_sub, abs_mul, abs_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

theorem add {x x' y y' a : ℝ} (hx : Close x x' a) (hy : Close y y' a) (hx' : 0 ≤ x')
    (hy' : 0 ≤ y') : Close (x + y) (x' + y') a := by
  unfold Close at *
  rw [abs_of_nonneg hx'] at hx; rw [abs_of_nonneg hy'] at hy
  rw [abs_of_nonneg (show 0 ≤ x' + y' by linarith)]
  calc |x + y - (x' + y')| = |(x - x') + (y - y')| := by ring_nf
    _ ≤ |x - x'| + |y - y'| := abs_add_le _ _
    _ ≤ a * (x' + y') := by linarith

theorem sum {ι : Type*} (s : Finset ι) {f g : ι → ℝ} {a : ℝ}
    (h : ∀ i ∈ s, Close (f i) (g i) a) (hg : ∀ i ∈ s, 0 ≤ g i) :
    Close (∑ i ∈ s, f i) (∑ i ∈ s, g i) a := by
  unfold Close at *
  rw [← sum_sub_distrib, abs_of_nonneg (sum_nonneg hg), mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (h i hi).trans ?_)
  rw [abs_of_nonneg (hg i hi)]

theorem mul {x x' y y' a b : ℝ} (hx : Close x x' a) (hy : Close y y' b) (ha : 0 ≤ a) :
    Close (x * y) (x' * y') (a + b + a * b) := by
  have h1 : |x * y - x' * y'| ≤ |x| * |y - y'| + |x - x'| * |y'| := by
    calc |x * y - x' * y'| = |x * (y - y') + (x - x') * y'| := by ring_nf
      _ ≤ |x * (y - y')| + |(x - x') * y'| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
  have h2 := hx.abs_le
  unfold Close at *
  rw [abs_mul]
  calc |x * y - x' * y'| ≤ |x| * |y - y'| + |x - x'| * |y'| := h1
    _ ≤ ((1 + a) * |x'|) * (b * |y'|) + (a * |x'|) * |y'| := by
        gcongr
    _ = (a + b + a * b) * (|x'| * |y'|) := by ring

theorem inv {x x' a : ℝ} (hx : Close x x' a) (ha : 0 ≤ a) (ha1 : a < 1) (hx' : x' ≠ 0) :
    Close x⁻¹ x'⁻¹ (a / (1 - a)) := by
  have hx'pos : 0 < |x'| := abs_pos.2 hx'
  have hlow := hx.abs_ge
  have hxpos : 0 < |x| := by nlinarith
  have hx0 : x ≠ 0 := abs_pos.1 hxpos
  unfold Close at *
  rw [inv_sub_inv hx0 hx', abs_div, abs_mul, abs_sub_comm, abs_inv, div_le_iff₀ (by positivity)]
  have : a / (1 - a) * |x'|⁻¹ * (|x| * |x'|) = a * |x| / (1 - a) := by field_simp
  rw [this, le_div_iff₀ (by linarith)]
  nlinarith

theorem inv_le {x x' a b : ℝ} (hx : Close x x' a) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hx' : x' ≠ 0)
    (hb : 2 * a ≤ b) : Close x⁻¹ x'⁻¹ b := by
  refine (hx.inv ha (by linarith) hx').mono ?_
  rw [div_le_iff₀ (by linarith)]; nlinarith

/-- `|q - q'| ≤ x` and `q' ≤ 1/2` give `1 - q = (1 - q')(1 ± 2x)`. -/
theorem one_sub {q q' x : ℝ} (h : |q - q'| ≤ x) (hq : q' ≤ 1 / 2) : Close (1 - q) (1 - q') (2 * x) := by
  unfold Close
  have : 1 - q - (1 - q') = -(q - q') := by ring
  rw [this, abs_neg, abs_of_nonneg (show 0 ≤ 1 - q' by linarith)]
  have := abs_nonneg (q - q')
  nlinarith

theorem of_logClose {x x' ξ : ℝ} (h : LogClose x x' ξ) (hξ : ξ ≤ 1) : Close x x' (2 * ξ) := by
  obtain ⟨hx, hx', hl⟩ := h
  have ht : |Real.log (x / x')| ≤ 1 := hl.trans hξ
  have := Real.abs_exp_sub_one_le ht
  rw [Real.exp_log (by positivity)] at this
  unfold Close
  rw [abs_of_pos hx']
  have e1 : x - x' = (x / x' - 1) * x' := by field_simp
  rw [e1, abs_mul, abs_of_pos hx']
  nlinarith [abs_nonneg (Real.log (x / x'))]

theorem logClose {x x' η : ℝ} (h : Close x x' η) (hx' : 0 < x') (hη : 0 ≤ η) (hη' : η ≤ 1 / 2) :
    LogClose x x' (2 * η) := by
  have hx := h.pos hx' (by linarith)
  refine ⟨hx, hx', ?_⟩
  have hle := h.le_of_nonneg hx'.le
  have hge := h.ge_of_nonneg hx'.le
  have ht : 0 < x / x' := by positivity
  have h1 : x / x' ≤ 1 + η := by rw [div_le_iff₀ hx']; linarith
  have h2 : 1 - η ≤ x / x' := by rw [le_div_iff₀ hx']; linarith
  rw [_root_.abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
    rw [Real.log_inv] at this
    have h3 : (x / x')⁻¹ - 1 ≤ 2 * η := by
      rw [inv_eq_one_div, div_sub_one ht.ne', div_le_iff₀ ht]; nlinarith
    linarith
  · have := Real.log_le_sub_one_of_pos ht; linarith

end Close

end LW
