import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative normalization of finite exponential tilts

The algebraic step in Appendix A.2, `thm:tilted_expansion`, Step 4.
The bound is uniform over the finite support and over the observable; in
particular the observable may include an indicator with strict inequalities.
This module does not assert binomial truncation or point approximation.
-/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Analysis.FiniteTiltEstimate

variable {α : Type*}

def average (S : Finset α) (w f : α → ℝ) : ℝ := ∑ a ∈ S, w a * f a

theorem average_add (S : Finset α) (w f g : α → ℝ) :
    average S w (fun a => f a + g a) = average S w f + average S w g := by
  simp [average, mul_add, Finset.sum_add_distrib]

theorem average_sub (S : Finset α) (w f g : α → ℝ) :
    average S w (fun a => f a - g a) = average S w f - average S w g := by
  simp [average, mul_sub, Finset.sum_sub_distrib]

theorem average_const (S : Finset α) (w : α → ℝ) (hw : ∑ a ∈ S, w a = 1)
    (c : ℝ) : average S w (fun _ => c) = c := by
  simp [average, ← Finset.sum_mul, hw]

theorem abs_average_le (S : Finset α) (w f : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hs : ∑ a ∈ S, w a = 1)
    (H : ℝ) (hf : ∀ a ∈ S, |f a| ≤ H) : |average S w f| ≤ H := by
  calc
    _ ≤ ∑ a ∈ S, |w a * f a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ S, w a * |f a| := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [abs_mul, abs_of_nonneg (hw a ha)]
    _ ≤ ∑ a ∈ S, w a * H := Finset.sum_le_sum fun a ha =>
      mul_le_mul_of_nonneg_left (hf a ha) (hw a ha)
    _ = H := by rw [← Finset.sum_mul, hs, one_mul]

/-- An explicit quotient remainder, including the normalization correction. -/
theorem quotient_remainder (A B u v R H b : ℝ)
    (hH : 0 ≤ H) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 4)
    (hA : |A| ≤ H) (hB : |B| ≤ H * b) (hu : |u| ≤ b)
    (hv : |v| ≤ b ^ 2) (hR : |R| ≤ H * b ^ 2) :
    |(A + B + R) / (1 + u + v) - (A + B - u * A)| ≤ 12 * H * b ^ 2 := by
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b ^ 2 ≤ b := by nlinarith
  have huv : |u + v| ≤ 2 * b :=
    (abs_add_le u v).trans (by linarith)
  have hden : 1 / 2 ≤ 1 + u + v := by
    have := (abs_le.mp huv).1
    linarith
  have hdenpos : 0 < 1 + u + v := by linarith
  have hBA : |B - u * A| ≤ 2 * H * b := by
    calc
      _ ≤ |B| + |u * A| := abs_sub _ _
      _ ≤ H * b + b * H := add_le_add hB (by
        rw [abs_mul]
        exact mul_le_mul hu hA (abs_nonneg _) hb)
      _ = _ := by ring
  have hnum : |R - A * v - (B - u * A) * (u + v)| ≤ 6 * H * b ^ 2 := by
    calc
      _ ≤ |R| + |A * v| + |(B - u * A) * (u + v)| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ H * b ^ 2 + H * b ^ 2 + (2 * H * b) * (2 * b) := by
        apply add_le_add
        · apply add_le_add hR
          rw [abs_mul]
          exact mul_le_mul hA hv (abs_nonneg _) hH
        · rw [abs_mul]
          exact mul_le_mul hBA huv (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have heq : (A + B + R) / (1 + u + v) - (A + B - u * A) =
      (R - A * v - (B - u * A) * (u + v)) / (1 + u + v) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hdenpos]
  apply (div_le_iff₀ hdenpos).mpr
  calc
    _ ≤ 6 * H * b ^ 2 := hnum
    _ ≤ 12 * H * b ^ 2 * (1 + u + v) := by
      nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 12 * H * b ^ 2 by positivity)]

/-- Finite exponential reweighting has a covariance first-order term and
an explicit quadratic error. No smoothness or event-boundary assumption. -/
theorem exponential_remainder (S : Finset α) (w f z : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hs : ∑ a ∈ S, w a = 1)
    (H b : ℝ) (hH : 0 ≤ H) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 4)
    (hf : ∀ a ∈ S, |f a| ≤ H) (hz : ∀ a ∈ S, |z a| ≤ b) :
    |average S w (fun a => Real.exp (z a) * f a) /
        average S w (fun a => Real.exp (z a)) -
      (average S w f + average S w (fun a => z a * f a) -
        average S w z * average S w f)| ≤ 12 * H * b ^ 2 := by
  let e := fun a => Real.exp (z a) - 1 - z a
  have he : ∀ a ∈ S, |e a| ≤ b ^ 2 := by
    intro a ha
    apply (Real.abs_exp_sub_one_sub_id_le ((hz a ha).trans (by linarith))).trans
    have := hz a ha
    nlinarith [sq_abs (z a), abs_nonneg (z a)]
  have hR : |average S w (fun a => e a * f a)| ≤ H * b ^ 2 := by
    apply abs_average_le S w _ hw hs
    intro a ha
    rw [abs_mul, mul_comm H]
    exact mul_le_mul (he a ha) (hf a ha) (abs_nonneg _) (sq_nonneg _)
  have hB : |average S w (fun a => z a * f a)| ≤ H * b := by
    apply abs_average_le S w _ hw hs
    intro a ha
    rw [abs_mul, mul_comm H]
    exact mul_le_mul (hz a ha) (hf a ha) (abs_nonneg _) hb
  have hden : average S w (fun a => Real.exp (z a)) =
      1 + average S w z + average S w e := by
    rw [← average_const S w hs 1, ← average_add, ← average_add]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [e]
    ring
  have hnum : average S w (fun a => Real.exp (z a) * f a) =
      average S w f + average S w (fun a => z a * f a) +
        average S w (fun a => e a * f a) := by
    rw [← average_add, ← average_add]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [e]
    ring
  rw [hnum, hden]
  exact quotient_remainder _ _ _ _ _ H b hH hb hbsmall
    (abs_average_le S w f hw hs H hf) hB
    (abs_average_le S w z hw hs b hz) (abs_average_le S w e hw hs _ he) hR

/-- Normalizing a relative perturbation of weights costs at most `4δH`.
This is the finite averaging step in A.2, Step 3. -/
theorem relative_weight_remainder (S : Finset α) (w f e : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hs : ∑ a ∈ S, w a = 1)
    (H δ : ℝ) (hH : 0 ≤ H) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 2)
    (hf : ∀ a ∈ S, |f a| ≤ H) (he : ∀ a ∈ S, |e a| ≤ δ) :
    |average S w (fun a => (1 + e a) * f a) /
        average S w (fun a => 1 + e a) - average S w f| ≤ 4 * H * δ := by
  have hu := abs_average_le S w e hw hs δ he
  have hA := abs_average_le S w f hw hs H hf
  have hB : |average S w (fun a => e a * f a)| ≤ δ * H := by
    apply abs_average_le S w _ hw hs
    intro a ha
    rw [abs_mul]
    exact mul_le_mul (he a ha) (hf a ha) (abs_nonneg _) hδ
  have hd : 0 < 1 + average S w e := by
    have := (abs_le.mp hu).1
    linarith
  have hnum : average S w (fun a => (1 + e a) * f a) =
      average S w f + average S w (fun a => e a * f a) := by
    simp [average, add_mul, mul_add, Finset.sum_add_distrib]
  rw [hnum, average_add, average_const S w hs]
  rw [div_sub' hd.ne', abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have heq : average S w f + average S w (fun a => e a * f a) -
      (1 + average S w e) * average S w f =
      average S w (fun a => e a * f a) - average S w f * average S w e := by ring
  rw [heq]
  calc
    _ ≤ |average S w (fun a => e a * f a)| + |average S w f * average S w e| :=
      abs_sub _ _
    _ ≤ δ * H + H * δ := add_le_add hB (by
      rw [abs_mul]
      exact mul_le_mul hA hu (abs_nonneg _) hH)
    _ ≤ 4 * H * δ * (1 + average S w e) := by
      have hlo : 1 / 2 ≤ 1 + average S w e := by
        have := (abs_le.mp hu).1
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hlo (show 0 ≤ 4 * H * δ by positivity)]

/-- Identify a normalized reweighted law without leaving a normalizer as an
unproved assumption. -/
theorem reweighted_average (S : Finset α) (w w' z f : α → ℝ) (K : ℝ)
    (hs : ∑ a ∈ S, w' a = 1)
    (h : ∀ a ∈ S, w' a = K * (w a * Real.exp (z a))) :
    average S w' f = average S w (fun a => Real.exp (z a) * f a) /
      average S w (fun a => Real.exp (z a)) := by
  have hden : K * average S w (fun a => Real.exp (z a)) = 1 := by
    rw [average, Finset.mul_sum]
    calc
      _ = ∑ a ∈ S, w' a := Finset.sum_congr rfl fun a ha => (h a ha).symm
      _ = 1 := hs
  have hd : average S w (fun a => Real.exp (z a)) ≠ 0 := by
    intro he
    rw [he, mul_zero] at hden
    norm_num at hden
  apply (eq_div_iff hd).mpr
  have hnum : average S w' f = K * average S w (fun a => Real.exp (z a) * f a) := by
    rw [average, average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [h a ha]
    ring
  rw [hnum]
  calc
    _ = average S w (fun a => Real.exp (z a) * f a) *
        (K * average S w (fun a => Real.exp (z a))) := by ring
    _ = _ := by rw [hden, mul_one]

end MajorityDynamics.Analysis.FiniteTiltEstimate
