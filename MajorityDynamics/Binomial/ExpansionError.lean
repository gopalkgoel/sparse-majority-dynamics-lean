import MajorityDynamics.Binomial.UniformWindow
import MajorityDynamics.Analysis.LogTail

/-! # Collecting the finite-window and discarded-tail error rates -/

noncomputable section
open Filter Topology
namespace MajorityDynamics.Binomial.Approximation

theorem finite_expansion_error (a d T p s l B δ : ℝ) (D : ℕ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hT : 0 ≤ T) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hl : 1 ≤ l) (hδ : δ ≤ 32 * d * T * p * l ^ 2) :
    12 * (a * (s * l) ^ D) * (d * B * (s * l)) ^ 2 +
      8 * (a * (s * l) ^ D) * δ ≤
      (12 * a * d ^ 2 + 256 * a * d * T) * max p (B ^ 2 * s ^ 2 * l ^ 2) *
        s ^ D * l ^ (2 + D) := by
  have hl0 : 0 ≤ l := by linarith
  have hpow : l ^ D ≤ l ^ (2 + D) := by
    rw [pow_add]
    nlinarith [pow_nonneg hl0 D, mul_nonneg (pow_nonneg hl0 D) (show 0 ≤ l ^ 2 - 1 by nlinarith)]
  have hmax0 : 0 ≤ max p (B ^ 2 * s ^ 2 * l ^ 2) := hp.trans (le_max_left _ _)
  have hquad : 12 * (a * (s * l) ^ D) * (d * B * (s * l)) ^ 2 ≤
      (12 * a * d ^ 2) * max p (B ^ 2 * s ^ 2 * l ^ 2) * s ^ D * l ^ (2 + D) := by
    calc
      _ = (12 * a * d ^ 2) * (B ^ 2 * s ^ 2 * l ^ 2) * s ^ D * l ^ D := by rw [mul_pow]; ring
      _ ≤ (12 * a * d ^ 2) * max p (B ^ 2 * s ^ 2 * l ^ 2) * s ^ D * l ^ D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)) (by positivity)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hlin : 8 * (a * (s * l) ^ D) * δ ≤
      (256 * a * d * T) * max p (B ^ 2 * s ^ 2 * l ^ 2) * s ^ D * l ^ (2 + D) := by
    calc
      _ ≤ 8 * (a * (s * l) ^ D) * (32 * d * T * p * l ^ 2) :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = (256 * a * d * T) * p * s ^ D * l ^ (2 + D) := by rw [mul_pow, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)) (by positivity)) (by positivity)
  calc
    _ ≤ (12 * a * d ^ 2) * max p (B ^ 2 * s ^ 2 * l ^ 2) * s ^ D * l ^ (2 + D) +
        (256 * a * d * T) * max p (B ^ 2 * s ^ 2 * l ^ 2) * s ^ D * l ^ (2 + D) := add_le_add hquad hlin
    _ = _ := by ring

theorem tail_expansion_error (a d T n B b τ₀ τ₁ t : ℝ) (D : ℕ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hT : 0 ≤ T) (hn : 1 ≤ n)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hτ₀ : τ₀ ≤ 2 * d * t) (hτ₁ : τ₁ ≤ 2 * d * t) :
    2 * (a * (2 * T * n) ^ D) * τ₁ +
      2 * (a * (2 * T * n) ^ D) * (1 + b + 2 * (d * B * (2 * T * n))) * τ₀ ≤
      (4 * a * (2 * T) ^ D * d * (3 + 4 * d * T) + 1) * n ^ (D + 1) * t := by
  have hn0 : 0 ≤ n := by linarith
  have hZ : d * B * (2 * T * n) ≤ 2 * d * T * n := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB1 hd) (show 0 ≤ 2 * T * n by positivity)
    nlinarith only [h]
  have hcoeff : 2 + b + 2 * (d * B * (2 * T * n)) ≤ (3 + 4 * d * T) * n := by
    nlinarith only [hZ, hb1, hn]
  calc
    _ ≤ 2 * (a * (2 * T * n) ^ D) * (2 * d * t) +
        2 * (a * (2 * T * n) ^ D) * (1 + b + 2 * (d * B * (2 * T * n))) * (2 * d * t) :=
      add_le_add (mul_le_mul_of_nonneg_left hτ₁ (by positivity))
        (mul_le_mul_of_nonneg_left hτ₀ (by positivity))
    _ = 4 * (a * (2 * T * n) ^ D) * d * t * (2 + b + 2 * (d * B * (2 * T * n))) := by ring
    _ ≤ 4 * (a * (2 * T * n) ^ D) * d * t * ((3 + 4 * d * T) * n) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = (4 * a * (2 * T) ^ D * d * (3 + 4 * d * T)) * n ^ (D + 1) * t := by
      rw [mul_pow, pow_succ]
      ring
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hn0 (D + 1)) ht]

theorem density_inverse_size (θ T : ℝ) (n : ℕ) (p : Probability)
    (hθ : θ < 1) (hT : 0 < T) (hn : 1 ≤ n) (h : Density θ T n p) :
    1 / (n : ℝ) ≤ T * (p : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-θ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  rw [Real.rpow_neg_one] at hpow
  have hh := mul_le_mul_of_nonneg_left h.1.le hT.le
  simp only [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at hh
  simpa only [one_div] using hpow.trans hh

/-- Exponential-in-log-square tails absorb every polynomial prefactor. -/
theorem polynomial_log_tail (A C : ℝ) (D : ℕ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      A * (n : ℝ) ^ D * Real.exp (-((Real.log n) ^ 2) / C) ≤ 1 / n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    Analysis.log_tail_eventually_le_power A C ((D + 1 : ℕ) : ℝ) hA hC] with n hn htail
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_neg hn0.le, Real.rpow_natCast] at htail
  have h := mul_le_mul_of_nonneg_right htail (pow_nonneg hn0.le D)
  have heq : ((n : ℝ) ^ (D + 1))⁻¹ * (n : ℝ) ^ D = 1 / n := by
    rw [pow_succ]
    field_simp
  calc
    _ = (A * Real.exp (-((Real.log n) ^ 2) / C)) * (n : ℝ) ^ D := by ring
    _ ≤ _ := h.trans_eq heq

end MajorityDynamics.Binomial.Approximation
