import MajorityDynamics.Literature.LWFormal.Approx

set_option autoImplicit true

/-!
# Identities for the shifted sequence `d - e b`
-/

namespace LW

open Finset

variable {n : ℕ} (d : Seq n)

theorem M1_cast : (M1 d : ℝ) = ∑ i, (d i : ℝ) := by simp [M1]

theorem sum_sub_dbar (hn : (n : ℝ) ≠ 0) : ∑ i, ((d i : ℝ) - dbar d) = 0 := by
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, dbar, M1_cast]
  field_simp
  ring

theorem sum_eps (hn : (n : ℝ) ≠ 0) : ∑ i, eps d i = 0 := by
  simp only [eps, ← sum_div, sum_sub_dbar d hn, zero_div]

theorem sum_eps_sq (hn : (n : ℝ) ≠ 0) (hd : dbar d ≠ 0) :
    ∑ i, eps d i ^ 2 = n * (sigma2 d / dbar d ^ 2) := by
  simp only [eps, div_pow, ← sum_div, sigma2]
  field_simp

theorem sigma2_nonneg : 0 ≤ sigma2 d :=
  div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg n)

theorem sigma2_le (hn : (n : ℝ) ≠ 0) {D : ℝ} (h : ∀ i, |(d i : ℝ) - dbar d| ≤ D) :
    sigma2 d ≤ D ^ 2 := by
  have hn' : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0] at hn
    · exact_mod_cast h0
  rw [sigma2, div_le_iff₀ hn']
  calc ∑ i, ((d i : ℝ) - dbar d) ^ 2 ≤ ∑ _i : Fin n, D ^ 2 :=
        sum_le_sum fun i _ => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = D ^ 2 * n := by simp [mul_comm]

theorem dbar_sub_e (b : Fin n) : dbar (d - e b) = dbar d - 1 / n := by
  rw [dbar, dbar, M1_sub_e]; push_cast; ring

theorem mu_sub_e (b : Fin n) (hn : (n : ℝ) ≠ 0) (hd : dbar d ≠ 0) :
    mu (d - e b) = mu d * (1 - 1 / dbar d / n) := by
  rw [mu, mu, dbar_sub_e]; field_simp

theorem eps_sub_e (b i : Fin n) (hn : (n : ℝ) ≠ 0) (hd : dbar d ≠ 0)
    (hnd : (n : ℝ) * dbar d - 1 ≠ 0) :
    eps (d - e b) i =
      (eps d i - (if i = b then 1 / dbar d else 0) + 1 / dbar d / n) / (1 - 1 / dbar d / n) := by
  have h1 : dbar d - 1 / n ≠ 0 := fun h =>
    hnd (by rw [sub_eq_zero] at h; rw [h]; field_simp; ring)
  have h2 : 1 - 1 / dbar d / n ≠ 0 := fun h => hnd (by
    have : 1 / dbar d / n = 1 := by linarith
    field_simp at this; linarith)
  rw [eps, eps, dbar_sub_e, sub_e_apply]; push_cast
  split_ifs <;> field_simp <;> ring

theorem sigma2_sub_e (b : Fin n) (hn : (n : ℝ) ≠ 0) :
    sigma2 (d - e b) = sigma2 d + (1 - 1 / n - 2 * ((d b : ℝ) - dbar d)) / n := by
  simp only [sigma2, dbar_sub_e, sub_e_apply]
  push_cast
  have key : ∀ i, ((d i : ℝ) - (if i = b then 1 else 0) - (dbar d - 1 / n)) ^ 2 =
      ((d i : ℝ) - dbar d) ^ 2 + 2 / n * ((d i : ℝ) - dbar d) + 1 / n ^ 2 +
        if i = b then 1 - 2 * (((d i : ℝ) - dbar d) + 1 / n) else 0 := fun i => by
    split_ifs <;> ring
  simp only [key, sum_add_distrib, ← mul_sum, sum_sub_dbar d hn, sum_ite_eq', mem_univ, if_true,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-! ### The doubly shifted sequence `d - e a - e v` -/

theorem dbar_sub_e_sub_e (a v : Fin n) : dbar (d - e a - e v) = dbar d - 2 / n := by
  rw [dbar_sub_e, dbar_sub_e]; ring

theorem mu_sub_e_sub_e (a v : Fin n) (hn : (n : ℝ) ≠ 0) (hd : dbar d ≠ 0) :
    mu (d - e a - e v) = mu d * (1 - 2 * (1 / dbar d / n)) := by
  rw [mu, mu, dbar_sub_e_sub_e]; field_simp

theorem inv_dbar_sub_e_sub_e (a v : Fin n) (hn : (n : ℝ) ≠ 0) (hd : dbar d ≠ 0)
    (hnd : (n : ℝ) * dbar d - 2 ≠ 0) :
    1 / dbar (d - e a - e v) = (1 / dbar d) / (1 - 2 * (1 / dbar d / n)) := by
  have h1 : dbar d - 2 / n ≠ 0 := fun h =>
    hnd (by rw [sub_eq_zero] at h; rw [h]; field_simp; ring)
  rw [dbar_sub_e_sub_e]; field_simp

theorem eps_sub_e_sub_e (a v i : Fin n) (hn : (n : ℝ) ≠ 0) (hd : dbar d ≠ 0)
    (hnd : (n : ℝ) * dbar d - 2 ≠ 0) :
    eps (d - e a - e v) i =
      (eps d i - (if i = a then 1 / dbar d else 0) - (if i = v then 1 / dbar d else 0) +
        2 * (1 / dbar d / n)) / (1 - 2 * (1 / dbar d / n)) := by
  have h1 : dbar d - 2 / n ≠ 0 := fun h =>
    hnd (by rw [sub_eq_zero] at h; rw [h]; field_simp; ring)
  have h2 : 1 - 2 * (1 / dbar d / n) ≠ 0 := fun h => hnd (by
    have : 2 * (1 / dbar d / n) = 1 := by linarith
    field_simp at this; linarith)
  rw [eps, eps, dbar_sub_e_sub_e, sub_e_apply, sub_e_apply]; push_cast
  split_ifs <;> field_simp <;> ring

theorem sigma2_sub_e_sub_e (a v : Fin n) (hav : a ≠ v) (hn : (n : ℝ) ≠ 0) :
    sigma2 (d - e a - e v) =
      sigma2 d + (2 - 4 / n - 2 * ((d a : ℝ) + d v - 2 * dbar d)) / n := by
  rw [sigma2_sub_e _ _ hn, sigma2_sub_e _ _ hn, dbar_sub_e, sub_e_apply, if_neg hav.symm]
  push_cast; ring

end LW
