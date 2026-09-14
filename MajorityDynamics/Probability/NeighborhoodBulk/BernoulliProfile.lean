import MajorityDynamics.Combinatorics.DegreeRatios.LogBounds
import MajorityDynamics.Probability.NeighborhoodBulk.Basic

noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Combinatorics.DegreeRatios

def bernoulliProduct {V : Type*} (A R : Finset V) (q : V → ℝ) : ℝ :=
  (∏ i ∈ R, q i) * ∏ i ∈ A \ R, (1 - q i)

def linearWeight {V : Type*} (A R : Finset V) (p H : ℝ) (d : V → ℝ) : ℝ :=
  (∑ i ∈ R, (d i - p * H) / (p * H)) - ∑ i ∈ A \ R, (d i - p * H) / H

theorem profile_entry (p H D L d : ℝ) (hp : 0 < p) (hp16 : p ≤ 1 / 16)
    (hH : 2 ≤ H) (hDlo : H - 1 ≤ D) (hDhi : D ≤ H) (hL : 0 ≤ L)
    (hscale : 2 * L ≤ Real.sqrt (p * H)) (hd : |d - p * H| ≤ Real.sqrt (p * H) * L) :
    0 < d / D ∧ d / D < 1 ∧
      |Real.log (d / D) - Real.log p - (d - p * H) / (p * H)| ≤
        2 * L ^ 2 / (p * H) + 2 / H ∧
      |Real.log (1 - d / D) + d / H| ≤ 18 * p ^ 2 + 3 * p / H := by
  have hH0 : 0 < H := by linarith
  have hD : 0 < D := by linarith
  have hhalf : H / 2 ≤ D := by linarith
  have hx : 0 < p * H := mul_pos hp hH0
  have hs0 := Real.sqrt_nonneg (p * H)
  have hsquare := Real.sq_sqrt hx.le
  have hdev : |d - p * H| ≤ p * H / 2 := by
    have hh := mul_le_mul_of_nonneg_left hscale hs0
    nlinarith
  have hdlo : p * H / 2 ≤ d := by linarith [(abs_le.mp hdev).1]
  have hdhi : d ≤ 3 * p * H / 2 := by linarith [(abs_le.mp hdev).2]
  have hd0 : 0 < d := (by positivity : 0 < p * H / 2).trans_le hdlo
  have hq : 0 < d / D := div_pos hd0 hD
  have hq3 : d / D ≤ 3 * p := by
    apply (div_le_iff₀ hD).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 3 * p)
    linarith
  have hqhalf : |d / D| ≤ 1 / 2 := by rw [abs_of_pos hq]; linarith
  let e := (d - p * H) / (p * H)
  have hehalf : |e| ≤ 1 / 2 := by
    dsimp [e]
    rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
    linarith
  have hepos : 0 < 1 + e := by linarith [(abs_le.mp hehalf).1]
  have hesq : e ^ 2 ≤ L ^ 2 / (p * H) := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Real.sqrt (p * H) * L)).mpr hd
    rw [sq_abs, mul_pow, Real.sq_sqrt hx.le] at hh
    dsimp [e]
    rw [div_pow]
    calc
      _ ≤ (p * H * L ^ 2) / (p * H) ^ 2 := div_le_div_of_nonneg_right hh (sq_nonneg _)
      _ = _ := by field_simp
  let t := (H - D) / H
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hDhi) hH0.le
  have ht1 : t ≤ 1 / H := by apply (div_le_div_iff_of_pos_right hH0).mpr; linarith
  have hthalf : |t| ≤ 1 / 2 := by
    rw [abs_of_nonneg ht0]
    apply (div_le_iff₀ hH0).mpr
    linarith
  have hratio : H / D = (1 - t)⁻¹ := by
    have hi : 1 - t = D / H := by dsimp [t]; field_simp; ring
    rw [hi, inv_div]
  have hlogratio : |Real.log (H / D)| ≤ 2 / H := by
    rw [hratio, Real.log_inv, abs_neg]
    have hh := abs_log_one_sub_le hthalf
    rw [abs_of_nonneg ht0] at hh
    calc
      _ ≤ 2 * t := hh
      _ ≤ 2 * (1 / H) := mul_le_mul_of_nonneg_left ht1 (by norm_num)
      _ = _ := by ring
  have heq : d / D = p * (1 + e) * (H / D) := by dsimp [e]; field_simp; ring
  have hlog : Real.log (d / D) = Real.log p + Real.log (1 + e) + Real.log (H / D) := by
    rw [heq, Real.log_mul (mul_pos hp hepos).ne' (div_pos hH0 hD).ne',
      Real.log_mul hp.ne' hepos.ne']
  have heTaylor : |Real.log (1 + e) - e| ≤ 2 * e ^ 2 := by
    have hh := abs_log_one_sub_add_le (x := -e) (by simpa only [abs_neg] using hehalf)
    simpa only [sub_eq_add_neg, neg_neg, neg_sq] using hh
  have hdiff0 : 0 ≤ d / D - d / H := sub_nonneg.mpr
    (div_le_div_of_nonneg_left hd0.le hD hDhi)
  have hdiff : |d / D - d / H| ≤ 3 * p / H := by
    rw [abs_of_nonneg hdiff0]
    have hi : d / D - d / H = d * (H - D) / (D * H) := by field_simp
    rw [hi]
    apply (div_le_iff₀ (mul_pos hD hH0)).mpr
    have hi' : 3 * p / H * (D * H) = 3 * p * D := by field_simp
    rw [hi']
    have h1 := mul_le_mul_of_nonneg_left (show H - D ≤ 1 by linarith) hd0.le
    have h2 := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 3 * p)
    nlinarith only [h1, h2, hdhi]
  refine ⟨hq, by linarith, ?_, ?_⟩
  · change |Real.log (d / D) - Real.log p - e| ≤ _
    rw [hlog]
    have hh := abs_add_le (Real.log (1 + e) - e) (Real.log (H / D))
    have hi : Real.log p + Real.log (1 + e) + Real.log (H / D) - Real.log p - e =
        (Real.log (1 + e) - e) + Real.log (H / D) := by ring
    rw [hi]
    calc
      _ ≤ |Real.log (1 + e) - e| + |Real.log (H / D)| := hh
      _ ≤ 2 * e ^ 2 + 2 / H := add_le_add heTaylor hlogratio
      _ ≤ 2 * (L ^ 2 / (p * H)) + 2 / H :=
        add_le_add (mul_le_mul_of_nonneg_left hesq (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ = _ := by ring
  · have hTaylor := abs_log_one_sub_add_le hqhalf
    have hqSq := (sq_le_sq₀ hq.le (by positivity : 0 ≤ 3 * p)).mpr hq3
    have hh := abs_sub (Real.log (1 - d / D) + d / D) (d / D - d / H)
    have hi : Real.log (1 - d / D) + d / H =
        (Real.log (1 - d / D) + d / D) - (d / D - d / H) := by ring
    rw [hi]
    calc
      _ ≤ |Real.log (1 - d / D) + d / D| + |d / D - d / H| := hh
      _ ≤ 2 * (d / D) ^ 2 + 3 * p / H := add_le_add hTaylor hdiff
      _ ≤ 2 * (3 * p) ^ 2 + 3 * p / H :=
        add_le_add (mul_le_mul_of_nonneg_left hqSq (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ = _ := by ring

end MajorityDynamics.Probability.NeighborhoodBulk
