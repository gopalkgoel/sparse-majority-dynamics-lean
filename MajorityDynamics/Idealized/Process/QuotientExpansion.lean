import MajorityDynamics.Idealized.Process.Basic

/-! A quantitative second-order quotient expansion for the edge template. -/
noncomputable section
namespace MajorityDynamics.Idealized.Process

/-- The perturbation parameter is explicit and no asymptotic conclusion is
assumed. This estimate is uniform in the three varying residual errors. -/
theorem quotient_linear_error {h δ B K e f m dx dy dz : ℝ}
    (hh : 0 ≤ h) (_hh1 : h ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsq : h ^ 2 ≤ δ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (he : |e| ≤ B) (hf : |f| ≤ B) (hm : |m| ≤ B)
    (hx : |dx| ≤ K * δ) (hy : |dy| ≤ K * δ) (hz : |dz| ≤ K * δ)
    (hden : 1 / 2 ≤ |1 + m * h + dz|) :
    |(1 + e * h + dx) * (1 + f * h + dy) / (1 + m * h + dz) -
      (1 + (e + f - m) * h)| ≤
        2 * (4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) * δ := by
  have hd0 : 0 < |1 + m * h + dz| := by linarith
  have hd : 1 + m * h + dz ≠ 0 := abs_pos.mp hd0
  have hcross : h * δ ≤ δ := by nlinarith
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hterm {a da : ℝ} (ha : |a| ≤ B) (hda : |da| ≤ K * δ) :
      |a * h + da| ≤ B * h + K * δ := by
    calc
      _ ≤ |a * h| + |da| := abs_add_le _ _
      _ ≤ B * h + K * δ := by
        rw [abs_mul, abs_of_nonneg hh]
        exact add_le_add (mul_le_mul_of_nonneg_right ha hh) hda
  have hproduct : |(e * h + dx) * (f * h + dy)| ≤
      (B ^ 2 + 2 * B * K + K ^ 2) * δ := by
    calc
      _ = |e * h + dx| * |f * h + dy| := abs_mul _ _
      _ ≤ (B * h + K * δ) * (B * h + K * δ) :=
        mul_le_mul (hterm he hx) (hterm hf hy) (abs_nonneg _) (by positivity)
      _ = B ^ 2 * h ^ 2 + (2 * B * K) * (h * δ) + K ^ 2 * δ ^ 2 := by ring
      _ ≤ B ^ 2 * δ + (2 * B * K) * δ + K ^ 2 * δ := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hsq (sq_nonneg B))
          (mul_le_mul_of_nonneg_left hcross (by positivity)))
          (mul_le_mul_of_nonneg_left hδsq (sq_nonneg K))
      _ = _ := by ring
  have hsum : |e + f - m| ≤ 3 * B := by
    calc
      _ ≤ |e + f| + |m| := abs_sub _ _
      _ ≤ (|e| + |f|) + |m| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  have hproduct' : |((e + f - m) * h) * (m * h + dz)| ≤
      (3 * B ^ 2 + 3 * B * K) * δ := by
    calc
      _ = (|e + f - m| * h) * |m * h + dz| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hh]
      _ ≤ (3 * B * h) * (B * h + K * δ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hsum hh) (hterm hm hz)
          (abs_nonneg _) (by positivity)
      _ = (3 * B ^ 2) * h ^ 2 + (3 * B * K) * (h * δ) := by ring
      _ ≤ (3 * B ^ 2) * δ + (3 * B * K) * δ :=
        add_le_add (mul_le_mul_of_nonneg_left hsq (by positivity))
          (mul_le_mul_of_nonneg_left hcross (by positivity))
      _ = _ := by ring
  have hlinear : |dx + dy - dz| ≤ 3 * K * δ := by
    calc
      _ ≤ |dx + dy| + |dz| := abs_sub _ _
      _ ≤ (|dx| + |dy|) + |dz| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  have hnum : |(1 + e * h + dx) * (1 + f * h + dy) -
      (1 + (e + f - m) * h) * (1 + m * h + dz)| ≤
        (4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) * δ := by
    have hid : (1 + e * h + dx) * (1 + f * h + dy) -
        (1 + (e + f - m) * h) * (1 + m * h + dz) =
        (dx + dy - dz) + (e * h + dx) * (f * h + dy) -
          ((e + f - m) * h) * (m * h + dz) := by ring
    rw [hid]
    calc
      _ ≤ |(dx + dy - dz) + (e * h + dx) * (f * h + dy)| +
          |((e + f - m) * h) * (m * h + dz)| := abs_sub _ _
      _ ≤ (|dx + dy - dz| + |(e * h + dx) * (f * h + dy)|) +
          |((e + f - m) * h) * (m * h + dz)| :=
            add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  have hid : (1 + e * h + dx) * (1 + f * h + dy) / (1 + m * h + dz) -
      (1 + (e + f - m) * h) =
      ((1 + e * h + dx) * (1 + f * h + dy) -
        (1 + (e + f - m) * h) * (1 + m * h + dz)) / (1 + m * h + dz) := by
    rw [div_sub' hd, mul_comm (1 + m * h + dz) (1 + (e + f - m) * h)]
  rw [hid, abs_div]
  calc
    _ ≤ ((4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) * δ) / (1 / 2) :=
      div_le_div₀ (by positivity) hnum (by norm_num) hden
    _ = _ := by ring

end MajorityDynamics.Idealized.Process
