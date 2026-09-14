import MajorityDynamics.Literature.LWFormal.Bip.Approx
import MajorityDynamics.Literature.LWFormal.Close

set_option autoImplicit true

/-!
# The exact `H`-ratio (34) versus `R*` (35), bipartite case

Real-variable core: for `u = (s - e_a, t)`, `v = (s - e_b, t)`,
`H(u)/H(v) = (s_a/s_b) ((n+1-s_b)/(n+1-s_a)) exp(EexpB)` and this is
`R*_{ab}(d)(1 + O(s²Φ²/m⁴ + sΦ/(m²ℓn) + s/(mn)))`, where `Φ ≥ ∑ (t_v - t̄)²`.
-/

namespace LW.Bip

open Real

/-- The exponent in `H̃(s - e_a, t)/H̃(s - e_b, t)`, with `F = ∑ (t_v - t̄)²`. -/
noncomputable def EexpB (ℓ n m sa sb F : ℝ) : ℝ :=
  (sb - sa) * (1 - F / (m * (1 - m / (ℓ * n)))) / (m * (1 - m / (ℓ * n)))

set_option maxHeartbeats 4000000 in
theorem bhratio_real {ℓ n m D s sa sb F Φ : ℝ} (hℓ : 576 ≤ ℓ) (hn : 576 ≤ n)
    (hm : m = D * ℓ) (hD1 : 1 ≤ D) (hμ : 2000 * m ≤ ℓ * n)
    (hs1 : 1 ≤ s) (hsD : 4 * s ≤ D) (hsa : |sa - 1 - D| ≤ s) (hsb : |sb - 1 - D| ≤ s)
    (hF0 : 0 ≤ F) (hFΦ : F ≤ Φ) (hmΦ : m ≤ Φ) (hsΦ : 100 * s * Φ ≤ m ^ 2) :
    Close (sa / sb * ((n + 1 - sb) / (n + 1 - sa)) * exp (EexpB ℓ n m sa sb F))
      (rhoB ((2 * m + 1) / (2 * ℓ * n)) (ℓ / (m + 1)) (F / (m * ℓ)) (1 / ℓ)
        ((sa - (m + 1) / ℓ) / ((m + 1) / ℓ)) ((sb - (m + 1) / ℓ) / ((m + 1) / ℓ)))
      (400 * (s ^ 2 * Φ ^ 2 / m ^ 4 + s * Φ / (m ^ 2 * ℓ * n) + s / (m * n))) := by
  unfold rhoB EexpB
  have hD4 : 4 ≤ D := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hn0 : 0 < n := by linarith
  have hm576 : 576 ≤ m := by rw [hm]; nlinarith
  have hm0 : 0 < m := by linarith
  have hℓn : 0 < ℓ * n := mul_pos hℓ0 hn0
  have hsa' := abs_le.1 hsa
  have hsb' := abs_le.1 hsb
  have hsa1 : 1 ≤ sa := by linarith
  have hsa2 : sa ≤ 2 * D := by linarith
  have hsb1 : 1 ≤ sb := by linarith
  have hsb2 : sb ≤ 2 * D := by linarith
  have hDn : 4 * D ≤ n := by
    have h1 : 2000 * D * ℓ ≤ n * ℓ := by rw [hm] at hμ; linarith
    have := le_of_mul_le_mul_right h1 hℓ0
    linarith
  have hnsa : n / 2 ≤ n + 1 - sa := by linarith
  have hnsb : n / 2 ≤ n + 1 - sb := by linarith
  have hnsa0 : 0 < n + 1 - sa := by linarith
  have hnsb0 : 0 < n + 1 - sb := by linarith
  have hsa0 : 0 < sa := by linarith
  have hsb0 : 0 < sb := by linarith
  have hs0 : 0 < s := by linarith
  have hΦ0 : 0 < Φ := by linarith
  have hΦm : 1 ≤ Φ / m := by rw [le_div_iff₀ hm0]; linarith
  have hΔ : |sb - sa| ≤ 2 * s := by rw [abs_le]; constructor <;> linarith
  have hA : s * Φ / m ^ 2 ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- densities
  set ν := m / (ℓ * n) with hν
  set μ := (2 * m + 1) / (2 * ℓ * n) with hμdef
  have hν0 : 0 ≤ ν := by positivity
  have hν1 : ν ≤ 1 / 1000 := by
    rw [hν, div_le_div_iff₀ hℓn (by norm_num)]; linarith
  have hμ0 : 0 ≤ μ := by positivity
  have hμ1 : μ ≤ 1 / 1000 := by
    rw [hμdef, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hμν : μ = ν + 1 / (2 * ℓ * n) := by rw [hμdef, hν]; field_simp
  have h1ν : 0 < 1 - ν := by linarith
  have h1μ : 0 < 1 - μ := by linarith
  have h1ν' : 1 - ν ≠ 0 := h1ν.ne'
  have h1μ' : 1 - μ ≠ 0 := h1μ.ne'
  have hm0' : m ≠ 0 := hm0.ne'
  have hm1' : m + 1 ≠ 0 := by linarith
  have hℓ0' : ℓ ≠ 0 := hℓ0.ne'
  have hn0' : n ≠ 0 := hn0.ne'
  have hm2 : m / (2 * ℓ * n) ≤ 1 / 4000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- the three reciprocals
  set a₁ := 1 / (m * (1 - ν)) with ha₁
  set a₂ := 1 / ((m + 1) * (1 - μ)) with ha₂
  set a₃ := 1 / (m * (1 - μ)) with ha₃
  have ha₁0 : 0 < a₁ := by positivity
  have ha₂0 : 0 < a₂ := by positivity
  have ha₃0 : 0 < a₃ := by positivity
  have ha₁m : a₁ ≤ 2 / m := by
    rw [ha₁, div_le_div_iff₀ (by positivity) hm0]
    nlinarith [mul_le_mul_of_nonneg_left hν1 hm0.le]
  have ha₂m : a₂ ≤ 2 / m := by
    rw [ha₂, div_le_div_iff₀ (by positivity) hm0]
    nlinarith [mul_le_mul_of_nonneg_left hμ1 hm0.le]
  have ha₃m : a₃ ≤ 2 / m := by
    rw [ha₃, div_le_div_iff₀ (by positivity) hm0]
    nlinarith [mul_le_mul_of_nonneg_left hμ1 hm0.le]
  have ha₁₂ : a₁ - a₂ = a₁ * a₂ * ((1 - μ) - m / (2 * ℓ * n)) := by
    have e : a₁ - a₂ = a₁ * a₂ * ((m + 1) * (1 - μ) - m * (1 - ν)) := by
      rw [ha₁, ha₂]; field_simp
    rw [e]; congr 1; linear_combination (-m) * hμν
  have ha₁₂' : |a₁ - a₂| ≤ 4 / m ^ 2 := by
    rw [ha₁₂, abs_mul, abs_mul, abs_of_pos ha₁0, abs_of_pos ha₂0]
    have h1 : |1 - μ - m / (2 * ℓ * n)| ≤ 1 := by
      have : 0 ≤ m / (2 * ℓ * n) := by positivity
      rw [abs_le]; constructor <;> linarith
    calc a₁ * a₂ * |1 - μ - m / (2 * ℓ * n)| ≤ 2 / m * (2 / m) * 1 := by gcongr
      _ = 4 / m ^ 2 := by ring
  have ha₁₃ : a₁ - a₃ = -(a₁ * a₃ * (m / (2 * ℓ * n))) := by
    have e : a₁ - a₃ = a₁ * a₃ * (m * (1 - μ) - m * (1 - ν)) := by
      rw [ha₁, ha₃]; field_simp
    rw [e, ← mul_neg]; congr 1; linear_combination (-m) * hμν
  have ha₁₃' : |a₁ - a₃| ≤ 2 / (m * ℓ * n) := by
    rw [ha₁₃, abs_neg, abs_mul, abs_mul, abs_of_pos ha₁0, abs_of_pos ha₃0,
      abs_of_pos (by positivity : 0 < m / (2 * ℓ * n))]
    calc a₁ * a₃ * (m / (2 * ℓ * n)) ≤ 2 / m * (2 / m) * (m / (2 * ℓ * n)) := by gcongr
      _ = 2 / (m * ℓ * n) := by field_simp
  have hsq : |a₁ ^ 2 - a₂ * a₃| ≤ 8 / m ^ 3 + 4 / (m ^ 2 * ℓ * n) := by
    have : a₁ ^ 2 - a₂ * a₃ = a₁ * (a₁ - a₂) + a₂ * (a₁ - a₃) := by ring
    rw [this]
    calc |a₁ * (a₁ - a₂) + a₂ * (a₁ - a₃)|
        ≤ |a₁ * (a₁ - a₂)| + |a₂ * (a₁ - a₃)| := abs_add_le _ _
      _ = a₁ * |a₁ - a₂| + a₂ * |a₁ - a₃| := by
          rw [abs_mul, abs_mul, abs_of_pos ha₁0, abs_of_pos ha₂0]
      _ ≤ 2 / m * (4 / m ^ 2) + 2 / m * (2 / (m * ℓ * n)) := by gcongr
      _ = 8 / m ^ 3 + 4 / (m ^ 2 * ℓ * n) := by field_simp; ring
  -- the exponent `y` and its linearisation `y'`
  set y := (sb - sa) * (1 - F / (m * (1 - ν))) / (m * (1 - ν)) with hy
  have hy' : y = (sb - sa) * ((1 - F * a₁) * a₁) := by rw [hy, ha₁]; ring
  set y' := (sb - sa) * ((1 - F * a₃) * a₂) with hy'def
  have hFa : ∀ a, 0 < a → a ≤ 2 / m → |1 - F * a| ≤ 3 * Φ / m := by
    intro a ha0 ham
    have h1 : F * a ≤ Φ * (2 / m) := mul_le_mul hFΦ ham ha0.le hΦ0.le
    have h2 : 0 ≤ F * a := by positivity
    have h3 : Φ * (2 / m) = 2 * (Φ / m) := by ring
    have h4 : 3 * Φ / m = 3 * (Φ / m) := by ring
    rw [abs_le]; constructor <;> linarith
  have hyb : |y| ≤ 12 * (s * Φ / m ^ 2) := by
    rw [hy', abs_mul, abs_mul, abs_of_pos ha₁0]
    calc |sb - sa| * (|1 - F * a₁| * a₁) ≤ 2 * s * (3 * Φ / m * (2 / m)) := by
          gcongr; exact hFa a₁ ha₁0 ha₁m
      _ = 12 * (s * Φ / m ^ 2) := by ring
  have hy'b : |y'| ≤ 12 * (s * Φ / m ^ 2) := by
    rw [hy'def, abs_mul, abs_mul, abs_of_pos ha₂0]
    calc |sb - sa| * (|1 - F * a₃| * a₂) ≤ 2 * s * (3 * Φ / m * (2 / m)) := by
          gcongr; exact hFa a₃ ha₃0 ha₃m
      _ = 12 * (s * Φ / m ^ 2) := by ring
  have hy1 : |y| ≤ 1 := by linarith
  have hyy' : |y - y'| ≤ 8 * (s / m ^ 2) + 16 * (s * Φ / m ^ 3) + 8 * (s * Φ / (m ^ 2 * ℓ * n)) := by
    have : y - y' = (sb - sa) * ((a₁ - a₂) - F * (a₁ ^ 2 - a₂ * a₃)) := by rw [hy', hy'def]; ring
    rw [this, abs_mul]
    have h1 : |(a₁ - a₂) - F * (a₁ ^ 2 - a₂ * a₃)| ≤
        4 / m ^ 2 + Φ * (8 / m ^ 3 + 4 / (m ^ 2 * ℓ * n)) := by
      calc |(a₁ - a₂) - F * (a₁ ^ 2 - a₂ * a₃)|
          ≤ |a₁ - a₂| + |F * (a₁ ^ 2 - a₂ * a₃)| := abs_sub _ _
        _ = |a₁ - a₂| + F * |a₁ ^ 2 - a₂ * a₃| := by rw [abs_mul, abs_of_nonneg hF0]
        _ ≤ 4 / m ^ 2 + Φ * (8 / m ^ 3 + 4 / (m ^ 2 * ℓ * n)) := by gcongr
    calc |sb - sa| * |(a₁ - a₂) - F * (a₁ ^ 2 - a₂ * a₃)|
        ≤ 2 * s * (4 / m ^ 2 + Φ * (8 / m ^ 3 + 4 / (m ^ 2 * ℓ * n))) := by gcongr
      _ = 8 * (s / m ^ 2) + 16 * (s * Φ / m ^ 3) + 8 * (s * Φ / (m ^ 2 * ℓ * n)) := by
          field_simp; ring
  -- absorb the lower-order terms into `A = s²Φ²/m⁴`
  have hA1 : s / m ^ 2 ≤ s ^ 2 * Φ ^ 2 / m ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : m ^ 2 ≤ s * Φ ^ 2 := by
      nlinarith [mul_le_mul hmΦ hmΦ hm0.le hΦ0.le,
        mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ Φ ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ s * m ^ 2)]
  have hA2 : s * Φ / m ^ 3 ≤ s ^ 2 * Φ ^ 2 / m ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : m ≤ s * Φ := by nlinarith [mul_le_mul hs1 hmΦ hm0.le hs0.le]
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ s * Φ * m ^ 3)]
  -- `exp y ≈ 1 + y'`
  have hG3 : Close (exp y) (1 + y')
      (336 * (s ^ 2 * Φ ^ 2 / m ^ 4) + 16 * (s * Φ / (m ^ 2 * ℓ * n))) := by
    have he := abs_exp_sub_one_sub_id_le hy1
    have hy2 : |y| ^ 2 ≤ 144 * (s ^ 2 * Φ ^ 2 / m ^ 4) := by
      calc |y| ^ 2 ≤ (12 * (s * Φ / m ^ 2)) ^ 2 := by gcongr
        _ = 144 * (s ^ 2 * Φ ^ 2 / m ^ 4) := by ring
    have h12 : 1 / 2 ≤ |1 + y'| := by
      have := (abs_le.1 hy'b).1
      exact le_abs.2 (Or.inl (by linarith))
    unfold Close
    have : |exp y - (1 + y')| ≤ |exp y - 1 - y| + |y - y'| := by
      have : exp y - (1 + y') = (exp y - 1 - y) + (y - y') := by ring
      rw [this]; exact abs_add_le _ _
    have hnn : 0 ≤ 336 * (s ^ 2 * Φ ^ 2 / m ^ 4) + 16 * (s * Φ / (m ^ 2 * ℓ * n)) := by positivity
    have hprod := mul_le_mul_of_nonneg_left h12 hnn
    have hy2' : y ^ 2 ≤ 144 * (s ^ 2 * Φ ^ 2 / m ^ 4) := by rw [← sq_abs]; exact hy2
    linarith
  -- the binomial-ratio factor
  set Aa := 2 * (m + 1) * (n + 1 - sa) + (sa - 1) with hAa
  set Ab := 2 * (m + 1) * (n + 1 - sb) + (sb - 1) with hAb
  have hAa0 : 0 < Aa := by rw [hAa]; nlinarith
  have hAb0 : 0 < Ab := by rw [hAb]; nlinarith
  have hAb' : m * n ≤ Ab := by rw [hAb]; nlinarith
  have hAa' : Aa ≠ 0 := hAa0.ne'
  have hnsa' : n + 1 - sa ≠ 0 := hnsa0.ne'
  have e0 : ∀ c, 1 + (c - (m + 1) / ℓ) / ((m + 1) / ℓ) = c * ℓ / (m + 1) := by
    intro c; field_simp; ring
  have e1 : ∀ c, 1 - μ * (1 + (c - (m + 1) / ℓ) / ((m + 1) / ℓ)) + μ * (ℓ / (m + 1)) =
      (2 * (m + 1) * (n + 1 - c) + (c - 1)) / (2 * n * (m + 1)) := by
    intro c; rw [e0, hμdef]; field_simp; ring
  have hF2 : (1 - μ * (1 + (sb - (m + 1) / ℓ) / ((m + 1) / ℓ)) + μ * (ℓ / (m + 1))) /
      (1 - μ * (1 + (sa - (m + 1) / ℓ) / ((m + 1) / ℓ)) + μ * (ℓ / (m + 1))) = Ab / Aa := by
    rw [e1, e1, hAa, hAb]
    exact div_div_div_cancel_right₀ (by positivity) _ _
  have hG2 : Close ((n + 1 - sb) / (n + 1 - sa)) (Ab / Aa) (16 * (s / (m * n))) := by
    unfold Close
    have h1 : (n + 1 - sb) / (n + 1 - sa) - Ab / Aa = (sa - sb) * n / ((n + 1 - sa) * Aa) := by
      rw [div_sub_div _ _ hnsa' hAa']
      congr 1
      rw [hAa, hAb]; ring
    have h2 : 16 * (s / (m * n)) * |Ab / Aa| * ((n + 1 - sa) * Aa) =
        16 * s * Ab * (n + 1 - sa) / (m * n) := by
      rw [abs_of_pos (div_pos hAb0 hAa0)]; field_simp
    rw [h1, abs_div, abs_mul, abs_of_pos hn0,
      abs_of_pos (mul_pos hnsa0 hAa0), div_le_iff₀ (mul_pos hnsa0 hAa0), h2,
      le_div_iff₀ (by positivity)]
    have hΔ' : |sa - sb| ≤ 2 * s := by rw [abs_sub_comm]; exact hΔ
    calc |sa - sb| * n * (m * n) ≤ 2 * s * n * (m * n) := by gcongr
      _ = 4 * s * (m * n * (n / 2)) := by ring
      _ ≤ 4 * s * (Ab * (n + 1 - sa)) := by gcongr
      _ ≤ 16 * s * Ab * (n + 1 - sa) := by nlinarith [mul_pos hAb0 hnsa0]
  have hF1 : (1 + (sa - (m + 1) / ℓ) / ((m + 1) / ℓ)) / (1 + (sb - (m + 1) / ℓ) / ((m + 1) / ℓ)) =
      sa / sb := by
    rw [e0, e0]; field_simp
  have hF3 : 1 + ((sa - (m + 1) / ℓ) / ((m + 1) / ℓ) - (sb - (m + 1) / ℓ) / ((m + 1) / ℓ)) *
      (F / (m * ℓ) / (1 - μ) - 1 / ℓ) / (1 - μ) = 1 + y' := by
    have e2 : (sa - (m + 1) / ℓ) / ((m + 1) / ℓ) - (sb - (m + 1) / ℓ) / ((m + 1) / ℓ) =
        (sa - sb) * ℓ / (m + 1) := by field_simp; ring
    rw [e2, hy'def, ha₂, ha₃]; field_simp; ring
  rw [hF1, hF2, hF3]
  have hmul := ((Close.refl (sa / sb) le_rfl).mul hG2 le_rfl).mul hG3 (by positivity)
  simp only [zero_add, zero_mul, add_zero] at hmul
  refine hmul.mono ?_
  have hB : s * Φ / (m ^ 2 * ℓ * n) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hsΦ (by positivity : (0 : ℝ) ≤ ℓ * n)]
  have hAA : s ^ 2 * Φ ^ 2 / m ^ 4 ≤ 1 / 10000 := by
    have : s ^ 2 * Φ ^ 2 / m ^ 4 = (s * Φ / m ^ 2) ^ 2 := by ring
    rw [this, sq]
    exact (mul_le_mul hA hA (by positivity) (by norm_num)).trans (by norm_num)
  have hE : 0 ≤ s / (m * n) := by positivity
  have hA0 : 0 ≤ s ^ 2 * Φ ^ 2 / m ^ 4 := by positivity
  have hB0 : 0 ≤ s * Φ / (m ^ 2 * ℓ * n) := by positivity
  have h1 : 336 * (s ^ 2 * Φ ^ 2 / m ^ 4) + 16 * (s * Φ / (m ^ 2 * ℓ * n)) ≤ 1 := by linarith
  linarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 16 * (s / (m * n)))]

end LW.Bip
