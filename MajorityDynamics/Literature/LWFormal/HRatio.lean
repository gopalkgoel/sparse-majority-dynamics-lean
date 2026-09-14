import MajorityDynamics.Literature.LWFormal.Approx
import MajorityDynamics.Literature.LWFormal.Close

set_option autoImplicit true

/-!
# (6.10): the real-variable estimate behind `H(d - e_a)/H(d - e_b) = R^gr_{ab}(d)(1 + O(1/n²))`

With `D = 2m/n`, `s = D^α`, `S2 = ∑ (dᵢ - D)²`, the exact ratio of the exponential factors is
`exp (Eexp n D dₐ d_b S2)`, and the binomial ratio is `dₐ(n - d_b)/(d_b(n - dₐ))`.
-/

namespace LW

open Real

/-- The exponent in `H̃(d - e_a)/H̃(d - e_b)`. -/
noncomputable def Eexp (n D da db S2 : ℝ) : ℝ :=
  (da - db) * (S2 - (da + db - 2 * D) + 1) / (D ^ 2 * (n - 1 - D) ^ 2)

set_option maxHeartbeats 4000000 in
theorem hratio_real {n : ℕ} {D s da db S2 : ℝ} (hn : (256 : ℝ) ≤ n) (hD : 32 ≤ D)
    (hDn : 8 * D ≤ n) (hs1 : 1 ≤ s) (hsD : 4 * s ≤ D) (hs3 : s ^ 3 ≤ D ^ 2)
    (hda : |da - D| ≤ s + 1) (hdb : |db - D| ≤ s + 1)
    (hS2 : 0 ≤ S2) (hS2' : S2 ≤ n * (s + 1) ^ 2) :
    Close (da / db * ((n - db) / (n - da)) * exp (Eexp n D da db S2))
      (rhoF ((da - (D + 1 / n)) / (D + 1 / n)) ((db - (D + 1 / n)) / (D + 1 / n))
        ((D + 1 / n) / (n - 1)) ((S2 - 1 / n) / n) (D + 1 / n) n) (5000 / (n : ℝ) ^ 2) := by
  unfold rhoF
  set n : ℝ := (n : ℝ) with hn_def
  set dbar := D + 1 / n with hdbar
  set T := n - 1 - D with hT
  set A := da - db with hA
  set B₁ := S2 - (da + db - 2 * D) + 1 with hB₁
  set B₂ := S2 - 1 / n with hB₂
  set C₁ := D ^ 2 * T ^ 2 with hC₁
  set C₂ := n ^ 2 * dbar ^ 2 * (1 - dbar / (n - 1)) ^ 2 with hC₂
  set E := Eexp n D da db S2 with hE
  have hE' : E = A * B₁ / C₁ := rfl
  -- basic bounds
  have hn0 : 0 < n := by linarith
  have hnn : 256 * n ≤ n * n := mul_le_mul_of_nonneg_right hn hn0.le
  have hnn2 : (65536 : ℝ) ≤ n ^ 2 := by
    calc (65536 : ℝ) = 256 ^ 2 := by norm_num
      _ ≤ n ^ 2 := pow_le_pow_left₀ (by norm_num) hn 2
  have h1n : 1 / n ≤ 1 / 256 := one_div_le_one_div_of_le (by norm_num) hn
  have h1n0 : 0 < 1 / n := by positivity
  have hda' := abs_le.1 hda
  have hdb' := abs_le.1 hdb
  have hda_lo : D / 2 ≤ da := by linarith
  have hda_hi : da ≤ 2 * D := by linarith
  have hdb_lo : D / 2 ≤ db := by linarith
  have hdb_hi : db ≤ 2 * D := by linarith
  have hda0 : 0 < da := by linarith
  have hdb0 : 0 < db := by linarith
  have hT_lo : 3 * n / 4 ≤ T := by rw [hT]; linarith
  have hT0 : 0 < T := by linarith
  have hnda : n / 2 ≤ n - da := by linarith
  have hndb : n / 2 ≤ n - db := by linarith
  have hnda0 : 0 < n - da := by linarith
  have hndb0 : 0 < n - db := by linarith
  have hdbar_pos : 0 < dbar := by rw [hdbar]; positivity
  have hn1 : 0 < n - 1 := by linarith
  have hμ : dbar / (n - 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ hn1, hdbar]; linarith
  have hμ0 : 0 < dbar / (n - 1) := by positivity
  have h1μ : 0 < 1 - dbar / (n - 1) := by linarith
  have hn1d : 0 < n - 1 - dbar := by rw [hdbar]; linarith
  have hD0 : 0 < D := by linarith
  have hC₁0 : 0 < C₁ := by positivity
  have hC₂0 : 0 < C₂ := by positivity
  have hs0 : 0 < s := by linarith
  have hT2 : 9 * n ^ 2 / 16 ≤ T ^ 2 := by
    calc 9 * n ^ 2 / 16 = (3 * n / 4) ^ 2 := by ring
      _ ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hT_lo 2
  have hT2D := mul_le_mul_of_nonneg_left hT2 (sq_nonneg D)
  have hn2D : 0 ≤ n ^ 2 * D ^ 2 := by positivity
  -- nonvanishing, for `field_simp`
  have hn0' : n ≠ 0 := hn0.ne'
  have hn1' : n - 1 ≠ 0 := hn1.ne'
  have hD0' : D ≠ 0 := hD0.ne'
  have hT0' : n - 1 - D ≠ 0 := hT0.ne'
  have hdbar' : dbar ≠ 0 := hdbar_pos.ne'
  have hda0' : da ≠ 0 := hda0.ne'
  have hdb0' : db ≠ 0 := hdb0.ne'
  have hnda' : n - da ≠ 0 := hnda0.ne'
  have hndb' : n - db ≠ 0 := hndb0.ne'
  have h1μ' : 1 - dbar / (n - 1) ≠ 0 := h1μ.ne'
  have hn1d' : n - 1 - dbar ≠ 0 := hn1d.ne'
  -- sizes of `A`, `B₁`, `B₂`
  have hAs : |A| ≤ 4 * s := by
    rw [hA]
    calc |da - db| ≤ |da - D| + |D - db| := abs_sub_le _ _ _
      _ ≤ 4 * s := by rw [abs_sub_comm D]; linarith
  have hs2 : (s + 1) ^ 2 ≤ 4 * s ^ 2 := by
    calc (s + 1) ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ = 4 * s ^ 2 := by ring
  have hns2 : n * (s + 1) ^ 2 ≤ 4 * n * s ^ 2 := by
    have := mul_le_mul_of_nonneg_left hs2 hn0.le; linarith
  have hs2' : s ≤ s ^ 2 := le_self_pow₀ hs1 two_ne_zero
  have hns : 5 * s ^ 2 ≤ n * s ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
  have hB₁s : |B₁| ≤ 5 * n * s ^ 2 := by
    rw [hB₁, abs_le]; constructor <;> linarith
  have hB₂s : |B₂| ≤ 5 * n * s ^ 2 := by
    rw [hB₂, abs_le]; constructor <;> linarith
  have hAB : ∀ B : ℝ, |B| ≤ 5 * n * s ^ 2 → |A * B| / C₁ ≤ 36 / n := by
    intro B hB
    have h1 : |A * B| ≤ 20 * n * D ^ 2 := by
      rw [abs_mul]
      calc |A| * |B| ≤ 4 * s * (5 * n * s ^ 2) :=
            mul_le_mul hAs hB (abs_nonneg _) (by positivity)
        _ = 20 * n * s ^ 3 := by ring
        _ ≤ 20 * n * D ^ 2 := by gcongr
    rw [div_le_div_iff₀ hC₁0 hn0]
    calc |A * B| * n ≤ 20 * n * D ^ 2 * n := mul_le_mul_of_nonneg_right h1 hn0.le
      _ ≤ 36 * C₁ := by rw [hC₁]; nlinarith only [hT2D, hn2D]
  -- (i) `|E| ≤ 36/n`
  have hEs : |E| ≤ 36 / n := by
    rw [hE', abs_div, abs_of_pos hC₁0]; exact hAB _ hB₁s
  have hE1 : |E| ≤ 1 := hEs.trans (by rw [div_le_one hn0]; linarith)
  have hexp : |exp E - 1 - E| ≤ 1296 / n ^ 2 := by
    refine (abs_exp_sub_one_sub_id_le hE1).trans ?_
    rw [← sq_abs]
    calc |E| ^ 2 ≤ (36 / n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hEs 2
      _ = 1296 / n ^ 2 := by ring
  -- (ii) `C₂ = C₁ (1 + O(1/n))`
  have hX : C₂ = C₁ * (((1 + 1 / (n * D)) * (1 - 1 / (n * T))) * (1 + 1 / (n - 1)) *
      (((1 + 1 / (n * D)) * (1 - 1 / (n * T))) * (1 + 1 / (n - 1)))) := by
    rw [hC₂, hC₁, hdbar, hT]; field_simp; ring
  have hsq : 256 * (1 / n * (1 / n)) ≤ 1 / n := by
    rw [show 256 * (1 / n * (1 / n)) = 256 / n * (1 / n) by ring]
    exact mul_le_of_le_one_left h1n0.le (by rw [div_le_one hn0]; exact hn)
  have hdiv : ∀ c : ℝ, c / n = c * (1 / n) := fun c => by ring
  have hC₂C₁ : Close C₂⁻¹ C₁⁻¹ (26 / n) := by
    have h1 : Close (1 + 1 / (n * D)) 1 (1 / n) := by
      unfold Close; rw [abs_one, mul_one, add_sub_cancel_left, abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le hn0 (le_mul_of_one_le_right hn0.le (by linarith))
    have h2 : Close (1 - 1 / (n * T)) 1 (1 / n) := by
      unfold Close; rw [abs_one, mul_one, sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le hn0 (le_mul_of_one_le_right hn0.le (by linarith))
    have h3 : Close (1 + 1 / (n - 1)) 1 (2 / n) := by
      unfold Close; rw [abs_one, mul_one, add_sub_cancel_left, abs_of_pos (by positivity)]
      rw [div_le_div_iff₀ hn1 hn0]; linarith
    have h12 := (h1.mul h2 h1n0.le).mono
      (show 1 / n + 1 / n + 1 / n * (1 / n) ≤ 3 / n by rw [hdiv 3]; linarith)
    rw [mul_one] at h12
    have h123 := (h12.mul h3 (by positivity)).mono
      (show 3 / n + 2 / n + 3 / n * (2 / n) ≤ 6 / n by
        have : 3 / n * (2 / n) = 6 * (1 / n * (1 / n)) := by ring
        rw [this, hdiv 3, hdiv 2, hdiv 6]; linarith)
    rw [mul_one] at h123
    have hXX := (h123.mul h123 (by positivity)).mono
      (show 6 / n + 6 / n + 6 / n * (6 / n) ≤ 13 / n by
        have : 6 / n * (6 / n) = 36 * (1 / n * (1 / n)) := by ring
        rw [this, hdiv 6, hdiv 13]; linarith)
    rw [mul_one] at hXX
    have := hXX.const_mul C₁
    rw [mul_one, ← hX] at this
    exact this.inv_le (by positivity) (by rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith)
      hC₁0.ne' (le_of_eq (by ring))
  -- (iii) `F3 - 1 = A B₂ / C₂` and `|E - (F3 - 1)| ≤ 939/n²`
  have hF3 : ((da - dbar) / dbar - (db - dbar) / dbar) * (B₂ / n) /
      ((1 - dbar / (n - 1)) ^ 2 * dbar * n) = A * B₂ / C₂ := by
    rw [hA, hC₂]; field_simp; ring
  have hdiff : |E - A * B₂ / C₂| ≤ 939 / n ^ 2 := by
    have hsplit : E - A * B₂ / C₂ = A * (B₁ - B₂) / C₁ + A * B₂ * (C₁⁻¹ - C₂⁻¹) := by
      rw [hE']; ring
    have hB₁₂ : |B₁ - B₂| ≤ 6 * s := by
      rw [hB₁, hB₂, abs_le]; constructor <;> linarith
    have ht1 : |A * (B₁ - B₂) / C₁| ≤ 3 / n ^ 2 := by
      rw [abs_div, abs_of_pos hC₁0, abs_mul, div_le_div_iff₀ hC₁0 (by positivity)]
      have h24 : |A| * |B₁ - B₂| ≤ 24 * s ^ 2 := by
        calc |A| * |B₁ - B₂| ≤ 4 * s * (6 * s) :=
              mul_le_mul hAs hB₁₂ (abs_nonneg _) (by positivity)
          _ = 24 * s ^ 2 := by ring
      have hs2D : 16 * s ^ 2 ≤ D ^ 2 := by
        calc 16 * s ^ 2 = (4 * s) ^ 2 := by ring
          _ ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hsD 2
      have hs2Dn := mul_le_mul_of_nonneg_right hs2D (sq_nonneg n)
      calc |A| * |B₁ - B₂| * n ^ 2 ≤ 24 * s ^ 2 * n ^ 2 :=
            mul_le_mul_of_nonneg_right h24 (by positivity)
        _ ≤ 3 * C₁ := by rw [hC₁]; nlinarith only [hT2D, hs2Dn, hn2D]
    have ht2 : |A * B₂ * (C₁⁻¹ - C₂⁻¹)| ≤ 936 / n ^ 2 := by
      rw [abs_mul]
      have h1 := hAB _ hB₂s
      have h2 : |C₁⁻¹ - C₂⁻¹| ≤ 26 / n * C₁⁻¹ := by
        have := hC₂C₁; unfold Close at this
        rw [abs_of_pos (inv_pos.2 hC₁0), abs_sub_comm] at this; exact this
      calc |A * B₂| * |C₁⁻¹ - C₂⁻¹| ≤ |A * B₂| * (26 / n * C₁⁻¹) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = 26 / n * (|A * B₂| / C₁) := by ring
        _ ≤ 26 / n * (36 / n) := by gcongr
        _ = 936 / n ^ 2 := by ring
    rw [hsplit]
    calc |A * (B₁ - B₂) / C₁ + A * B₂ * (C₁⁻¹ - C₂⁻¹)| ≤ _ := abs_add_le _ _
      _ ≤ 3 / n ^ 2 + 936 / n ^ 2 := add_le_add ht1 ht2
      _ = 939 / n ^ 2 := by ring
  -- (iv) `Close (exp E) F3 (4500/n²)`
  have hn4 : 65536 * (1 / n ^ 2 * (1 / n ^ 2)) ≤ 1 / n ^ 2 := by
    rw [show 65536 * (1 / n ^ 2 * (1 / n ^ 2)) = 65536 / n ^ 2 * (1 / n ^ 2) by ring]
    exact mul_le_of_le_one_left (by positivity) (by rw [div_le_one (by positivity)]; exact hnn2)
  have hdiv2 : ∀ c : ℝ, c / n ^ 2 = c * (1 / n ^ 2) := fun c => by ring
  have hu0 : 0 < 1 / n ^ 2 := by positivity
  have hG3 : Close (exp E) (1 + A * B₂ / C₂) (4500 / n ^ 2) := by
    unfold Close
    have hnum : |exp E - (1 + A * B₂ / C₂)| ≤ 2235 / n ^ 2 := by
      calc |exp E - (1 + A * B₂ / C₂)| = |(exp E - 1 - E) + (E - A * B₂ / C₂)| := by ring_nf
        _ ≤ |exp E - 1 - E| + |E - A * B₂ / C₂| := abs_add_le _ _
        _ ≤ 1296 / n ^ 2 + 939 / n ^ 2 := add_le_add hexp hdiff
        _ = 2235 / n ^ 2 := by ring
    have hden : 1 / 2 ≤ |1 + A * B₂ / C₂| := by
      have h1 : |A * B₂ / C₂| ≤ |E| + |E - A * B₂ / C₂| := by
        calc |A * B₂ / C₂| = |E - (E - A * B₂ / C₂)| := by ring_nf
          _ ≤ _ := abs_sub _ _
      have h36 : 36 / n ≤ 36 / 256 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
      have h939 : 939 / n ^ 2 ≤ 939 / 65536 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnn2
      calc 1 / 2 ≤ |(1 : ℝ)| - |A * B₂ / C₂| := by rw [abs_one]; linarith
        _ ≤ |1 + A * B₂ / C₂| := by
          have := abs_sub_abs_le_abs_sub (1 : ℝ) (-(A * B₂ / C₂))
          rw [abs_neg, sub_neg_eq_add] at this; exact this
    have hden' := mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ 4500 / n ^ 2 by positivity)
    have : 0 ≤ 15 / n ^ 2 := by positivity
    calc |exp E - (1 + A * B₂ / C₂)| ≤ 2235 / n ^ 2 := hnum
      _ = 4500 / n ^ 2 * (1 / 2) - 15 / n ^ 2 := by ring
      _ ≤ 4500 / n ^ 2 * |1 + A * B₂ / C₂| := by linarith
  -- (v) `Close G2 F2 (13/n²)`
  have hqa0 : n * (n / 2) ≤ n * (n - da) := mul_le_mul_of_nonneg_left hnda hn0.le
  have hqb0 : n * (n / 2) ≤ n * (n - db) := mul_le_mul_of_nonneg_left hndb hn0.le
  have hF2 : (n - db) / (n - da) =
      (1 - dbar / (n - 1) * (1 + (db - dbar) / dbar) + 1 / n) /
        (1 - dbar / (n - 1) * (1 + (da - dbar) / dbar) + 1 / n) *
      (1 - 1 / (n * (n - da))) * (1 - 1 / (n * (n - db)))⁻¹ := by
    have hqa : n * (n - da) - 1 ≠ 0 := by
      have : n * (n / 2) = n * n / 2 := by ring
      linarith
    have hqb : n * (n - db) - 1 ≠ 0 := by
      have : n * (n / 2) = n * n / 2 := by ring
      linarith
    have e1 : 1 - dbar / (n - 1) * (1 + (db - dbar) / dbar) + 1 / n =
        (n * (n - db) - 1) / (n * (n - 1)) := by field_simp; ring
    have e2 : 1 - dbar / (n - 1) * (1 + (da - dbar) / dbar) + 1 / n =
        (n * (n - da) - 1) / (n * (n - 1)) := by field_simp; ring
    have e3 : 1 - 1 / (n * (n - da)) = (n * (n - da) - 1) / (n * (n - da)) := by
      field_simp
    have e4 : 1 - 1 / (n * (n - db)) = (n * (n - db) - 1) / (n * (n - db)) := by
      field_simp
    rw [e1, e2, e3, e4]
    field_simp
  have hG2 : Close ((n - db) / (n - da))
      ((1 - dbar / (n - 1) * (1 + (db - dbar) / dbar) + 1 / n) /
        (1 - dbar / (n - 1) * (1 + (da - dbar) / dbar) + 1 / n)) (13 / n ^ 2) := by
    have hqa : 1 / (n * (n - da)) ≤ 2 / n ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hn0 hnda0) (by positivity)]
      have : n * (n / 2) = n ^ 2 / 2 := by ring
      linarith
    have hqb : 1 / (n * (n - db)) ≤ 2 / n ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hn0 hndb0) (by positivity)]
      have : n * (n / 2) = n ^ 2 / 2 := by ring
      linarith
    have h1 : Close (1 - 1 / (n * (n - da))) 1 (4 / n ^ 2) := by
      have := Close.one_sub (q := 1 / (n * (n - da))) (q' := 0) (x := 2 / n ^ 2)
        (by rwa [sub_zero, abs_of_pos (one_div_pos.2 (mul_pos hn0 hnda0))]) (by norm_num)
      rwa [sub_zero, show 2 * (2 / n ^ 2) = 4 / n ^ 2 by ring] at this
    have h2 : Close (1 - 1 / (n * (n - db)))⁻¹ 1 (8 / n ^ 2) := by
      have := Close.one_sub (q := 1 / (n * (n - db))) (q' := 0) (x := 2 / n ^ 2)
        (by rwa [sub_zero, abs_of_pos (one_div_pos.2 (mul_pos hn0 hndb0))]) (by norm_num)
      rw [sub_zero] at this
      have h4 : 2 * (2 / n ^ 2) ≤ 1 / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have := this.inv_le (by positivity) h4 one_ne_zero le_rfl
      rwa [inv_one, show 2 * (2 * (2 / n ^ 2)) = 8 / n ^ 2 by ring] at this
    rewrite [hF2]
    have := ((Close.refl ((1 - dbar / (n - 1) * (1 + (db - dbar) / dbar) + 1 / n) /
        (1 - dbar / (n - 1) * (1 + (da - dbar) / dbar) + 1 / n)) le_rfl).mul h1 le_rfl).mul h2
      (by positivity)
    simp only [zero_add, zero_mul, add_zero, mul_one] at this
    refine this.mono ?_
    have : 4 / n ^ 2 * (8 / n ^ 2) = 32 * (1 / n ^ 2 * (1 / n ^ 2)) := by ring
    rw [this, hdiv2 4, hdiv2 8, hdiv2 13]; linarith
  -- assemble
  have hF1 : da / db = (1 + (da - dbar) / dbar) / (1 + (db - dbar) / dbar) := by
    have e : ∀ x : ℝ, 1 + (x - dbar) / dbar = x / dbar := fun x => by field_simp; ring
    rw [e, e, div_div_div_cancel_right₀ hdbar']
  rewrite [hF3, ← hF1]
  have := ((Close.refl (da / db) le_rfl).mul hG2 le_rfl).mul hG3 (by positivity)
  simp only [zero_add, zero_mul, add_zero] at this
  refine this.mono ?_
  have : 13 / n ^ 2 * (4500 / n ^ 2) = 58500 * (1 / n ^ 2 * (1 / n ^ 2)) := by ring
  rw [this, hdiv2 13, hdiv2 4500, hdiv2 5000]; linarith

end LW
