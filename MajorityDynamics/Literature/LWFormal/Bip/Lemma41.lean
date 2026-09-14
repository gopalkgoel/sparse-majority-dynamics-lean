import MajorityDynamics.Literature.LWFormal.Bip.OpP
import MajorityDynamics.Literature.LWFormal.Bip.OpY
import MajorityDynamics.Literature.LWFormal.Lemma71

set_option autoImplicit true

/-!
# Lemma 4.1 (bipartite)

`badB_valid` instantiates `badB_expansion` at the shifted sequence `d - e_b` of an `S`-heavy `d`;
`lemma_4_1a` combines it with `ratioB_expansion`. `lemma_4_1b` instantiates `opPB_expansion`
at the shifts `d - e_v`, `d - e_b - e_v` of a balanced `d`, and `lemma_4_1c` instantiates
`opYB_expansion` at `d - e_a - e_v`.
-/

namespace LW.Bip

open Finset LW.TM

variable {ℓ n : ℕ}

/-- The scale `η = 2 D^{φ-1}` for `D ≥ 32`. -/
theorem eta_bounds {φ D : ℝ} (hφ₁ : 1 / 2 ≤ φ) (hφ₂ : φ < 3 / 5) (hD : 32 ≤ D) :
    0 < 2 * D ^ (φ - 1) ∧ 2 * D ^ (φ - 1) ≤ 2 * D ^ (-(2 / 5 : ℝ)) ∧ 2 * D ^ (φ - 1) ≤ 1 / 2 ∧
    (2 * D ^ (φ - 1)) ^ 2 = 4 * D ^ (2 * φ - 2) ∧ (2 * D ^ (φ - 1)) ^ 4 = 16 * D ^ (4 * φ - 4) := by
  have hDpos : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hηpos : 0 < D ^ (φ - 1) := Real.rpow_pos_of_pos hDpos _
  have hη25 : D ^ (φ - 1) ≤ D ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
  have hη12 : D ^ (φ - 1) ≤ 1 / 4 := by
    calc D ^ (φ - 1) ≤ D ^ (-(2 / 5 : ℝ)) := hη25
      _ ≤ (32 : ℝ) ^ (-(2 / 5 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hD (by norm_num)
      _ = (2 : ℝ) ^ (-2 : ℝ) := by
        rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      _ = 1 / 4 := by norm_num
  refine ⟨by positivity, by linarith, by linarith, ?_, ?_⟩
  · rw [mul_pow, ← Real.rpow_natCast (D ^ (φ - 1)), ← Real.rpow_mul hDpos.le]
    norm_num; congr 1; ring
  · rw [mul_pow, ← Real.rpow_natCast (D ^ (φ - 1)), ← Real.rpow_mul hDpos.le]
    norm_num; congr 1; ring

/-- The smallness bounds of one side at the common scale `η = 2 D^{φ-1}`, `D ≤ s̄`. -/
theorem side_bounds {k : ℕ} {φ D : ℝ} (hφ₁ : 1 / 2 ≤ φ) (hφ₂ : φ < 3 / 5) (hD : 32 ≤ D)
    {s : Seq k} (hDs : D ≤ dbar s) (hsp : ∀ i, |(s i : ℝ) - dbar s| ≤ 2 * dbar s ^ φ)
    (hk : (k : ℝ) ≠ 0) :
    (∀ i, |eps s i| ≤ 2 * D ^ (φ - 1)) ∧ 1 / dbar s ≤ (2 * D ^ (φ - 1)) ^ 2 ∧
    sigma2 s / dbar s ^ 2 ≤ (2 * D ^ (φ - 1)) ^ 2 := by
  have hDpos : 0 < D := by linarith
  have hspos : 0 < dbar s := by linarith
  have hs0 : dbar s ≠ 0 := hspos.ne'
  have hs1 : 1 ≤ dbar s := by linarith
  have hmono : dbar s ^ (φ - 1) ≤ D ^ (φ - 1) :=
    Real.rpow_le_rpow_of_nonpos hDpos hDs (by linarith)
  have hmono2 : dbar s ^ (2 * φ - 2) ≤ D ^ (2 * φ - 2) :=
    Real.rpow_le_rpow_of_nonpos hDpos hDs (by linarith)
  obtain ⟨-, -, -, hη2, -⟩ := eta_bounds hφ₁ hφ₂ hD
  have hε : ∀ i, |eps s i| ≤ 2 * D ^ (φ - 1) := fun i => by
    rw [eps, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    calc |(s i : ℝ) - dbar s| ≤ 2 * dbar s ^ φ := hsp i
      _ = 2 * dbar s ^ (φ - 1) * dbar s := by
        rw [Real.rpow_sub_one hs0, mul_assoc, div_mul_cancel₀ _ hs0]
      _ ≤ 2 * D ^ (φ - 1) * dbar s := by gcongr
  have hs2 : dbar s ^ (2 * φ - 2) = (dbar s ^ (φ - 1)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hspos.le]; congr 1; push_cast; ring
  refine ⟨hε, ?_, ?_⟩
  · rw [hη2]
    calc 1 / dbar s = dbar s ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ dbar s ^ (2 * φ - 2) := Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
      _ ≤ D ^ (2 * φ - 2) := hmono2
      _ ≤ 4 * D ^ (2 * φ - 2) := by
        have := Real.rpow_pos_of_pos hDpos (2 * φ - 2); linarith
  · rw [hη2, div_le_iff₀ (by positivity)]
    calc sigma2 s ≤ (2 * dbar s ^ φ) ^ 2 := sigma2_le s hk hsp
      _ = 4 * dbar s ^ (2 * φ - 2) * dbar s ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast (dbar s ^ φ), ← Real.rpow_mul hspos.le,
          ← Real.rpow_natCast (dbar s) 2, mul_assoc, ← Real.rpow_add hspos]
        norm_num; ring_nf
      _ ≤ 4 * D ^ (2 * φ - 2) * dbar s ^ 2 := by gcongr

/-- `bad(P*,Y*)_{ab}(d - e_b)/μ` expanded in the parameters of `d`, where
`1/n = μ/s̄ (1+c')`, `1/ℓ = μ/t̄ (1-c')`. -/
theorem badB_valid : ∃ bF : Bd, ∀ {ℓ n : ℕ} (d : BSeq ℓ n) (a b : Fin ℓ) (η c' : ℝ), a ≠ b →
    0 < η → η ≤ 1 / 2 → 2 ≤ dbar d.1 → 2 ≤ dbar d.2 → 0 < mu d → mu d ≤ 1 / 4 →
    (∀ i, |eps d.1 i| ≤ η) → (∀ v, |eps d.2 v| ≤ η) →
    1 / dbar d.1 ≤ η ^ 2 → 1 / dbar d.2 ≤ η ^ 2 →
    sigma2 d.1 / dbar d.1 ^ 2 ≤ η ^ 2 → sigma2 d.2 / dbar d.2 ^ 2 ≤ η ^ 2 →
    |c'| ≤ mu d * (1 / dbar d.1) * (1 / dbar d.2) →
    1 / (n : ℝ) = mu d * (1 / dbar d.1) * (1 + c') →
    1 / (ℓ : ℝ) = mu d * (1 / dbar d.2) * (1 - c') →
    Valid η 0 (bad Pst Yst a b (d - eS b) / mu d)
      (Pc.mk0 1 (eps d.1 b)
        (-(1 / dbar d.1) + 1 / dbar d.2 * mu d - 1 / dbar d.2 + sigma2 d.2 / dbar d.2 ^ 2)
        ((1 / dbar d.2 * mu d - 1 / dbar d.2 + sigma2 d.2 / dbar d.2 ^ 2) *
          (eps d.1 a * mu d + 2 * eps d.1 b * mu d - eps d.1 b) / (mu d - 1))) bF := by
  obtain ⟨bF, h⟩ := badB_expansion
  refine ⟨bF, fun {ℓ n} d a b η c' hab hη hη2 hs1 ht1 hμpos hμ hεS hεT hδS hδT htS htT hc' hνS hνT => ?_⟩
  have hs0 : dbar d.1 ≠ 0 := by linarith
  have ht0 : dbar d.2 ≠ 0 := by linarith
  have hℓ0 : (ℓ : ℝ) ≠ 0 := fun h0 => hs0 (by rw [dbar, h0, div_zero])
  have hn0 : (n : ℝ) ≠ 0 := fun h0 => ht0 (by rw [dbar, h0, div_zero])
  have hn : 0 < n := Nat.pos_of_ne_zero (by exact_mod_cast hn0)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast hℓ0)
  have hℓd : (ℓ : ℝ) * dbar d.1 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < ℓ * dbar d.1 - 1).ne'
  have h1 : dbar d.1 - 1 / ℓ ≠ 0 := fun h =>
    hℓd (by rw [sub_eq_zero] at h; rw [h, mul_one_div_cancel hℓ0, sub_self])
  have h2 : 1 - 1 / dbar d.1 * (1 / ℓ) ≠ 0 := fun h => hℓd (by
    have : 1 / dbar d.1 * (1 / ℓ) = 1 := by linarith
    field_simp at this; linarith)
  have hc'1 : 1 + c' ≠ 0 := by
    have h1 := (abs_le.1 hc').1
    have hs' : 1 / dbar d.1 ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    have ht' : 1 / dbar d.2 ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    have hs'0 : 0 ≤ 1 / dbar d.1 := div_nonneg zero_le_one (by linarith)
    have ht'0 : 0 ≤ 1 / dbar d.2 := div_nonneg zero_le_one (by linarith)
    have : mu d * (1 / dbar d.1) * (1 / dbar d.2) ≤ 1 / 4 * 1 * 1 :=
      mul_le_mul (mul_le_mul hμ hs' hs'0 (by norm_num)) ht' ht'0 (by norm_num)
    linarith
  have hμc : mu d * (1 + c') = dbar d.1 / n := by
    calc mu d * (1 + c') = mu d * (1 / dbar d.1) * (1 + c') * dbar d.1 := by field_simp
      _ = dbar d.1 / n := by rw [← hνS]; ring
  have hda : (((d - eS b).1 a : ℤ) : ℝ) = 1 / (1 / dbar d.1) * (1 + eps d.1 a) := by
    rw [sub_eS_fst, sub_e_apply, if_neg hab, sub_zero, eps]; field_simp; ring
  rw [bad_eq (d - eS b) hab, hda, sub_eS_snd]
  refine h η (mu d) (1 / dbar d.1) (1 / dbar d.2) (sigma2 d.1 / dbar d.1 ^ 2)
    (sigma2 d.2 / dbar d.2 ^ 2) ((∑ v, eps d.2 v ^ 3) / n) (eps d.1 a) (eps d.1 b) c' (1 / n)
    (1 / ℓ) n univ (eps d.2) _ _ _ _ _ hη hη2 hμpos hμ (by positivity) hδS (by positivity) hδT
    (div_nonneg (sigma2_nonneg _) (by positivity)) htS
    (div_nonneg (sigma2_nonneg _) (by positivity)) htT ?_ (hεS a) (hεS b) (fun v _ => hεT v)
    hc' hn (by simp) rfl hνS hνT (sum_eps _ hn0) (sum_eps_sq _ hn0 ht0) (by field_simp) ?_ ?_ ?_
    ?_ ?_
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n), div_le_iff₀ (by positivity)]
    simpa [mul_comm] using abs_sum_pow_three_le univ (eps d.2) fun v _ => hεT v
  · rw [mu_sub_eS]; linear_combination (-(1 / (ℓ : ℝ)) / 2) * hνS
  · rw [sub_eS_fst, eps_sub_e d.1 b a hℓ0 hs0 hℓd, if_neg hab]; ring
  · rw [sub_eS_fst, eps_sub_e d.1 b b hℓ0 hs0 hℓd, if_pos rfl]; ring
  · rw [sS, sub_eS_fst, sigma2_sub_e _ _ hℓ0, dbar_sub_e, hμc, eps]
    field_simp
    ring
  · rw [sT, sub_eS_snd, show sigma2 d.2 / (dbar d.2 * ℓ) = sigma2 d.2 / dbar d.2 * (1 / ℓ) by
      field_simp, hνT]
    field_simp

/-- `R*` factored as in `ratioD`. -/
theorem Rst_eq (d : BSeq ℓ n) (a b : Fin ℓ) {c' : ℝ} (hℓ0 : (ℓ : ℝ) ≠ 0) (ht0 : dbar d.2 ≠ 0)
    (hνT : 1 / (ℓ : ℝ) = mu d * (1 / dbar d.2) * (1 - c')) :
    Rst a b d = (1 + eps d.1 a) / (1 + eps d.1 b) *
      ((1 - mu d * (1 + eps d.1 b) + mu d * (1 / dbar d.1)) /
        (1 - mu d * (1 + eps d.1 a) + mu d * (1 / dbar d.1))) *
      (1 + mu d * Kfun (mu d) (1 / dbar d.2) (sigma2 d.2 / dbar d.2 ^ 2) c' (eps d.1 a)
        (eps d.1 b)) := by
  have hsT : sT d = sigma2 d.2 / dbar d.2 ^ 2 * (mu d * (1 - c')) := by
    rw [sT, show sigma2 d.2 / (dbar d.2 * ℓ) = sigma2 d.2 / dbar d.2 * (1 / ℓ) by field_simp, hνT]
    field_simp
  unfold Rst rhoB Kfun
  rw [hsT, hνT]
  ring

set_option maxHeartbeats 2000000 in
/-- Lemma 4.1(a): `ℛ(P*,Y*) = R* (1 + O(μ d̄^{4φ-4}))` on `S`-heavy sequences. -/
theorem lemma_4_1a (φ : ℝ) (hφ₁ : 1 / 2 ≤ φ) (hφ₂ : φ < 3 / 5) :
    ∃ C D₀ : ℝ, ∀ (ℓ n : ℕ) (d : BSeq ℓ n), D₀ ≤ dmin d → Spread φ d → SH d →
      ∀ a b, Close (opR Pst Yst a b d) (Rst a b d) (C * err41 φ d) := by
  obtain ⟨bF, hbF⟩ := badB_valid
  obtain ⟨bG, bD, hGD⟩ := ratioB_expansion bF
  set η₁ := min (1 / 2) (min (min bF.η₀ bG.η₀) (min bD.η₀ (9 / 16 / (2 * (bD.all + bD.R + 1)))))
    with hη₁
  refine ⟨16 * (32 / 9 * |bG.R|), max 32 ((η₁ / 2) ^ (-(5 / 2 : ℝ))),
    fun ℓ n d hD hS hSH a b => ?_⟩
  obtain ⟨hμ4, hspS, hspT⟩ := hS
  have hd32 : 32 ≤ dmin d := le_trans (le_max_left _ _) hD
  have hs32 : 32 ≤ dbar d.1 := le_trans hd32 (min_le_left _ _)
  have ht32 : 32 ≤ dbar d.2 := le_trans hd32 (min_le_right _ _)
  have hdpos : 0 < dmin d := by linarith
  have hs0 : dbar d.1 ≠ 0 := by linarith
  have ht0 : dbar d.2 ≠ 0 := by linarith
  have hℓ0 : (ℓ : ℝ) ≠ 0 := fun h0 => hs0 (by rw [dbar, h0, div_zero])
  have hn0 : (n : ℝ) ≠ 0 := fun h0 => ht0 (by rw [dbar, h0, div_zero])
  have hℓpos : (0 : ℝ) < ℓ := by positivity
  have hnpos : (0 : ℝ) < n := by positivity
  have hM : (M1 d.1 : ℝ) = M1 d.2 + 1 := by exact_mod_cast hSH
  have hT : (0 : ℝ) < M1 d.2 := by
    have : dbar d.2 * n = M1 d.2 := by rw [dbar]; field_simp
    nlinarith
  have hμpos : 0 < mu d := div_pos (by linarith) (by positivity)
  set c' : ℝ := 1 / ((M1 d.1 : ℝ) + M1 d.2) with hc'_def
  have hνS : 1 / (n : ℝ) = mu d * (1 / dbar d.1) * (1 + c') := by
    rw [hc'_def, mu, dbar, hM]; field_simp; ring
  have hνT : 1 / (ℓ : ℝ) = mu d * (1 / dbar d.2) * (1 - c') := by
    rw [hc'_def, mu, dbar, hM]; field_simp; ring
  have hc' : |c'| ≤ mu d * (1 / dbar d.1) * (1 / dbar d.2) := by
    have key : mu d * (1 / dbar d.1) * (1 / dbar d.2) =
        (2 * M1 d.2 + 1) / (2 * ((M1 d.2 : ℝ) + 1) * M1 d.2) := by
      rw [mu, dbar, dbar, hM]; field_simp; ring
    rw [key, hc'_def, hM, abs_of_pos (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hC0 : 0 ≤ 16 * (32 / 9 * |bG.R|) * err41 φ d := by
    unfold err41; have := Real.rpow_pos_of_pos hdpos (4 * φ - 4); positivity
  obtain ⟨hηpos, hη25, hη12, -, hη4⟩ := eta_bounds hφ₁ hφ₂ hd32
  obtain ⟨hεS, hδS, htS⟩ := side_bounds hφ₁ hφ₂ hd32 (min_le_left _ _) hspS hℓ0
  obtain ⟨hεT, hδT, htT⟩ := side_bounds hφ₁ hφ₂ hd32 (min_le_right _ _) hspT hn0
  set η := 2 * dmin d ^ (φ - 1) with hη
  have hεa := abs_le.1 (hεS a)
  have hεb := abs_le.1 (hεS b)
  have h1a : 0 < 1 + eps d.1 a := by linarith
  have h1b : 0 < 1 + eps d.1 b := by linarith
  have hda : (d.1 a : ℝ) = dbar d.1 * (1 + eps d.1 a) := by rw [eps]; field_simp; ring
  have hdb : (d.1 b : ℝ) = dbar d.1 * (1 + eps d.1 b) := by rw [eps]; field_simp; ring
  have hν0 : 0 ≤ mu d * (1 / dbar d.1) := by positivity
  have hA : 0 < 1 - mu d * (1 + eps d.1 a) + mu d * (1 / dbar d.1) := by
    have : mu d * (1 + eps d.1 a) ≤ 1 / 4 * (3 / 2) :=
      mul_le_mul hμ4.le (by linarith) h1a.le (by norm_num)
    linarith
  by_cases hab : a = b
  · subst hab
    have hR : opR Pst Yst a a d = 1 := by
      have : (d.1 a : ℝ) ≠ 0 := by rw [hda]; positivity
      simp [opR, bad, this]
    have hρ : Rst a a d = 1 := by
      simp only [Rst, rhoB, sub_self, zero_mul, zero_div, add_zero, mul_one]
      rw [div_self h1a.ne', div_self hA.ne', one_mul]
    rw [hR, hρ]; exact Close.refl 1 hC0
  have hFab := hbF d a b η c' hab hηpos hη12 (by linarith) (by linarith) hμpos hμ4.le hεS hεT hδS
    hδT htS htT hc' hνS hνT
  have hFba := hbF d b a η c' (Ne.symm hab) hηpos hη12 (by linarith) (by linarith) hμpos hμ4.le
    hεS hεT hδS hδT htS htT hc' hνS hνT
  obtain ⟨hGv, hDv⟩ := hGD η (mu d) (1 / dbar d.1) (1 / dbar d.2) (sigma2 d.2 / dbar d.2 ^ 2) c'
    (eps d.1 a) (eps d.1 b) _ _ hηpos hμpos hμ4.le (by positivity) hδS (by positivity) hδT
    (div_nonneg (sigma2_nonneg _) (by positivity)) htT (hεS a) (hεS b) hc' hFab hFba
  set Fab := bad Pst Yst a b (d - eS b) / mu d with hFab_def
  set Fba := bad Pst Yst b a (d - eS a) / mu d with hFba_def
  -- `η ≤ η₁`
  have hη₁pos : 0 < η₁ := by
    have := hDv.all_nonneg; have := hDv.R_nonneg
    simp only [hη₁, lt_min_iff]
    exact ⟨by norm_num, ⟨hFab.η₀_pos, hGv.η₀_pos⟩, hDv.η₀_pos, by positivity⟩
  have hηη₁ : η ≤ η₁ := eta_le hη₁pos hη25 (le_trans (le_max_right _ _) hD)
  simp only [hη₁, le_min_iff] at hηη₁
  obtain ⟨-, ⟨-, hG0⟩, hD0, hDL⟩ := hηη₁
  -- numerical bounds
  set G := ratioG (mu d) (1 / dbar d.1) (1 / dbar d.2) (sigma2 d.2 / dbar d.2 ^ 2) c' (eps d.1 a)
    (eps d.1 b) Fab Fba with hG
  set D := ratioD (mu d) (1 / dbar d.1) (1 / dbar d.2) (sigma2 d.2 / dbar d.2 ^ 2) c' (eps d.1 a)
    (eps d.1 b) Fba with hD_def
  have hGb : |G| ≤ |bG.R| * η ^ 4 := by
    have := hGv.rem hηpos hG0 (by simp [hηpos.le])
    rw [val_mk0_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hDb : 9 / 16 / 2 ≤ D :=
    hDv.lower (L := 9 / 16) (by show (9 : ℝ) / 16 ≤ (mu d - 1) ^ 2; nlinarith) hηpos
      (le_min_iff.2 ⟨hD0, hDL⟩) (by simp [hηpos.le])
  have hDpos : 0 < D := by linarith
  -- the exact identity `ℛ - R* = R* · μ · ratioG / ratioD`
  have e1 : bad Pst Yst a b (d - eS b) = mu d * Fab := by rw [hFab_def]; field_simp
  have e2 : bad Pst Yst b a (d - eS a) = mu d * Fba := by rw [hFba_def]; field_simp
  have hfac := hDpos.ne'
  rw [hD_def] at hfac
  unfold ratioD at hfac
  obtain ⟨⟨hf1, hf2⟩, hf3⟩ := mul_ne_zero_iff.1 hfac |>.imp_left mul_ne_zero_iff.1
  have hR : opR Pst Yst a b d =
      (1 + eps d.1 a) / (1 + eps d.1 b) * ((1 - mu d * Fab) / (1 - mu d * Fba)) := by
    rw [opR, e1, e2, hda, hdb]; field_simp
  have hkey : mu d * G =
      (1 - mu d * Fab) * (1 - mu d * (1 + eps d.1 a) + mu d * (1 / dbar d.1)) -
      (1 - mu d * Fba) * (1 - mu d * (1 + eps d.1 b) + mu d * (1 / dbar d.1)) *
        (1 + mu d * Kfun (mu d) (1 / dbar d.2) (sigma2 d.2 / dbar d.2 ^ 2) c' (eps d.1 a)
          (eps d.1 b)) := by
    rw [hG]; unfold ratioG; ring
  have hdiff : opR Pst Yst a b d - Rst a b d = Rst a b d * mu d * G / D := by
    rw [hR, Rst_eq d a b hℓ0 ht0 hνT, hD_def]
    unfold ratioD
    exact ratio_identity hA.ne' hf2 hf3 hf1 hkey
  rw [Close, hdiff, abs_div, abs_mul, abs_mul, abs_of_pos hμpos, abs_of_pos hDpos, err41,
    div_le_iff₀ hDpos]
  have hρ0 := abs_nonneg (Rst a b d)
  have hμη : 0 ≤ mu d * dmin d ^ (4 * φ - 4) := by positivity
  calc |Rst a b d| * mu d * |G| ≤ |Rst a b d| * mu d * (|bG.R| * η ^ 4) :=
        mul_le_mul_of_nonneg_left hGb (by positivity)
    _ = 16 * (32 / 9 * |bG.R|) * (mu d * dmin d ^ (4 * φ - 4)) * |Rst a b d| * (9 / 16 / 2) := by
        rw [hη4]; ring
    _ ≤ 16 * (32 / 9 * |bG.R|) * (mu d * dmin d ^ (4 * φ - 4)) * |Rst a b d| * D :=
        mul_le_mul_of_nonneg_left hDb (by positivity)

/-- The algebra behind `𝒫 - P* = P* · μ · G / D`. -/
theorem opPB_identity {S Qa G A ea ev μ L : ℝ} (hμ : μ ≠ 0) (hL : L ≠ 0)
    (hD : (1 + ea) * (1 + A) * (S / L) ≠ 0)
    (hG : 1 - Qa = μ * G + (1 + ea) * (1 + A) * (S / L)) :
    μ * L * (1 + ev) * (S / (1 - Qa))⁻¹ - μ * (1 + ea) * (1 + ev) * (1 + A) =
      μ * (1 + ea) * (1 + ev) * (1 + A) * μ * G / ((1 + ea) * (1 + A) * (S / L)) := by
  have hea : 1 + ea ≠ 0 := fun h => hD (by rw [h]; ring)
  have hA : 1 + A ≠ 0 := fun h => hD (by rw [h]; ring)
  have hS : S ≠ 0 := fun h => hD (by rw [h]; ring)
  rw [hG, inv_div]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- Lemma 4.1(b): `𝒫(P*,R*) = P* (1 + O(μ d̄^{4φ-4}))` on balanced sequences. -/
theorem lemma_4_1b (φ : ℝ) (hφ₁ : 1 / 2 ≤ φ) (hφ₂ : φ < 3 / 5) :
    ∃ C D₀ : ℝ, ∀ (ℓ n : ℕ) (d : BSeq ℓ n), D₀ ≤ dmin d → Spread φ d → Bal d →
      ∀ a v, Close (opP Pst Rst a v d) (Pst a v d) (C * err41 φ d) := by
  obtain ⟨bG, bD, hGD⟩ := opPB_expansion
  set η₁ := min (1 / 2) (min bG.η₀ (min bD.η₀ (3 / 4 / (2 * (bD.all + bD.R + 1))))) with hη₁
  refine ⟨16 * (8 / 3 * |bG.R|), max 32 ((η₁ / 2) ^ (-(5 / 2 : ℝ))),
    fun ℓ n d hD hS hB a v => ?_⟩
  obtain ⟨hμ4, hspS, hspT⟩ := hS
  have hd32 : 32 ≤ dmin d := le_trans (le_max_left _ _) hD
  have hs32 : 32 ≤ dbar d.1 := le_trans hd32 (min_le_left _ _)
  have ht32 : 32 ≤ dbar d.2 := le_trans hd32 (min_le_right _ _)
  have hdpos : 0 < dmin d := by linarith
  have hs0 : dbar d.1 ≠ 0 := by linarith
  have ht0 : dbar d.2 ≠ 0 := by linarith
  have hℓ0 : (ℓ : ℝ) ≠ 0 := fun h0 => hs0 (by rw [dbar, h0, div_zero])
  have hn0 : (n : ℝ) ≠ 0 := fun h0 => ht0 (by rw [dbar, h0, div_zero])
  have hℓpos : (0 : ℝ) < ℓ := by positivity
  have hnpos : (0 : ℝ) < n := by positivity
  have hℓ : 0 < ℓ := by exact_mod_cast hℓpos
  have hνS : 1 / (n : ℝ) = mu d * (1 / dbar d.1) := inv_n_of_bal hB hℓ0 hn0 hs0
  have hνT : 1 / (ℓ : ℝ) = mu d * (1 / dbar d.2) := inv_l_of_bal hB hℓ0 hn0 ht0
  have hμn : mu d = dbar d.1 / n := by
    rw [eq_div_iff hn0]; have := hνS; field_simp at this; linarith
  have hμℓ : mu d = dbar d.2 / ℓ := by
    rw [eq_div_iff hℓ0]; have := hνT; field_simp at this; linarith
  have hμpos : 0 < mu d := by rw [hμn]; positivity
  have hC0 : 0 ≤ 16 * (8 / 3 * |bG.R|) * err41 φ d := by
    unfold err41; have := Real.rpow_pos_of_pos hdpos (4 * φ - 4); positivity
  obtain ⟨hηpos, hη25, hη12, -, hη4⟩ := eta_bounds hφ₁ hφ₂ hd32
  obtain ⟨hεS, hδS, htS⟩ := side_bounds hφ₁ hφ₂ hd32 (min_le_left _ _) hspS hℓ0
  obtain ⟨hεT, hδT, htT⟩ := side_bounds hφ₁ hφ₂ hd32 (min_le_right _ _) hspT hn0
  set η := 2 * dmin d ^ (φ - 1) with hη
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hn0)
  have hℓd : (ℓ : ℝ) * dbar d.1 - 1 ≠ 0 := by
    have := mul_le_mul hℓ1 hs32 (by norm_num) hℓpos.le; linarith
  have hnd : (n : ℝ) * dbar d.2 - 1 ≠ 0 := by
    have := mul_le_mul hn1 ht32 (by norm_num) hnpos.le; linarith
  have hsTb : ∀ b, sT (d - eS b - eT v) = sT (d - eT v) := fun b => by
    simp only [sT, sub_eS_snd, sub_eT_snd]
  obtain ⟨hGv, hDv⟩ := hGD η (mu d) (1 / dbar d.1) (1 / dbar d.2) (sigma2 d.1 / dbar d.1 ^ 2)
    (sigma2 d.2 / dbar d.2 ^ 2) ((∑ b, eps d.1 b ^ 3) / ℓ) (eps d.1 a) (eps d.2 v) (1 / n) (1 / ℓ)
    (mu (d - eT v)) (mu (d - eS a - eT v)) (sT (d - eT v)) (eps (d.2 - e v) v) (sS d) (sT d) ℓ
    univ a (eps d.1) (fun b => eps (d.1 - e b) b) (fun b => sS (d - eS b - eT v))
    hηpos hη12 hμpos hμ4.le (by positivity) hδS (by positivity) hδT
    (div_nonneg (sigma2_nonneg _) (by positivity)) htS
    (div_nonneg (sigma2_nonneg _) (by positivity)) htT
    (by
      rw [abs_div, abs_of_pos hℓpos, div_le_iff₀ hℓpos]
      simpa [mul_comm] using abs_sum_pow_three_le univ (eps d.1) fun b _ => hεS b)
    (hεS a) (hεT v) (fun b _ => hεS b) hℓ (by simp) (mem_univ a) rfl hνS hνT
    (sum_eps _ hℓ0) (sum_eps_sq _ hℓ0 hs0) (by field_simp)
    (by rw [mu_sub_eT]; linear_combination (-(1 / (n : ℝ)) / 2) * hνT)
    (by rw [mu_sub_eS_sub_eT]; linear_combination (-(1 / (n : ℝ))) * hνT)
    (by
      rw [sT, sub_eT_snd, sigma2_sub_e _ _ hn0, dbar_sub_e, hμℓ, eps]
      field_simp
      ring)
    (by rw [eps_sub_e d.2 v v hn0 ht0 hnd, if_pos rfl]; ring)
    (fun b _ => by rw [eps_sub_e d.1 b b hℓ0 hs0 hℓd, if_pos rfl]; ring)
    (fun b _ => by
      rw [sS, sub_eT_fst, sub_eS_fst, sigma2_sub_e _ _ hℓ0, dbar_sub_e, hμn, eps]
      field_simp
      ring)
    (by rw [sS, hμn]; field_simp)
    (by rw [sT, hμℓ]; field_simp)
  -- `η ≤ η₁`
  have hη₁pos : 0 < η₁ := by
    have := hDv.all_nonneg; have := hDv.R_nonneg
    simp only [hη₁, lt_min_iff]
    exact ⟨by norm_num, hGv.η₀_pos, hDv.η₀_pos, by positivity⟩
  have hηη₁ : η ≤ η₁ := eta_le hη₁pos hη25 (le_trans (le_max_right _ _) hD)
  simp only [hη₁, le_min_iff] at hηη₁
  obtain ⟨-, hG0, hD0, hDL⟩ := hηη₁
  -- numerical bounds
  set Qa := piB (mu (d - eS a - eT v)) (sS (d - eS a - eT v)) (sT (d - eT v)) (eps (d.1 - e a) a)
    (eps (d.2 - e v) v) with hQa
  set S := ∑ b, pTermB (mu (d - eT v)) (1 / dbar d.1) (sT (d - eT v)) (1 / ℓ) (eps d.1 b)
    (eps d.1 a) (mu (d - eS a - eT v)) (sS (d - eS b - eT v)) (eps (d.1 - e b) b)
    (eps (d.2 - e v) v) with hS
  set D := pDenB (mu d) (sS d) (sT d) (eps d.1 a) (eps d.2 v) (S / ℓ) with hD_def
  set G := (1 - Qa - D) / mu d with hG
  have hGb : |G| ≤ |bG.R| * η ^ 4 := by
    have := hGv.rem hηpos hG0 (by simp [hηpos.le])
    rw [val_mk0_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hDb : 3 / 4 / 2 ≤ D :=
    hDv.lower (L := 3 / 4) (by show (3 : ℝ) / 4 ≤ 1 - mu d; linarith) hηpos
      (le_min_iff.2 ⟨hD0, hDL⟩) (by simp [hηpos.le])
  have hDpos : 0 < D := by linarith
  -- the exact identity `𝒫 - P* = P* · μ · G / D`
  have hterm : ∀ b, Rst b a (d - eT v) * (1 - Pst b v (d - eS b - eT v)) =
      pTermB (mu (d - eT v)) (1 / dbar d.1) (sT (d - eT v)) (1 / ℓ) (eps d.1 b) (eps d.1 a)
        (mu (d - eS a - eT v)) (sS (d - eS b - eT v)) (eps (d.1 - e b) b) (eps (d.2 - e v) v) :=
    fun b => by
      simp only [Rst, Pst, pTermB, sub_eT_fst, sub_eS_fst, sub_eS_snd, sub_eT_snd, hsTb,
        mu_sub_eS_sub_eT]
  have hQa' : Pst a v (d - eS a - eT v) = Qa := by
    simp only [Pst, hQa, sub_eT_fst, sub_eS_fst, sub_eS_snd, sub_eT_snd, hsTb]
  have hopP : opP Pst Rst a v d = (d.2 v : ℝ) * (S / (1 - Qa))⁻¹ := by
    rw [opP, ← sum_div, hQa', hS]
    congr 3
    exact sum_congr rfl fun b _ => hterm b
  have hPst : Pst a v d = mu d * (1 + eps d.1 a) * (1 + eps d.2 v) *
      (1 + AcorrB (mu d) (sS d) (sT d) (eps d.1 a) (eps d.2 v)) := rfl
  have hdv : (d.2 v : ℝ) = mu d * ℓ * (1 + eps d.2 v) := by
    rw [hμℓ, eps]; field_simp; ring
  have hD' : D = (1 + eps d.1 a) * (1 + AcorrB (mu d) (sS d) (sT d) (eps d.1 a) (eps d.2 v)) *
      (S / ℓ) := rfl
  have hG' : 1 - Qa = mu d * G + D := by rw [hG]; field_simp; ring
  have hdiff : opP Pst Rst a v d - Pst a v d = Pst a v d * mu d * G / D := by
    rw [hopP, hPst, hdv, hD']
    exact opPB_identity hμpos.ne' hℓ0 (hD' ▸ hDpos.ne') (hD' ▸ hG')
  rw [Close, hdiff, abs_div, abs_mul, abs_mul, abs_of_pos hμpos, abs_of_pos hDpos, err41,
    div_le_iff₀ hDpos]
  have hρ0 := abs_nonneg (Pst a v d)
  have hμη : 0 ≤ mu d * dmin d ^ (4 * φ - 4) := by positivity
  calc |Pst a v d| * mu d * |G| ≤ |Pst a v d| * mu d * (|bG.R| * η ^ 4) :=
        mul_le_mul_of_nonneg_left hGb (mul_nonneg hρ0 hμpos.le)
    _ = 16 * (8 / 3 * |bG.R|) * (mu d * dmin d ^ (4 * φ - 4)) * |Pst a v d| * (3 / 4 / 2) := by
        rw [hη4]; ring
    _ ≤ 16 * (8 / 3 * |bG.R|) * (mu d * dmin d ^ (4 * φ - 4)) * |Pst a v d| * D :=
        mul_le_mul_of_nonneg_left hDb (by positivity)

/-- The algebra behind `𝒴 - Y* = Y* · μ · G / D`. -/
theorem opYB_identity {P M M' N Yd Qa G D μ : ℝ} (hM : M' = M)
    (hD : D = Yd * (1 - Qa)) (hD0 : D ≠ 0) (hG : N = μ * G + D) :
    P * (M' * N) / (1 - Qa) - P * M * Yd = P * M * Yd * μ * G / D := by
  have hQ : 1 - Qa ≠ 0 := fun h => hD0 (by rw [hD, h, mul_zero])
  have hYd : Yd ≠ 0 := fun h => hD0 (by rw [hD, h, zero_mul])
  subst hM
  rw [hG, hD]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- Lemma 4.1(c): `𝒴(P*,Y*) = Y* (1 + O(μ d̄^{4φ-4}))` on balanced sequences. -/
theorem lemma_4_1c (φ : ℝ) (hφ₁ : 1 / 2 ≤ φ) (hφ₂ : φ < 3 / 5) :
    ∃ C D₀ : ℝ, ∀ (ℓ n : ℕ) (d : BSeq ℓ n), D₀ ≤ dmin d → Spread φ d → Bal d →
      ∀ a v b, a ≠ b → Close (opY Pst Yst a v b d) (Yst a v b d) (C * err41 φ d) := by
  obtain ⟨bG, bD, hGD⟩ := opYB_expansion
  set η₁ := min (1 / 2) (min bG.η₀ (min bD.η₀ (3 / 4 / (2 * (bD.all + bD.R + 1))))) with hη₁
  refine ⟨16 * (8 / 3 * |bG.R|), max 32 ((η₁ / 2) ^ (-(5 / 2 : ℝ))),
    fun ℓ n d hD hS hB a v b hab => ?_⟩
  obtain ⟨hμ4, hspS, hspT⟩ := hS
  have hd32 : 32 ≤ dmin d := le_trans (le_max_left _ _) hD
  have hs32 : 32 ≤ dbar d.1 := le_trans hd32 (min_le_left _ _)
  have ht32 : 32 ≤ dbar d.2 := le_trans hd32 (min_le_right _ _)
  have hdpos : 0 < dmin d := by linarith
  have hs0 : dbar d.1 ≠ 0 := by linarith
  have ht0 : dbar d.2 ≠ 0 := by linarith
  have hℓ0 : (ℓ : ℝ) ≠ 0 := fun h0 => hs0 (by rw [dbar, h0, div_zero])
  have hn0 : (n : ℝ) ≠ 0 := fun h0 => ht0 (by rw [dbar, h0, div_zero])
  have hℓpos : (0 : ℝ) < ℓ := by positivity
  have hnpos : (0 : ℝ) < n := by positivity
  have hνS : 1 / (n : ℝ) = mu d * (1 / dbar d.1) := inv_n_of_bal hB hℓ0 hn0 hs0
  have hνT : 1 / (ℓ : ℝ) = mu d * (1 / dbar d.2) := inv_l_of_bal hB hℓ0 hn0 ht0
  have hμn : mu d = dbar d.1 / n := by
    rw [eq_div_iff hn0]; have := hνS; field_simp at this; linarith
  have hμℓ : mu d = dbar d.2 / ℓ := by
    rw [eq_div_iff hℓ0]; have := hνT; field_simp at this; linarith
  have hμpos : 0 < mu d := by rw [hμn]; positivity
  obtain ⟨hηpos, hη25, hη12, -, hη4⟩ := eta_bounds hφ₁ hφ₂ hd32
  obtain ⟨hεS, hδS, htS⟩ := side_bounds hφ₁ hφ₂ hd32 (min_le_left _ _) hspS hℓ0
  obtain ⟨hεT, hδT, htT⟩ := side_bounds hφ₁ hφ₂ hd32 (min_le_right _ _) hspT hn0
  set η := 2 * dmin d ^ (φ - 1) with hη
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hℓ0)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hn0)
  have hℓd : (ℓ : ℝ) * dbar d.1 - 1 ≠ 0 := by
    have := mul_le_mul hℓ1 hs32 (by norm_num) hℓpos.le; linarith
  have hnd : (n : ℝ) * dbar d.2 - 1 ≠ 0 := by
    have := mul_le_mul hn1 ht32 (by norm_num) hnpos.le; linarith
  have ht1 : dbar d.2 - 1 / n ≠ 0 := fun h =>
    hnd (by rw [sub_eq_zero] at h; rw [h, mul_one_div_cancel hn0, sub_self])
  obtain ⟨hGv, hDv⟩ := hGD η (mu d) (1 / dbar d.1) (1 / dbar d.2) (sigma2 d.1 / dbar d.1 ^ 2)
    (sigma2 d.2 / dbar d.2 ^ 2) (eps d.1 a) (eps d.2 v) (eps d.1 b) (1 / n) (1 / ℓ)
    (mu (d - eS a - eT v)) (sS (d - eS a - eT v)) (sT (d - eS a - eT v)) (1 / dbar (d.2 - e v))
    (eps (d.1 - e a) a) (eps (d.2 - e v) v) (eps (d.1 - e a) b) (sS d) (sT d)
    hηpos hη12 hμpos hμ4.le (by positivity) hδS (by positivity) hδT
    (div_nonneg (sigma2_nonneg _) (by positivity)) htS
    (div_nonneg (sigma2_nonneg _) (by positivity)) htT (hεS a) (hεT v) (hεS b) hνS hνT
    (by rw [mu_sub_eS_sub_eT]; linear_combination (-(1 / (n : ℝ))) * hνT)
    (by
      rw [sS, sub_eT_fst, sub_eS_fst, sigma2_sub_e _ _ hℓ0, dbar_sub_e, hμn, eps]
      field_simp
      ring)
    (by
      rw [sT, sub_eT_snd, sub_eS_snd, sigma2_sub_e _ _ hn0, dbar_sub_e, hμℓ, eps]
      field_simp
      ring)
    (by rw [dbar_sub_e]; field_simp)
    (by rw [eps_sub_e d.1 a a hℓ0 hs0 hℓd, if_pos rfl]; ring)
    (by rw [eps_sub_e d.2 v v hn0 ht0 hnd, if_pos rfl]; ring)
    (by rw [eps_sub_e d.1 a b hℓ0 hs0 hℓd, if_neg hab.symm]; ring)
    (by rw [sS, hμn]; field_simp)
    (by rw [sT, hμℓ]; field_simp)
  -- `η ≤ η₁`
  have hη₁pos : 0 < η₁ := by
    have := hDv.all_nonneg; have := hDv.R_nonneg
    simp only [hη₁, lt_min_iff]
    exact ⟨by norm_num, hGv.η₀_pos, hDv.η₀_pos, by positivity⟩
  have hηη₁ : η ≤ η₁ := eta_le hη₁pos hη25 (le_trans (le_max_right _ _) hD)
  simp only [hη₁, le_min_iff] at hηη₁
  obtain ⟨-, hG0, hD0, hDL⟩ := hηη₁
  -- numerical bounds
  set N := yNumB (mu (d - eS a - eT v)) (sS (d - eS a - eT v)) (sT (d - eS a - eT v))
    (1 / dbar (d.2 - e v)) (eps (d.1 - e a) a) (eps (d.2 - e v) v) (eps (d.1 - e a) b) with hN
  set D := yDenB (mu d) (sS d) (sT d) (1 / dbar d.2) (eps d.1 a) (eps d.2 v) (eps d.1 b)
    (mu (d - eS a - eT v)) (sS (d - eS a - eT v)) (sT (d - eS a - eT v)) (eps (d.1 - e a) a)
    (eps (d.2 - e v) v) with hD_def
  set G := (N - D) / mu d with hG
  have hGb : |G| ≤ |bG.R| * η ^ 4 := by
    have := hGv.rem hηpos hG0 (by simp [hηpos.le])
    rw [val_mk0_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hDb : 3 / 4 / 2 ≤ D :=
    hDv.lower (L := 3 / 4) (by show (3 : ℝ) / 4 ≤ 1 - mu d; linarith) hηpos
      (le_min_iff.2 ⟨hD0, hDL⟩) (by simp [hηpos.le])
  have hDpos : 0 < D := by linarith
  -- the exact identity `𝒴 - Y* = Y* · μ · G / D`
  have hnum : Pst b v (d - eS a - eT v) - Yst a v b (d - eS a - eT v) =
      mu (d - eS a - eT v) * (1 + eps (d.1 - e a) b) * N := by
    simp only [Pst, Yst, hN, yNumB, piB, sub_eS_fst, sub_eT_fst, sub_eS_snd, sub_eT_snd]
    ring
  have hopY : opY Pst Yst a v b d =
      Pst a v d * (mu (d - eS a - eT v) * (1 + eps (d.1 - e a) b) * N) /
        (1 - piB (mu (d - eS a - eT v)) (sS (d - eS a - eT v)) (sT (d - eS a - eT v))
          (eps (d.1 - e a) a) (eps (d.2 - e v) v)) := by
    rw [opY, hnum]
    simp only [Pst, sub_eS_fst, sub_eT_fst, sub_eS_snd, sub_eT_snd]
  have hYst : Yst a v b d = Pst a v d * (mu d * (1 + eps d.1 b)) *
      ((1 + eps d.2 v - 1 / dbar d.2) *
        (1 + AcorrB (mu d) (sS d) (sT d) (eps d.1 b) (eps d.2 v - 1 / dbar d.2)) *
        (1 + TcB (mu d) (1 / dbar d.2) (eps d.1 a) (eps d.1 b))) := by
    simp only [Yst, piB]; ring
  have hM : mu (d - eS a - eT v) * (1 + eps (d.1 - e a) b) = mu d * (1 + eps d.1 b) := by
    have h2 : 1 - 1 / dbar d.1 / ℓ ≠ 0 := fun h => hℓd (by
      have : 1 / dbar d.1 / ℓ = 1 := by linarith
      field_simp at this; linarith)
    have hx : (1 + eps (d.1 - e a) b) * (1 - 1 / dbar d.1 / ℓ) = 1 + eps d.1 b := by
      have h4 : dbar d.1 * ℓ - 1 ≠ 0 := by rwa [mul_comm]
      rw [eps_sub_e d.1 a b hℓ0 hs0 hℓd, if_neg hab.symm]; field_simp; ring
    have hm : mu (d - eS a - eT v) = mu d * (1 - 1 / dbar d.1 / ℓ) := by
      rw [mu_sub_eS_sub_eT]; linear_combination (-(1 / (ℓ : ℝ))) * hνS
    rw [hm, ← hx]; ring
  have hD' : D = (1 + eps d.2 v - 1 / dbar d.2) *
      (1 + AcorrB (mu d) (sS d) (sT d) (eps d.1 b) (eps d.2 v - 1 / dbar d.2)) *
      (1 + TcB (mu d) (1 / dbar d.2) (eps d.1 a) (eps d.1 b)) *
      (1 - piB (mu (d - eS a - eT v)) (sS (d - eS a - eT v)) (sT (d - eS a - eT v))
        (eps (d.1 - e a) a) (eps (d.2 - e v) v)) := rfl
  have hG' : N = mu d * G + D := by rw [hG]; field_simp; ring
  have hdiff : opY Pst Yst a v b d - Yst a v b d = Yst a v b d * mu d * G / D := by
    rw [hopY, hYst]
    exact opYB_identity hM hD' hDpos.ne' hG'
  rw [Close, hdiff, abs_div, abs_mul, abs_mul, abs_of_pos hμpos, abs_of_pos hDpos, err41,
    div_le_iff₀ hDpos]
  have hρ0 := abs_nonneg (Yst a v b d)
  have hμη : 0 ≤ mu d * dmin d ^ (4 * φ - 4) := by positivity
  calc |Yst a v b d| * mu d * |G| ≤ |Yst a v b d| * mu d * (|bG.R| * η ^ 4) :=
        mul_le_mul_of_nonneg_left hGb (mul_nonneg hρ0 hμpos.le)
    _ = 16 * (8 / 3 * |bG.R|) * (mu d * dmin d ^ (4 * φ - 4)) * |Yst a v b d| * (3 / 4 / 2) := by
        rw [hη4]; ring
    _ ≤ 16 * (8 / 3 * |bG.R|) * (mu d * dmin d ^ (4 * φ - 4)) * |Yst a v b d| * D :=
        mul_le_mul_of_nonneg_left hDb (by positivity)

end LW.Bip
