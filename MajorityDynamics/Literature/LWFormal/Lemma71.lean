import MajorityDynamics.Literature.LWFormal.Bad
import MajorityDynamics.Literature.LWFormal.OpP
import MajorityDynamics.Literature.LWFormal.Shift

set_option autoImplicit true

/-!
# Lemma 7.1

`bad_valid` instantiates `bad_expansion` at the actual shifted sequence `d - e_b`;
`lemma_7_1a` combines it with `ratio_expansion`. `lemma_7_1b` instantiates `opP_expansion`
at `d - e_v`, `d - e_b - e_v`, and `lemma_7_1c` instantiates `opY_expansion` at `d - e_a - e_v`.
-/

namespace LW

open Finset LW.TM

theorem val_mk0_zero (z : ℝ) : TM.val (Pc.mk0 0 0 0 0) z = 0 := by
  simp [TM.val, TM.grade, Pc.mk0, Pc.mk]

theorem abs_sum_pow_three_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {η : ℝ}
    (h : ∀ i ∈ s, |f i| ≤ η) : |∑ i ∈ s, f i ^ 3| ≤ s.card * η ^ 3 :=
  calc |∑ i ∈ s, f i ^ 3| ≤ ∑ i ∈ s, |f i ^ 3| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, η ^ 3 := sum_le_sum fun i hi => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h i hi) 3
    _ = s.card * η ^ 3 := by simp

/-- `bad(P^gr,Y^gr)_{ab}(d - e_b)/μ` expanded in the parameters of `d`. -/
theorem bad_valid : ∃ bF : Bd, ∀ {n : ℕ} (d : Seq n) (a b : Fin n) (η : ℝ), a ≠ b →
    0 < η → η ≤ 1 / 2 → 1 ≤ dbar d → mu d ≤ 1 / 4 → 3 ≤ n → (∀ i, |eps d i| ≤ η) →
    1 / dbar d ≤ η ^ 2 → sigma2 d / dbar d ^ 2 ≤ η ^ 2 →
    Valid η 0 (bad Pgr Ygr a b (d - e b) / mu d)
      (Pc.mk0 1 (eps d b) (-(1 / dbar d) + sigma2 d / dbar d ^ 2)
        (sigma2 d / dbar d ^ 2 * (eps d a * mu d + 2 * eps d b * mu d - eps d b) / (mu d - 1)))
      bF := by
  obtain ⟨bF, h⟩ := bad_expansion
  refine ⟨bF, fun {n} d a b η hab hη hη2 hd hμ hn hε hδ ht => ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hd0 : dbar d ≠ 0 := by linarith
  have hnd : (n : ℝ) * dbar d - 1 ≠ 0 := by nlinarith
  have h1 : dbar d - 1 / n ≠ 0 := fun h => hnd (by rw [sub_eq_zero] at h; rw [h]; field_simp; ring)
  have h2 : 1 - 1 / dbar d / n ≠ 0 := fun h => hnd (by
    have : 1 / dbar d / n = 1 := by linarith
    field_simp at this; linarith)
  have hμpos : 0 < mu d := div_pos (by linarith) (by linarith)
  have h3 : 1 + mu d * (1 / dbar d) ≠ 0 := by positivity
  have hmud : 1 / ((n : ℝ) - 1) = mu d * (1 / dbar d) := by rw [mu]; field_simp
  have hba : b ∈ univ.erase a := mem_erase.2 ⟨hab.symm, mem_univ b⟩
  have hcard : ((univ.erase a).erase b).card = n - 2 := by
    rw [card_erase_of_mem hba, card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]; omega
  have hsum : ∀ f : Fin n → ℝ, ∑ v ∈ (univ.erase a).erase b, f v = ∑ i, f i - f a - f b := by
    intro f
    rw [← add_sum_erase _ _ (mem_univ a), ← add_sum_erase _ _ hba]; ring
  have hdb : (1 : ℝ) / dbar (d - e b) = 1 / dbar d / (1 - 1 / dbar d / n) := by
    rw [dbar_sub_e]; field_simp
  have hda : (((d - e b) a : ℤ) : ℝ) = 1 / (1 / dbar d) * (1 + eps d a) := by
    rw [sub_e_apply, if_neg hab, sub_zero, eps]; field_simp; ring
  rw [bad_eq (d - e b) hab, hda]
  refine h η (mu d) (1 / dbar d) (sigma2 d / dbar d ^ 2) ((∑ i, eps d i ^ 3) / n) (eps d a)
    (eps d b) n _ (eps d) _ _ _ _ _ _ hη hη2 hμpos hμ (by positivity) hδ
    (div_nonneg (sigma2_nonneg d) (by positivity)) ht ?_
    (hε a) (hε b) (fun v _ => hε v) hn hcard hmud ?_ ?_ ?_ (mu_sub_e d b hn0 hd0) hdb ?_ ?_ ?_ ?_
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n), div_le_iff₀ (by positivity)]
    simpa [mul_comm] using abs_sum_pow_three_le univ (eps d) fun i _ => hε i
  · rw [hsum, sum_eps d hn0]; ring
  · rw [hsum, sum_eps_sq d hn0 hd0]
  · rw [hsum]; field_simp
  · rw [eps_sub_e d b a hn0 hd0 hnd, if_neg hab]; ring
  · rw [eps_sub_e d b b hn0 hd0 hnd, if_pos rfl]
  · intro v hv
    rw [eps_sub_e d b v hn0 hd0 hnd, if_neg (mem_erase.1 hv).1]; ring
  · rw [sigma2_sub_e d b hn0, dbar_sub_e, mu, eps]
    field_simp
    linear_combination
      (-(sigma2 d * n ^ 2 - 1 - 2 * n * d b + 2 * n * dbar d + n)) * mul_inv_cancel₀ hn0

/-- `R^gr` factored as in `ratioD`. -/
theorem Rgr_eq {n : ℕ} (d : Seq n) (a b : Fin n) (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (hd : dbar d ≠ 0) :
    Rgr a b d = (1 + eps d a) / (1 + eps d b) *
      ((1 - mu d * (1 + eps d b) + 1 / n) / (1 - mu d * (1 + eps d a) + 1 / n)) *
      (1 + (eps d a - eps d b) * (sigma2 d / dbar d ^ 2) * mu d * (1 - 1 / n) /
        (1 - mu d) ^ 2) := by
  have key : mu d * (1 - 1 / n) = dbar d / n := by rw [mu]; field_simp
  unfold Rgr rhoF
  rw [show (eps d a - eps d b) * (sigma2 d / dbar d ^ 2) * mu d * (1 - 1 / n) =
    (eps d a - eps d b) * (sigma2 d / dbar d ^ 2) * (mu d * (1 - 1 / n)) by ring, key]
  congr 2
  field_simp

/-- The algebra behind `ℛ - R^gr = R^gr · μ · ratioG / ratioD`. -/
theorem ratio_identity {X A B Cf μ Fab Fba G : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : Cf ≠ 0)
    (hF : 1 - μ * Fba ≠ 0)
    (hG : μ * G = (1 - μ * Fab) * A - (1 - μ * Fba) * B * Cf) :
    X * ((1 - μ * Fab) / (1 - μ * Fba)) - X * (B / A) * Cf =
      X * (B / A) * Cf * μ * G / ((1 - μ * Fba) * B * Cf) := by
  rw [mul_assoc (X * (B / A) * Cf) μ G, hG]
  field_simp

/-- The scale `η = 2 d̄^{α-1}` and the smallness bounds it satisfies under `Spread α d`. -/
theorem spread_bounds {n : ℕ} {α : ℝ} (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 3 / 5) {d : Seq n}
    (hd32 : 32 ≤ dbar d) (hS : Spread α d) (hn0 : (n : ℝ) ≠ 0) :
    0 < 2 * dbar d ^ (α - 1) ∧ 2 * dbar d ^ (α - 1) ≤ 2 * dbar d ^ (-(2 / 5 : ℝ)) ∧
    2 * dbar d ^ (α - 1) ≤ 1 / 2 ∧ (∀ i, |eps d i| ≤ 2 * dbar d ^ (α - 1)) ∧
    1 / dbar d ≤ (2 * dbar d ^ (α - 1)) ^ 2 ∧
    sigma2 d / dbar d ^ 2 ≤ (2 * dbar d ^ (α - 1)) ^ 2 ∧
    (2 * dbar d ^ (α - 1)) ^ 4 = 16 * dbar d ^ (4 * α - 4) := by
  obtain ⟨-, hsp⟩ := hS
  have hdpos : 0 < dbar d := by linarith
  have hd0 : dbar d ≠ 0 := hdpos.ne'
  have hd1 : 1 ≤ dbar d := by linarith
  set η₀ := dbar d ^ (α - 1) with hη₀
  have hηpos : 0 < η₀ := Real.rpow_pos_of_pos hdpos _
  have hη25 : η₀ ≤ dbar d ^ (-(2 / 5 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hη12 : η₀ ≤ 1 / 4 := by
    calc η₀ ≤ dbar d ^ (-(2 / 5 : ℝ)) := hη25
      _ ≤ (32 : ℝ) ^ (-(2 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hd32 (by norm_num)
      _ = (2 : ℝ) ^ (-2 : ℝ) := by
        rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      _ = 1 / 4 := by norm_num
  have hε : ∀ i, |eps d i| ≤ 2 * η₀ := fun i => by
    rw [eps, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos, hη₀, Real.rpow_sub_one hd0,
      mul_assoc, div_mul_cancel₀ _ hd0]
    exact hsp i
  have hη2 : η₀ ^ 2 = dbar d ^ (2 * α - 2) := by
    rw [hη₀, ← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]; congr 1; push_cast; ring
  have hδ : 1 / dbar d ≤ η₀ ^ 2 := by
    rw [hη2, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have ht : sigma2 d / dbar d ^ 2 ≤ (2 * η₀) ^ 2 := by
    rw [mul_pow, hη2, div_le_iff₀ (by positivity)]
    calc sigma2 d ≤ (2 * dbar d ^ α) ^ 2 := sigma2_le d hn0 hsp
      _ = 2 ^ 2 * dbar d ^ (2 * α - 2) * dbar d ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast (dbar d ^ α), ← Real.rpow_mul hdpos.le,
          ← Real.rpow_natCast (dbar d) 2, mul_assoc, ← Real.rpow_add hdpos]
        congr 2; push_cast; ring
  have hη4 : (2 * η₀) ^ 4 = 16 * dbar d ^ (4 * α - 4) := by
    rw [mul_pow, hη₀, ← Real.rpow_natCast (dbar d ^ (α - 1)), ← Real.rpow_mul hdpos.le]
    norm_num
    congr 1; ring
  refine ⟨by positivity, by linarith, by linarith, hε, ?_, ht, hη4⟩
  nlinarith

/-- `η ≤ η₁` once `d̄ ≥ (η₁/2)^{-5/2}`. -/
theorem eta_le {η η₁ D : ℝ} (hη₁ : 0 < η₁) (hη : η ≤ 2 * D ^ (-(2 / 5 : ℝ)))
    (hD : (η₁ / 2) ^ (-(5 / 2 : ℝ)) ≤ D) : η ≤ η₁ :=
  calc η ≤ 2 * D ^ (-(2 / 5 : ℝ)) := hη
    _ ≤ 2 * ((η₁ / 2) ^ (-(5 / 2 : ℝ))) ^ (-(2 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (by positivity) _) hD (by norm_num))
        (by norm_num)
    _ = η₁ := by rw [← Real.rpow_mul (by positivity)]; norm_num; ring

/-- Lemma 7.1(a): `ℛ(P^gr,Y^gr) = R^gr (1 + O(μ d̄^{4α-4}))`. -/
theorem lemma_7_1a (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 3 / 5) :
    ∃ C D₀ : ℝ, ∀ (n : ℕ) (d : Seq n), D₀ ≤ dbar d → Spread α d →
      ∀ a b, Close (opR Pgr Ygr a b d) (Rgr a b d) (C * err71 α d) := by
  obtain ⟨bF, hbF⟩ := bad_valid
  obtain ⟨bG, bD, hGD⟩ := ratio_expansion bF
  set η₁ := min (1 / 2) (min (min bF.η₀ bG.η₀) (min bD.η₀ (9 / 16 / (2 * (bD.all + bD.R + 1)))))
    with hη₁
  refine ⟨16 * (32 / 9 * |bG.R|), max 32 ((η₁ / 2) ^ (-(5 / 2 : ℝ))), fun n d hD hS a b => ?_⟩
  obtain ⟨hμ4, hsp⟩ := hS
  have hd32 : 32 ≤ dbar d := le_trans (le_max_left _ _) hD
  have hd8 : 8 ≤ dbar d := by linarith
  have hdpos : 0 < dbar d := by linarith
  have hd0 : dbar d ≠ 0 := hdpos.ne'
  have hd1 : 1 ≤ dbar d := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast a.pos
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hμ0 : 0 ≤ mu d := div_nonneg hdpos.le (by linarith)
  have hC0 : 0 ≤ 16 * (32 / 9 * |bG.R|) * err71 α d := by
    unfold err71; have := Real.rpow_pos_of_pos hdpos (4 * α - 4); positivity
  obtain ⟨hηpos, hη25, hη12, hε, hδ, ht, hη4⟩ := spread_bounds hα₁ hα₂ hd32 ⟨hμ4, hsp⟩ hn0
  set η := 2 * dbar d ^ (α - 1) with hη
  have hεa := abs_le.1 (hε a)
  have hεb := abs_le.1 (hε b)
  have h1a : 0 < 1 + eps d a := by linarith
  have h1b : 0 < 1 + eps d b := by linarith
  have hda : (d a : ℝ) = dbar d * (1 + eps d a) := by rw [eps]; field_simp; ring
  have hdb : (d b : ℝ) = dbar d * (1 + eps d b) := by rw [eps]; field_simp; ring
  have hν0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hA : 0 < 1 - mu d * (1 + eps d a) + 1 / n := by
    have : mu d * (1 + eps d a) ≤ 1 / 4 * (3 / 2) :=
      mul_le_mul hμ4.le (by linarith) h1a.le (by norm_num)
    linarith
  by_cases hab : a = b
  · subst hab
    have hR : opR Pgr Ygr a a d = 1 := by
      have : (d a : ℝ) ≠ 0 := by rw [hda]; positivity
      simp [opR, bad, this]
    have hρ : Rgr a a d = 1 := by
      simp only [Rgr, rhoF, sub_self, zero_mul, zero_div, add_zero, mul_one]
      rw [div_self h1a.ne', div_self hA.ne', one_mul]
    rw [hR, hρ]; exact Close.refl 1 hC0
  -- `a ≠ b`: `n ≥ 3` and the expansions apply
  have hn2 : (2 : ℝ) ≤ n := by
    have : 1 < Fintype.card (Fin n) := Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨a, b, hab⟩⟩
    rw [Fintype.card_fin] at this; exact_mod_cast this
  have hn1' : (0 : ℝ) < n - 1 := by linarith
  have hn3r : (3 : ℝ) ≤ n := by rw [mu, div_lt_iff₀ hn1'] at hμ4; linarith
  have hn3 : 3 ≤ n := by exact_mod_cast hn3r
  have hμpos : 0 < mu d := div_pos hdpos hn1'
  have hFab := hbF d a b η hab hηpos hη12 hd1 hμ4.le hn3 hε hδ ht
  have hFba := hbF d b a η (Ne.symm hab) hηpos hη12 hd1 hμ4.le hn3 hε hδ ht
  have hν : 1 / (n : ℝ) = mu d * (1 / dbar d) * (1 + mu d * (1 / dbar d))⁻¹ := by
    rw [mu]; field_simp; ring
  obtain ⟨hGv, hDv⟩ := hGD η (mu d) (1 / dbar d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b)
    (1 / n) _ _ hηpos hμpos hμ4.le (by positivity) hδ (div_nonneg (sigma2_nonneg d) (by positivity))
    ht (hε a) (hε b) hν hFab hFba
  set Fab := bad Pgr Ygr a b (d - e b) / mu d with hFab_def
  set Fba := bad Pgr Ygr b a (d - e a) / mu d with hFba_def
  -- `η ≤ η₁`
  have hη₁pos : 0 < η₁ := by
    have := hDv.all_nonneg; have := hDv.R_nonneg
    simp only [hη₁, lt_min_iff]
    exact ⟨by norm_num, ⟨hFab.η₀_pos, hGv.η₀_pos⟩, hDv.η₀_pos, by positivity⟩
  have hηη₁ : η ≤ η₁ := eta_le hη₁pos hη25 (le_trans (le_max_right _ _) hD)
  simp only [hη₁, le_min_iff] at hηη₁
  obtain ⟨-, ⟨-, hG0⟩, hD0, hDL⟩ := hηη₁
  -- numerical bounds
  have hGb : |ratioG (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fab Fba| ≤
      |bG.R| * η ^ 4 := by
    have := hGv.rem hηpos hG0 (by simp [hηpos.le])
    rw [val_mk0_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hDb : 9 / 16 / 2 ≤ ratioD (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fba :=
    hDv.lower (L := 9 / 16) (by show (9 : ℝ) / 16 ≤ (mu d - 1) ^ 2; nlinarith) hηpos
      (le_min_iff.2 ⟨hD0, hDL⟩) (by simp [hηpos.le])
  have hDpos : 0 < ratioD (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fba := by
    linarith
  -- the exact identity `ℛ - R^gr = R^gr · μ · ratioG / ratioD`
  have e1 : bad Pgr Ygr a b (d - e b) = mu d * Fab := by rw [hFab_def]; field_simp
  have e2 : bad Pgr Ygr b a (d - e a) = mu d * Fba := by rw [hFba_def]; field_simp
  have hfac := hDpos.ne'
  unfold ratioD at hfac
  obtain ⟨⟨hf1, hf2⟩, hf3⟩ := mul_ne_zero_iff.1 hfac |>.imp_left mul_ne_zero_iff.1
  have hR : opR Pgr Ygr a b d =
      (1 + eps d a) / (1 + eps d b) * ((1 - mu d * Fab) / (1 - mu d * Fba)) := by
    rw [opR, e1, e2, hda, hdb]; field_simp
  have hkey : mu d * ratioG (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fab Fba =
      (1 - mu d * Fab) * (1 - mu d * (1 + eps d a) + 1 / n) -
      (1 - mu d * Fba) * (1 - mu d * (1 + eps d b) + 1 / n) *
        (1 + (eps d a - eps d b) * (sigma2 d / dbar d ^ 2) * mu d * (1 - 1 / n) /
          (1 - mu d) ^ 2) := by
    unfold ratioG; ring
  have hdiff : opR Pgr Ygr a b d - Rgr a b d =
      Rgr a b d * mu d *
        ratioG (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fab Fba /
        ratioD (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fba := by
    rw [hR, Rgr_eq d a b hn0 hn1'.ne' hd0]
    unfold ratioD
    exact ratio_identity hA.ne' hf2 hf3 hf1 hkey
  set G := ratioG (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fab Fba
  set D := ratioD (mu d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d b) (1 / n) Fba
  rw [Close, hdiff, abs_div, abs_mul, abs_mul, abs_of_pos hμpos, abs_of_pos hDpos, err71,
    div_le_iff₀ hDpos]
  have hρ0 := abs_nonneg (Rgr a b d)
  have hμη : 0 ≤ mu d * dbar d ^ (4 * α - 4) := by positivity
  calc |Rgr a b d| * mu d * |G| ≤ |Rgr a b d| * mu d * (|bG.R| * η ^ 4) :=
        mul_le_mul_of_nonneg_left hGb (by positivity)
    _ = 16 * (32 / 9 * |bG.R|) * (mu d * dbar d ^ (4 * α - 4)) * |Rgr a b d| * (9 / 16 / 2) := by
        rw [hη4]; ring
    _ ≤ 16 * (32 / 9 * |bG.R|) * (mu d * dbar d ^ (4 * α - 4)) * |Rgr a b d| * D :=
        mul_le_mul_of_nonneg_left hDb (by positivity)

/-- The algebra behind `𝒴 - Y^gr = Y^gr · μ · yG / yD`. -/
theorem opY_identity {X F K w κ yN yD μ : ℝ} (hF : F ≠ 0) (hK : K ≠ 0) (hw : w ≠ 0)
    (hκ : κ ≠ 0) (hyD : yD ≠ 0) (hμ : μ ≠ 0) :
    X * (K * w / κ * yN) / (K * w * yD / F) - X * F =
      X * F * μ * ((yN - κ * yD) / μ) / (κ * yD) := by
  field_simp

set_option maxHeartbeats 2000000 in
/-- Lemma 7.1(c): `𝒴(P^gr,Y^gr) = Y^gr (1 + O(μ d̄^{4α-4}))`. -/
theorem lemma_7_1c (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 3 / 5) :
    ∃ C D₀ : ℝ, ∀ (n : ℕ) (d : Seq n), D₀ ≤ dbar d → Spread α d →
      ∀ a v b, a ≠ v → a ≠ b → v ≠ b →
        Close (opY Pgr Ygr a v b d) (Ygr a v b d) (C * err71 α d) := by
  obtain ⟨bG, bD, hGD⟩ := opY_expansion
  set η₁ := min (1 / 2) (min bG.η₀ (min bD.η₀ (3 / 4 / (2 * (bD.all + bD.R + 1))))) with hη₁
  refine ⟨16 * (8 / 3 * |bG.R|), max 32 ((η₁ / 2) ^ (-(5 / 2 : ℝ))),
    fun n d hD hS a v b hav hab hvb => ?_⟩
  obtain ⟨hμ4, hsp⟩ := hS
  have hd32 : 32 ≤ dbar d := le_trans (le_max_left _ _) hD
  have hd8 : 8 ≤ dbar d := by linarith
  have hdpos : 0 < dbar d := by linarith
  have hd0 : dbar d ≠ 0 := hdpos.ne'
  have hn3 : 3 ≤ n := by
    have h := card_le_univ ({a, v, b} : Finset (Fin n))
    have h3 : ({a, v, b} : Finset (Fin n)).card = 3 := card_eq_three.2 ⟨a, v, b, hav, hab, hvb, rfl⟩
    rwa [h3, Fintype.card_fin] at h
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1' : (n : ℝ) - 1 ≠ 0 := by linarith
  have hμpos : 0 < mu d := div_pos hdpos (by linarith)
  obtain ⟨hηpos, hη25, hη12, hε, hδ, ht, hη4⟩ := spread_bounds hα₁ hα₂ hd32 ⟨hμ4, hsp⟩ hn0
  set η := 2 * dbar d ^ (α - 1) with hη
  have hεb := abs_le.1 (hε b)
  have hεv := abs_le.1 (hε v)
  have hd18 : 1 / dbar d ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hd8
  have h1b : 0 < 1 + eps d b := by linarith
  have hw : 0 < 1 + eps d v - 1 / dbar d := by linarith
  have hmud : 1 / ((n : ℝ) - 1) = mu d * (1 / dbar d) := by rw [mu]; field_simp
  have hnd2 : (n : ℝ) * dbar d - 2 ≠ 0 := by nlinarith
  -- the parameters of `d - e_a - e_v`
  have hμ3 := mu_sub_e_sub_e d a v hn0 hd0
  have hδ3 := inv_dbar_sub_e_sub_e d a v hn0 hd0 hnd2
  have hxa : eps (d - e a - e v) a =
      (eps d a - 1 / dbar d + 2 * (1 / dbar d / n)) / (1 - 2 * (1 / dbar d / n)) := by
    rw [eps_sub_e_sub_e d a v a hn0 hd0 hnd2, if_pos rfl, if_neg hav, sub_zero]
  have hxv : eps (d - e a - e v) v =
      (eps d v - 1 / dbar d + 2 * (1 / dbar d / n)) / (1 - 2 * (1 / dbar d / n)) := by
    rw [eps_sub_e_sub_e d a v v hn0 hd0 hnd2, if_neg hav.symm, if_pos rfl, sub_zero]
  have hxb : eps (d - e a - e v) b =
      (eps d b + 2 * (1 / dbar d / n)) / (1 - 2 * (1 / dbar d / n)) := by
    rw [eps_sub_e_sub_e d a v b hn0 hd0 hnd2, if_neg hab.symm, if_neg hvb.symm, sub_zero,
      sub_zero]
  have hs0 : sigma2 d / (dbar d * n) = sigma2 d / dbar d ^ 2 * (mu d * (1 - 1 / n)) := by
    rw [mu]; field_simp
  have hs3 : sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n) =
      (sigma2 d / dbar d ^ 2 + 2 * (1 / dbar d / n) * (1 / dbar d) * (1 - 2 / n) -
        2 * (1 / dbar d / n) * (eps d a + eps d v)) * (mu d * (1 - 1 / n)) /
        (1 - 2 * (1 / dbar d / n)) := by
    have h1 : dbar d - 2 / n ≠ 0 := fun h =>
      hnd2 (by rw [sub_eq_zero] at h; rw [h]; field_simp; ring)
    rw [sigma2_sub_e_sub_e d a v hav hn0, dbar_sub_e_sub_e, mu, eps, eps]
    field_simp
    ring
  obtain ⟨hGv, hDv⟩ := hGD η (mu d) (1 / dbar d) (sigma2 d / dbar d ^ 2) (eps d a) (eps d v)
    (eps d b) _ _ _ _ _ _ _ _ n hηpos hη12 hμpos hμ4.le (by positivity) hδ
    (div_nonneg (sigma2_nonneg d) (by positivity)) ht (hε a) (hε v) (hε b) hn3 hmud rfl hμ3 hδ3
    hxa hxv hxb hs0 hs3
  -- `η ≤ η₁`
  have hη₁pos : 0 < η₁ := by
    have := hDv.all_nonneg; have := hDv.R_nonneg
    simp only [hη₁, lt_min_iff]
    exact ⟨by norm_num, hGv.η₀_pos, hDv.η₀_pos, by positivity⟩
  have hηη₁ : η ≤ η₁ := eta_le hη₁pos hη25 (le_trans (le_max_right _ _) hD)
  simp only [hη₁, le_min_iff] at hηη₁
  obtain ⟨-, hG0, hD0, hDL⟩ := hηη₁
  -- numerical bounds
  set G := (yNum (mu (d - e a - e v)) (sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n))
        (1 / ((n : ℝ) - 1)) (1 / dbar (d - e a - e v)) (eps (d - e a - e v) a)
        (eps (d - e a - e v) v) (eps (d - e a - e v) b) -
      (1 - 2 * (1 / dbar d / n)) *
      yDen (mu d) (sigma2 d / (dbar d * n)) (1 / ((n : ℝ) - 1)) (1 / dbar d) (eps d a) (eps d v)
        (eps d b) (mu (d - e a - e v)) (sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n))
        (eps (d - e a - e v) a) (eps (d - e a - e v) v)) / mu d with hG
  set D := (1 - 2 * (1 / dbar d / n)) *
      yDen (mu d) (sigma2 d / (dbar d * n)) (1 / ((n : ℝ) - 1)) (1 / dbar d) (eps d a) (eps d v)
        (eps d b) (mu (d - e a - e v)) (sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n))
        (eps (d - e a - e v) a) (eps (d - e a - e v) v) with hD_def
  have hGb : |G| ≤ |bG.R| * η ^ 4 := by
    have := hGv.rem hηpos hG0 (by simp [hηpos.le])
    rw [val_mk0_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hDb : 3 / 4 / 2 ≤ D :=
    hDv.lower (L := 3 / 4) (by show (3 : ℝ) / 4 ≤ 1 - mu d; linarith) hηpos
      (le_min_iff.2 ⟨hD0, hDL⟩) (by simp [hηpos.le])
  have hDpos : 0 < D := by linarith
  obtain ⟨hκ0, hyD0⟩ := mul_ne_zero_iff.1 hDpos.ne'
  -- the exact identity `𝒴 - Y^gr = Y^gr · μ · G / D`
  have h1μ3 : 1 - mu (d - e a - e v) ≠ 0 := by
    rw [hμ3]
    have : 0 ≤ 1 / dbar d / n := by positivity
    nlinarith
  have hN : Pgr b v (d - e a - e v) - Ygr a v b (d - e a - e v) =
      mu (d - e a - e v) * (1 + eps (d - e a - e v) b) * (1 + eps (d - e a - e v) v) *
        yNum (mu (d - e a - e v)) (sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n))
          (1 / ((n : ℝ) - 1)) (1 / dbar (d - e a - e v)) (eps (d - e a - e v) a)
          (eps (d - e a - e v) v) (eps (d - e a - e v) b) := by
    simp only [Pgr, Ygr, piF_eq, yNum, Tcorr]
    field_simp
    ring
  have hK : mu (d - e a - e v) * (1 + eps (d - e a - e v) b) * (1 + eps (d - e a - e v) v) =
      mu d * (1 + eps d b) * (1 + eps d v - 1 / dbar d) / (1 - 2 * (1 / dbar d / n)) := by
    have hκ' : dbar d * n - 2 ≠ 0 := by rwa [mul_comm]
    have hκ'' : -2 + dbar d * n ≠ 0 := by rwa [add_comm, ← sub_eq_add_neg]
    rw [hμ3, hxb, hxv]; field_simp; ring
  set F := piF (eps d b) (eps d v - 1 / dbar d) (mu d) (sigma2 d) (dbar d) n *
    (1 + (1 + eps d a - mu d * (1 + eps d a + eps d b)) / (((n : ℝ) - 1) * (1 - mu d))) with hF
  have h1μ : 1 - mu d ≠ 0 := by linarith
  have hMF : (1 - Pgr a v (d - e a - e v)) * F =
      mu d * (1 + eps d b) * (1 + eps d v - 1 / dbar d) *
      yDen (mu d) (sigma2 d / (dbar d * n)) (1 / ((n : ℝ) - 1)) (1 / dbar d) (eps d a) (eps d v)
        (eps d b) (mu (d - e a - e v)) (sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n))
        (eps (d - e a - e v) a) (eps (d - e a - e v) v) := by
    simp only [hF, Pgr, piF_eq, yDen, Tcorr]
    field_simp
    ring
  have hK0 : mu d * (1 + eps d b) ≠ 0 := by positivity
  have hF0 : F ≠ 0 := fun h => hyD0 (by
    rw [h, mul_zero] at hMF
    exact (mul_eq_zero.1 hMF.symm).resolve_left (by positivity))
  have hM : 1 - Pgr a v (d - e a - e v) = mu d * (1 + eps d b) * (1 + eps d v - 1 / dbar d) *
      yDen (mu d) (sigma2 d / (dbar d * n)) (1 / ((n : ℝ) - 1)) (1 / dbar d) (eps d a) (eps d v)
        (eps d b) (mu (d - e a - e v)) (sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n))
        (eps (d - e a - e v) a) (eps (d - e a - e v) v) / F := by
    rw [eq_div_iff hF0]; exact hMF
  have hY : Ygr a v b d = Pgr a v d * F := by simp only [Ygr, Pgr, hF]; ring
  have hdiff : opY Pgr Ygr a v b d - Ygr a v b d = Ygr a v b d * mu d * G / D := by
    rw [opY, hN, hK, hM, hY]
    exact opY_identity hF0 hK0 hw.ne' hκ0 hyD0 hμpos.ne'
  rw [Close, hdiff, abs_div, abs_mul, abs_mul, abs_of_pos hμpos, abs_of_pos hDpos, err71,
    div_le_iff₀ hDpos]
  have hρ0 := abs_nonneg (Ygr a v b d)
  have hμη : 0 ≤ mu d * dbar d ^ (4 * α - 4) := by positivity
  calc |Ygr a v b d| * mu d * |G| ≤ |Ygr a v b d| * mu d * (|bG.R| * η ^ 4) :=
        mul_le_mul_of_nonneg_left hGb (mul_nonneg hρ0 hμpos.le)
    _ = 16 * (8 / 3 * |bG.R|) * (mu d * dbar d ^ (4 * α - 4)) * |Ygr a v b d| * (3 / 4 / 2) := by
        rw [hη4]; ring
    _ ≤ 16 * (8 / 3 * |bG.R|) * (mu d * dbar d ^ (4 * α - 4)) * |Ygr a v b d| * D :=
        mul_le_mul_of_nonneg_left hDb (by positivity)

/-- The algebra behind `𝒫 - P^gr = P^gr · μ · G / D`. -/
theorem opP_identity {S Qa G A ea ev μ N : ℝ} (hμ : μ ≠ 0) (hN : N - 1 ≠ 0)
    (hD : (1 + ea) * (1 + A) * (1 + 1 / (N - 1)) * (S / N) ≠ 0)
    (hG : 1 - Qa = μ * G + (1 + ea) * (1 + A) * (1 + 1 / (N - 1)) * (S / N)) :
    μ * (N - 1) * (1 + ev) * (S / (1 - Qa))⁻¹ - μ * (1 + ea) * (1 + ev) * (1 + A) =
      μ * (1 + ea) * (1 + ev) * (1 + A) * μ * G /
        ((1 + ea) * (1 + A) * (1 + 1 / (N - 1)) * (S / N)) := by
  have hea : 1 + ea ≠ 0 := fun h => hD (by rw [h]; ring)
  have hA : 1 + A ≠ 0 := fun h => hD (by rw [h]; ring)
  have hm : 1 + 1 / (N - 1) ≠ 0 := fun h => hD (by rw [h]; ring)
  have hS : S ≠ 0 := fun h => hD (by rw [h]; ring)
  have hN0 : N ≠ 0 := fun h => hD (by rw [h]; simp)
  rw [hG, inv_div]
  field_simp
  linear_combination (ev * μ * N * G - ev * μ * N ^ 2 * G + μ * N * G - μ * N ^ 2 * G) *
    mul_inv_cancel₀ hN0

set_option maxHeartbeats 2000000 in
/-- Lemma 7.1(b): `𝒫(P^gr,R^gr) = P^gr (1 + O(μ d̄^{4α-4}))`. -/
theorem lemma_7_1b (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 3 / 5) :
    ∃ C D₀ : ℝ, ∀ (n : ℕ) (d : Seq n), D₀ ≤ dbar d → Spread α d →
      ∀ a v, a ≠ v → Close (opP Pgr Rgr a v d) (Pgr a v d) (C * err71 α d) := by
  obtain ⟨bG, bD, hGD⟩ := opP_expansion
  set η₁ := min (1 / 2) (min bG.η₀ (min bD.η₀ (3 / 4 / (2 * (bD.all + bD.R + 1))))) with hη₁
  refine ⟨16 * (8 / 3 * |bG.R|), max 32 ((η₁ / 2) ^ (-(5 / 2 : ℝ))), fun n d hD hS a v hav => ?_⟩
  obtain ⟨hμ4, hsp⟩ := hS
  have hd32 : 32 ≤ dbar d := le_trans (le_max_left _ _) hD
  have hd8 : 8 ≤ dbar d := by linarith
  have hdpos : 0 < dbar d := by linarith
  have hd0 : dbar d ≠ 0 := hdpos.ne'
  have hn2 : (2 : ℝ) ≤ n := by
    have : 1 < Fintype.card (Fin n) := Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨a, v, hav⟩⟩
    rw [Fintype.card_fin] at this; exact_mod_cast this
  have hn1' : (0 : ℝ) < n - 1 := by linarith
  have hn3r : (3 : ℝ) ≤ n := by rw [mu, div_lt_iff₀ hn1'] at hμ4; linarith
  have hn3 : 3 ≤ n := by exact_mod_cast hn3r
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hμpos : 0 < mu d := div_pos hdpos hn1'
  obtain ⟨hηpos, hη25, hη12, hε, hδ, ht, hη4⟩ := spread_bounds hα₁ hα₂ hd32 ⟨hμ4, hsp⟩ hn0
  set η := 2 * dbar d ^ (α - 1) with hη
  have hmud : 1 / ((n : ℝ) - 1) = mu d * (1 / dbar d) := by rw [mu]; field_simp
  have hnd : (n : ℝ) * dbar d - 1 ≠ 0 := by nlinarith
  have hnd2 : (n : ℝ) * dbar d - 2 ≠ 0 := by nlinarith
  have h1 : dbar d - 1 / n ≠ 0 := fun h => hnd (by rw [sub_eq_zero] at h; rw [h]; field_simp; ring)
  have h2 : 1 - 1 / dbar d / n ≠ 0 := fun h => hnd (by
    have : 1 / dbar d / n = 1 := by linarith
    field_simp at this; linarith)
  have haV : a ∈ univ.erase v := mem_erase.2 ⟨hav, mem_univ a⟩
  have hcard : (univ.erase v).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]
  have hsum : ∀ f : Fin n → ℝ, ∑ b ∈ univ.erase v, f b = ∑ i, f i - f v := fun f => by
    rw [← add_sum_erase _ _ (mem_univ v)]; ring
  have hdb : (1 : ℝ) / dbar (d - e v) = 1 / dbar d / (1 - 1 / dbar d / n) := by
    rw [dbar_sub_e]; field_simp
  have hs0 : sigma2 d / (dbar d * n) = sigma2 d / dbar d ^ 2 * (mu d * (1 - 1 / n)) := by
    rw [mu]; field_simp
  have hs' : sigma2 (d - e v) / (dbar (d - e v) * n) =
      (sigma2 d / dbar d ^ 2 + 1 / dbar d / n * (1 / dbar d) * (1 - 1 / n) -
        2 * (1 / dbar d / n) * eps d v) * mu d / ((1 + mu d * (1 / dbar d)) * (1 - 1 / dbar d / n)) := by
    have h3 : 1 + mu d * (1 / dbar d) = n / (n - 1) := by rw [mu]; field_simp; ring
    rw [h3, sigma2_sub_e d v hn0, dbar_sub_e, mu, eps]
    field_simp
    ring
  obtain ⟨hGv, hDv⟩ := hGD η (mu d) (1 / dbar d) (sigma2 d / dbar d ^ 2) ((∑ i, eps d i ^ 3) / n)
    (eps d a) (eps d v) (1 / dbar d / n) (mu (d - e v)) (sigma2 (d - e v)) (dbar (d - e v))
    (eps (d - e v) a) (sigma2 d / (dbar d * n)) n (univ.erase v) a (eps d) (eps (d - e v))
    (fun b => eps (d - e b - e v) b) (fun b => eps (d - e b - e v) v) (fun b => mu (d - e b - e v))
    (fun b => sigma2 (d - e b - e v) / (dbar (d - e b - e v) * n))
    hηpos hη12 hμpos hμ4.le (by positivity) hδ (div_nonneg (sigma2_nonneg d) (by positivity)) ht
    (by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n), div_le_iff₀ (by positivity)]
      simpa [mul_comm] using abs_sum_pow_three_le univ (eps d) fun i _ => hε i)
    (hε a) (hε v) (fun b _ => hε b) hn3 hcard haV rfl hmud rfl
    (by rw [hsum, sum_eps d hn0]; ring) (by rw [hsum, sum_eps_sq d hn0 hd0])
    (by rw [hsum]; field_simp) (mu_sub_e d v hn0 hd0) hdb
    (by rw [eps_sub_e d v a hn0 hd0 hnd, if_neg hav]; ring)
    (fun b hb => by rw [eps_sub_e d v b hn0 hd0 hnd, if_neg (mem_erase.1 hb).1]; ring)
    hs' (fun b _ => mu_sub_e_sub_e d b v hn0 hd0)
    (fun b hb => by
      rw [eps_sub_e_sub_e d b v b hn0 hd0 hnd2, if_pos rfl, if_neg (mem_erase.1 hb).1, sub_zero])
    (fun b hb => by
      rw [eps_sub_e_sub_e d b v v hn0 hd0 hnd2, if_neg (mem_erase.1 hb).1.symm, if_pos rfl,
        sub_zero])
    (fun b hb => by
      have hbv := (mem_erase.1 hb).1
      have h1 : dbar d - 2 / n ≠ 0 := fun h =>
        hnd2 (by rw [sub_eq_zero] at h; rw [h]; field_simp; ring)
      rw [sigma2_sub_e_sub_e d b v hbv hn0, dbar_sub_e_sub_e, mu, eps, eps]
      field_simp
      ring)
    hs0
  -- `η ≤ η₁`
  have hη₁pos : 0 < η₁ := by
    have := hDv.all_nonneg; have := hDv.R_nonneg
    simp only [hη₁, lt_min_iff]
    exact ⟨by norm_num, hGv.η₀_pos, hDv.η₀_pos, by positivity⟩
  have hηη₁ : η ≤ η₁ := eta_le hη₁pos hη25 (le_trans (le_max_right _ _) hD)
  simp only [hη₁, le_min_iff] at hηη₁
  obtain ⟨-, hG0, hD0, hDL⟩ := hηη₁
  -- numerical bounds
  set Qa := pQ (mu (d - e a - e v)) (sigma2 (d - e a - e v) / (dbar (d - e a - e v) * n))
    (1 / ((n : ℝ) - 1)) (eps (d - e a - e v) a) (eps (d - e a - e v) v) with hQa
  set S := ∑ b ∈ univ.erase v, pTerm (mu (d - e v)) (sigma2 (d - e v)) (dbar (d - e v)) n
    (eps (d - e v) a) (eps (d - e v) b) (mu (d - e b - e v))
    (sigma2 (d - e b - e v) / (dbar (d - e b - e v) * n)) (1 / ((n : ℝ) - 1))
    (eps (d - e b - e v) b) (eps (d - e b - e v) v) with hS
  set D := pDen (mu d) (sigma2 d / (dbar d * n)) (1 / ((n : ℝ) - 1)) (eps d a) (eps d v) (S / n)
    with hD_def
  set G := (1 - Qa - D) / mu d with hG
  have hGb : |G| ≤ |bG.R| * η ^ 4 := by
    have := hGv.rem hηpos hG0 (by simp [hηpos.le])
    rw [val_mk0_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hDb : 3 / 4 / 2 ≤ D :=
    hDv.lower (L := 3 / 4) (by show (3 : ℝ) / 4 ≤ 1 - mu d; linarith) hηpos
      (le_min_iff.2 ⟨hD0, hDL⟩) (by simp [hηpos.le])
  have hDpos : 0 < D := by linarith
  -- the exact identity `𝒫 - P^gr = P^gr · μ · G / D`
  have hopP : opP Pgr Rgr a v d = (d v : ℝ) * (S / (1 - Qa))⁻¹ := by
    rw [opP, hS, ← sum_div]
    simp only [Rgr, Pgr, pTerm, piF_eq_pQ, hQa]
  have hPgr : Pgr a v d = mu d * (1 + eps d a) * (1 + eps d v) *
      (1 + Acorr (mu d) (sigma2 d / (dbar d * n)) (1 / ((n : ℝ) - 1)) (eps d a) (eps d v)) := by
    simp only [Pgr, piF_eq_pQ, pQ]
  have hdv : (d v : ℝ) = mu d * ((n : ℝ) - 1) * (1 + eps d v) := by
    rw [mu, eps]; field_simp; ring
  have hD' : D = (1 + eps d a) *
      (1 + Acorr (mu d) (sigma2 d / (dbar d * n)) (1 / ((n : ℝ) - 1)) (eps d a) (eps d v)) *
      (1 + 1 / ((n : ℝ) - 1)) * (S / n) := by
    simp only [hD_def, pDen]
  have hG' : 1 - Qa = mu d * G + D := by rw [hG]; field_simp; ring
  have hdiff : opP Pgr Rgr a v d - Pgr a v d = Pgr a v d * mu d * G / D := by
    rw [hopP, hPgr, hdv, hD']
    exact opP_identity hμpos.ne' hn1'.ne' (hD' ▸ hDpos.ne') (hD' ▸ hG')
  rw [Close, hdiff, abs_div, abs_mul, abs_mul, abs_of_pos hμpos, abs_of_pos hDpos, err71,
    div_le_iff₀ hDpos]
  have hρ0 := abs_nonneg (Pgr a v d)
  have hμη : 0 ≤ mu d * dbar d ^ (4 * α - 4) := by positivity
  calc |Pgr a v d| * mu d * |G| ≤ |Pgr a v d| * mu d * (|bG.R| * η ^ 4) :=
        mul_le_mul_of_nonneg_left hGb (mul_nonneg hρ0 hμpos.le)
    _ = 16 * (8 / 3 * |bG.R|) * (mu d * dbar d ^ (4 * α - 4)) * |Pgr a v d| * (3 / 4 / 2) := by
        rw [hη4]; ring
    _ ≤ 16 * (8 / 3 * |bG.R|) * (mu d * dbar d ^ (4 * α - 4)) * |Pgr a v d| * D :=
        mul_le_mul_of_nonneg_left hDb (by positivity)

/-- Lemma 7.1 (a)–(c), for `d̄` large. -/
theorem lemma_7_1 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 3 / 5) :
    ∃ C D₀ : ℝ, ∀ (n : ℕ) (d : Seq n), D₀ ≤ dbar d → Spread α d →
      (∀ a b, Close (opR Pgr Ygr a b d) (Rgr a b d) (C * err71 α d)) ∧
      (∀ a v, a ≠ v → Close (opP Pgr Rgr a v d) (Pgr a v d) (C * err71 α d)) ∧
      (∀ a v b, a ≠ v → a ≠ b → v ≠ b →
        Close (opY Pgr Ygr a v b d) (Ygr a v b d) (C * err71 α d)) := by
  obtain ⟨Ca, Da, ha⟩ := lemma_7_1a α hα₁ hα₂
  obtain ⟨Cb, Db, hb⟩ := lemma_7_1b α hα₁ hα₂
  obtain ⟨Cc, Dc, hc⟩ := lemma_7_1c α hα₁ hα₂
  refine ⟨max Ca (max Cb Cc), max 1 (max Da (max Db Dc)), fun n d hD hS => ?_⟩
  have hd : 0 < dbar d := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hD)
  have hn : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [dbar] at hd
    · exact_mod_cast h0
  have he : 0 ≤ err71 α d :=
    mul_nonneg (div_nonneg hd.le (by linarith)) (Real.rpow_nonneg hd.le _)
  have hDa := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hD
  have hDb := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hD
  have hDc := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hD
  refine ⟨fun a b => (ha n d hDa hS a b).mono (mul_le_mul_of_nonneg_right (le_max_left _ _) he),
    fun a v h => (hb n d hDb hS a v h).mono (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_max_right _ _)) he),
    fun a v b h1 h2 h3 => (hc n d hDc hS a v b h1 h2 h3).mono (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right _ _) (le_max_right _ _)) he)⟩

end LW
