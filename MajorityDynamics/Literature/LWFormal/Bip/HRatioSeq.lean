import MajorityDynamics.Literature.LWFormal.Bip.HRatio
import MajorityDynamics.Literature.LWFormal.Bip.Errors
import MajorityDynamics.Literature.LWFormal.Assembly

set_option autoImplicit true

/-!
# (35) on integer sequences: `H(d - e_a)/H(d - e_b) = R*_{ab}(d)(1 + O(με⁴))` on `Q₁¹`
-/

namespace LW.Bip

open Finset Real

variable {ℓ n : ℕ}

/-- The ideal weight `H(d) = P_ℬ(d) H̃(d)` on integer sequence pairs. -/
noncomputable def HB (ℓ n m : ℕ) (d : BSeq ℓ n) : ℝ :=
  probB ℓ n m (toN d.1) (toN d.2) * Htilde (toN d.1) (toN d.2)

/-- `μ d̄^{4φ-4}` as a function of `(ℓ, n, m)` only. -/
noncomputable def errE (φ : ℝ) (ℓ n m : ℕ) : ℝ :=
  m / (ℓ * n) * min (m / ℓ : ℝ) (m / n) ^ (4 * φ - 4)

theorem errE_swap (φ : ℝ) (ℓ n m : ℕ) : errE φ n ℓ m = errE φ ℓ n m := by
  simp only [errE, min_comm, mul_comm (n : ℝ)]

theorem mean_toN {k : ℕ} {d : Seq k} (h : ∀ i, 0 ≤ d i) : mean (toN d) = dbar d := by
  simp only [mean, dbar, M1_cast, toN_cast h]

theorem var_toN {k : ℕ} {d : Seq k} (h : ∀ i, 0 ≤ d i) : var (toN d) = sigma2 d := by
  simp only [var, sigma2, mean_toN h, toN_cast h]

theorem muN_toN {d : BSeq ℓ n} (h1 : ∀ a, 0 ≤ d.1 a) (h2 : ∀ v, 0 ≤ d.2 v) :
    muN (toN d.1) (toN d.2) = mu d := by
  simp only [muN, mu, M1_cast, toN_cast h1, toN_cast h2]; ring

theorem HB_swap (m : ℕ) (d : BSeq ℓ n) : HB n ℓ m d.swap = HB ℓ n m d := by
  simp only [HB, probB, Htilde, muN, Prod.fst_swap, Prod.snd_swap, mul_comm (n : ℕ) ℓ,
    mul_comm (2 * (n : ℝ)) (ℓ : ℝ), mul_comm (2 * (ℓ : ℝ)) (n : ℝ), add_comm (∑ v, ((toN d.2) v : ℝ))]
  ring_nf

theorem swap_sub_eT (d : BSeq ℓ n) (v : Fin n) : (d - eT v).swap = d.swap - eS v := by
  ext <;> simp [eT, eS]

theorem swap_sub_eS (d : BSeq ℓ n) (a : Fin ℓ) : (d - eS a).swap = d.swap - eT a := by
  ext <;> simp [eT, eS]

/-- The exact ratio `H(d - e_a, t)/H(d - e_b, t)` in the form of `bhratio_real`. -/
theorem HB_ratio_eq {m : ℕ} {d : BSeq ℓ n} (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmℓn : m < ℓ * n) (hM1 : M1 d.1 = m + 1) (hM2 : M1 d.2 = m)
    (hs1 : ∀ a, (1 : ℝ) ≤ d.1 a) (hsn : ∀ a, (d.1 a : ℝ) ≤ n) (ht0 : ∀ v, 0 ≤ d.2 v)
    (htℓ : ∀ v, (d.2 v : ℝ) ≤ ℓ) (a b : Fin ℓ) :
    HB ℓ n m (d - eS a) / HB ℓ n m (d - eS b) =
      (d.1 a : ℝ) / d.1 b * ((n + 1 - d.1 b) / (n + 1 - d.1 a)) *
        exp (EexpB ℓ n m (d.1 a) (d.1 b) (∑ v, ((d.2 v : ℝ) - m / n) ^ 2)) := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmℓn' : (m : ℝ) < ℓ * n := by exact_mod_cast hmℓn
  have hs0 : ∀ c, 0 ≤ d.1 c := fun c => by
    have : (1 : ℤ) ≤ d.1 c := by exact_mod_cast hs1 c
    omega
  have hpos : ∀ (c a : Fin ℓ), 0 ≤ (d.1 - e c) a := fun c a => by
    have : (1 : ℤ) ≤ d.1 a := by exact_mod_cast hs1 a
    rw [sub_e_apply]; split_ifs <;> omega
  have hk1 : ∀ c, 1 ≤ toN d.1 c := fun c => by
    have : (1 : ℤ) ≤ d.1 c := by exact_mod_cast hs1 c
    simp only [toN]; omega
  have hk : ∀ c, toN d.1 c ≤ n := fun c => by
    have : d.1 c ≤ (n : ℤ) := by exact_mod_cast hsn c
    simp only [toN]; omega
  -- the binomial ratio
  have hprod : ∀ c, ∏ i, (n.choose (toN (d.1 - e c) i) : ℝ) =
      (n.choose (toN d.1 c - 1) : ℝ) / n.choose (toN d.1 c) *
        ∏ i, (n.choose (toN d.1 i) : ℝ) := by
    intro c
    have hne : ∀ i, i ≠ c → toN (d.1 - e c) i = toN d.1 i := fun i hi => by
      simp only [toN, sub_e_apply_of_ne d.1 hi]
    have hself : toN (d.1 - e c) c = toN d.1 c - 1 := by
      simp only [toN, sub_e_apply, if_true, Int.pred_toNat]
    have hrest : ∏ i ∈ univ.erase c, (n.choose (toN (d.1 - e c) i) : ℝ) =
        ∏ i ∈ univ.erase c, (n.choose (toN d.1 i) : ℝ) :=
      prod_congr rfl fun i hi => by rw [hne i (ne_of_mem_erase hi)]
    have h0 : (n.choose (toN d.1 c) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (hk c)).ne'
    rw [← mul_prod_erase univ (fun i => (n.choose (toN (d.1 - e c) i) : ℝ)) (mem_univ c),
      ← mul_prod_erase univ (fun i => (n.choose (toN d.1 i) : ℝ)) (mem_univ c), hrest, hself]
    field_simp
  have hcast : ∀ c, ((toN d.1 c : ℕ) : ℝ) = d.1 c := toN_cast hs0
  have hPB : probB ℓ n m (toN (d - eS a).1) (toN (d - eS a).2) /
      probB ℓ n m (toN (d - eS b).1) (toN (d - eS b).2) =
      (d.1 a : ℝ) / d.1 b * ((n + 1 - d.1 b) / (n + 1 - d.1 a)) := by
    have hC : (((ℓ * n).choose m : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hmℓn.le).ne'
    have hP : ∏ i, (n.choose (toN d.1 i) : ℝ) ≠ 0 :=
      prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (Nat.choose_pos (hk i)).ne'
    have hT : ∏ v, (ℓ.choose (toN d.2 v) : ℝ) ≠ 0 :=
      prod_ne_zero_iff.2 fun v _ => by
        have h1 : toN d.2 v ≤ ℓ := by
          have : d.2 v ≤ (ℓ : ℤ) := by exact_mod_cast htℓ v
          simp only [toN]; omega
        exact_mod_cast (Nat.choose_pos h1).ne'
    have hnda : (n : ℝ) + 1 - d.1 a ≠ 0 := by linarith [hsn a]
    have hndb : (n : ℝ) + 1 - d.1 b ≠ 0 := by linarith [hsn b]
    have hda0 : (d.1 a : ℝ) ≠ 0 := by linarith [hs1 a]
    have hdb0 : (d.1 b : ℝ) ≠ 0 := by linarith [hs1 b]
    simp only [probB, sub_eS_fst, sub_eS_snd]
    rw [hprod a, hprod b, choose_pred_div _ (hk1 a) (hk a), choose_pred_div _ (hk1 b) (hk b),
      hcast, hcast]
    field_simp
  -- the exponential ratio
  have hEF : Htilde (toN (d - eS a).1) (toN (d - eS a).2) /
      Htilde (toN (d - eS b).1) (toN (d - eS b).2) =
      exp (EexpB ℓ n m (d.1 a) (d.1 b) (∑ v, ((d.2 v : ℝ) - m / n) ^ 2)) := by
    have hℓ0 : (ℓ : ℝ) ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hdbar1 : dbar d.1 = (m + 1) / ℓ := by rw [dbar, hM1]; push_cast; ring
    have hdbar2 : dbar d.2 = m / n := by simp [dbar, hM2]
    have hF : ∑ v, ((d.2 v : ℝ) - m / n) ^ 2 = n * sigma2 d.2 := by
      rw [sigma2, hdbar2]; field_simp
      exact sum_congr rfl fun v _ => by ring
    have hμ : ∀ c, muN (toN (d - eS c).1) (toN (d - eS c).2) = m / (ℓ * n) := fun c => by
      rw [muN_toN (hpos c) (by simpa using ht0), mu, sub_eS_fst, sub_eS_snd, M1_sub_e, hM1, hM2]
      push_cast; field_simp; ring
    have hmean : ∀ c, mean (toN (d - eS c).1) = m / ℓ := fun c => by
      rw [sub_eS_fst, mean_toN (hpos c), dbar_sub_e, hdbar1]; field_simp; ring
    have hvar : ∀ c, var (toN (d - eS c).1) =
        sigma2 d.1 + (1 - 1 / ℓ - 2 * ((d.1 c : ℝ) - (m + 1) / ℓ)) / ℓ := fun c => by
      rw [sub_eS_fst, var_toN (hpos c), sigma2_sub_e _ _ hℓ0, hdbar1]
    have hvart : ∀ c, var (toN (d - eS c).2) = sigma2 d.2 := fun c => by
      rw [sub_eS_snd, var_toN ht0]
    have hmeant : ∀ c, mean (toN (d - eS c).2) = m / n := fun c => by
      rw [sub_eS_snd, mean_toN ht0, hdbar2]
    unfold Htilde
    rw [← exp_sub]
    congr 1
    simp only [hμ, hmean, hvar, hvart, hmeant, hF, EexpB]
    have h1 : (m : ℝ) * (1 - m / (ℓ * n)) ≠ 0 := by
      have : (m : ℝ) / (ℓ * n) < 1 := by rw [div_lt_one (by positivity)]; exact hmℓn'
      have : (0 : ℝ) < 1 - m / (ℓ * n) := by linarith
      positivity
    field_simp
    ring
  rw [HB, HB, mul_div_mul_comm, hPB, hEF]

/-- Basic facts about `d ∈ Q₁¹`: sums, `dbar`, entry bounds. -/
theorem Q1D_facts {φ : ℝ} (hφ₁ : φ < 1) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B) {d : BSeq ℓ n}
    (hd : d ∈ Q1D φ ℓ n m) :
    M1 d.1 = m + 1 ∧ M1 d.2 = m ∧ (∀ v, 0 ≤ d.2 v) ∧ (∀ a, (1 : ℝ) ≤ d.1 a) ∧
      (∀ a, (d.1 a : ℝ) ≤ n) ∧ (∀ v, (d.2 v : ℝ) ≤ ℓ) ∧
      (∀ a, |(d.1 a : ℝ) - 1 - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ + 1) ∧
      ∀ v, |(d.2 v : ℝ) - m / n| ≤ (m / n : ℝ) ^ φ := by
  obtain ⟨hℓ, hn, hm, hμ, -, -, -, hD4, hT4, hlog⟩ := hS.bounds
  obtain ⟨a₀, hd₀⟩ := hd
  obtain ⟨hs0, ht0, hM1, hM2, hsdev, htdev⟩ := hd₀
  rw [sub_eS_snd] at ht0 htdev hM2
  have hM1' : M1 d.1 = m + 1 := by have := M1_sub_eS_fst d a₀; omega
  have hD1 : (1 : ℝ) ≤ m / ℓ := (one_le_rpow (by linarith) (by norm_num)).trans hD4
  have hT1 : (1 : ℝ) ≤ m / n := by
    have : (1 : ℝ) ≤ log n ^ (4 : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num)]
      calc (1 : ℝ) * 16 ≤ 35000 ^ (4 : ℝ) := by
            rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
        _ ≤ log n ^ (4 : ℝ) := rpow_le_rpow (by norm_num) hlog (by norm_num)
    exact this.trans hT4
  have hDφ : (m / ℓ : ℝ) ^ φ ≤ m / ℓ := by
    have := rpow_le_rpow_of_exponent_le hD1 hφ₁.le; rwa [rpow_one] at this
  have hTφ : (m / n : ℝ) ^ φ ≤ m / n := by
    have := rpow_le_rpow_of_exponent_le hT1 hφ₁.le; rwa [rpow_one] at this
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hDn : 2 * (m / ℓ : ℝ) + 2 ≤ n := by
    have : (2000 * (m / ℓ) : ℝ) ≤ n := by
      rw [mul_div_assoc', div_le_iff₀ hℓ0]; linarith
    linarith
  have hTℓ : 2 * (m / n : ℝ) ≤ ℓ := by
    have : (2000 * (m / n) : ℝ) ≤ ℓ := by
      rw [mul_div_assoc', div_le_iff₀ hn0]; linarith
    have : (0 : ℝ) ≤ m / n := by positivity
    linarith
  have hDφ' : (m / ℓ : ℝ) ^ φ < m / ℓ := by
    have hD1' : (1 : ℝ) < m / ℓ := by
      refine lt_of_lt_of_le ?_ hD4
      calc (1 : ℝ) = 1 ^ (4 : ℝ) := (one_rpow _).symm
        _ < log n ^ (4 : ℝ) := rpow_lt_rpow (by norm_num) (by linarith) (by norm_num)
    have := rpow_lt_rpow_of_exponent_lt hD1' hφ₁; rwa [rpow_one] at this
  have hδ : ∀ a, |(if a = a₀ then (1 : ℝ) else 0) - 1| ≤ 1 := fun a => by
    split_ifs <;> norm_num
  have hδ0 : ∀ a, 0 ≤ (if a = a₀ then (1 : ℝ) else 0) := fun a => by split_ifs <;> norm_num
  have hcast : ∀ a, ((d - eS a₀).1 a : ℝ) = d.1 a - if a = a₀ then 1 else 0 := fun a => by
    rw [sub_eS_fst, sub_e_apply]; push_cast; rfl
  have hsdev' : ∀ a, |(d.1 a : ℝ) - 1 - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ + 1 := fun a => by
    have h := hsdev a
    rw [hcast] at h
    calc |(d.1 a : ℝ) - 1 - m / ℓ|
        = |((d.1 a : ℝ) - (if a = a₀ then 1 else 0) - m / ℓ) +
            ((if a = a₀ then (1 : ℝ) else 0) - 1)| := by ring_nf
      _ ≤ |(d.1 a : ℝ) - (if a = a₀ then 1 else 0) - m / ℓ| +
            |(if a = a₀ then (1 : ℝ) else 0) - 1| := abs_add_le _ _
      _ ≤ _ := add_le_add h (hδ a)
  refine ⟨hM1', hM2, ht0, fun a => ?_, fun a => ?_, fun v => ?_, hsdev', htdev⟩
  · have h0 : (0 : ℝ) ≤ (d - eS a₀).1 a := by exact_mod_cast hs0 a
    rw [hcast] at h0
    have h := (abs_le.1 (hsdev a)).1
    rw [hcast] at h
    have hpos : (0 : ℝ) < d.1 a := by
      by_cases hh : a = a₀
      · subst hh; rw [if_pos rfl] at h0; linarith
      · rw [if_neg hh, sub_zero] at h; linarith
    have : (0 : ℤ) < d.1 a := by exact_mod_cast hpos
    exact_mod_cast this
  · have h := (abs_le.1 (hsdev' a)).2
    linarith
  · have h := (abs_le.1 (htdev v)).2
    linarith

set_option maxHeartbeats 1000000 in
/-- (35): `H(d - e_a)/H(d - e_b) = R*_{ab}(d)(1 + O(errH))` on `Q₁¹`. -/
theorem hratio_S {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) {m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) {d : BSeq ℓ n} (hd : d ∈ Q1D φ ℓ n m) (a b : Fin ℓ) :
    Close (HB ℓ n m (d - eS a) / HB ℓ n m (d - eS b)) (Rst a b d) (errH φ ℓ n m) := by
  obtain ⟨hℓ, hn, hm, hμ, -, hTℓ, -, hD4, hT4, hlog⟩ := hS.bounds
  obtain ⟨hM1, hM2, ht0, hs1, hsn, htℓ, hsdev, htdev⟩ := Q1D_facts (by linarith) hS hd
  set D : ℝ := m / ℓ with hDdef
  set T : ℝ := m / n with hTdef
  set F : ℝ := ∑ v, ((d.2 v : ℝ) - m / n) ^ 2 with hFdef
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hD1 : 1 ≤ D := (one_le_rpow (by linarith) (by norm_num)).trans hD4
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) ≤ log n ^ (4 : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num)]
      calc (1 : ℝ) * 16 ≤ 35000 ^ (4 : ℝ) := by
            rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
        _ ≤ log n ^ (4 : ℝ) := rpow_le_rpow (by norm_num) hlog (by norm_num)
    exact this.trans hT4
  have hD0 : 0 < D := by linarith
  have hT0 : 0 < T := by linarith
  have hmD : (m : ℝ) = D * ℓ := by rw [hDdef]; field_simp
  have hmT : (m : ℝ) = n * T := by rw [hTdef]; field_simp
  have hL1 : 1 ≤ log n := by linarith
  -- `4 s ≤ D`: `D^φ ≤ D^{3/5} ≤ D/16` since `D^{2/5} ≥ (log n)^{8/5} ≥ 16`
  have hsD : 4 * (D ^ φ + 1) ≤ D := by
    have h1 : D ^ φ ≤ D ^ (3 / 5 : ℝ) := rpow_le_rpow_of_exponent_le hD1 hφ₂.le
    have h2 : (16 : ℝ) ≤ D ^ (2 / 5 : ℝ) := by
      calc (16 : ℝ) ≤ log n := by linarith
        _ = log n ^ (1 : ℝ) := (rpow_one _).symm
        _ ≤ log n ^ (8 / 5 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = (log n ^ (4 : ℝ)) ^ (2 / 5 : ℝ) := by rw [← rpow_mul (by linarith)]; norm_num
        _ ≤ D ^ (2 / 5 : ℝ) := rpow_le_rpow (by positivity) hD4 (by norm_num)
    have h3 : D = D ^ (3 / 5 : ℝ) * D ^ (2 / 5 : ℝ) := by rw [← rpow_add hD0]; norm_num
    have h4 : 0 ≤ D ^ (3 / 5 : ℝ) := by positivity
    have h5 : 1 ≤ D ^ φ := one_le_rpow hD1 (by linarith)
    have h6 := mul_le_mul_of_nonneg_left h2 h4
    rw [← h3] at h6
    linarith
  have hs1' : (1 : ℝ) ≤ D ^ φ + 1 := by linarith [rpow_nonneg hD0.le φ]
  -- `F ≤ Φ = n T^{2φ}` and `m ≤ Φ`
  have hT2φ : (T ^ φ) ^ 2 = T ^ (2 * φ) := by
    rw [← rpow_natCast, ← rpow_mul hT0.le]; norm_num; ring_nf
  have hFΦ : F ≤ n * T ^ (2 * φ) := by
    rw [hFdef, ← hT2φ]
    calc ∑ v, ((d.2 v : ℝ) - m / n) ^ 2 ≤ ∑ _v : Fin n, (T ^ φ) ^ 2 :=
          sum_le_sum fun v _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (htdev v) 2
      _ = n * (T ^ φ) ^ 2 := by simp
  have hmΦ : (m : ℝ) ≤ n * T ^ (2 * φ) := by
    rw [hmT]
    refine mul_le_mul_of_nonneg_left ?_ hn0.le
    have := rpow_le_rpow_of_exponent_le hT1 (show (1 : ℝ) ≤ 2 * φ by linarith)
    rwa [rpow_one] at this
  -- `100 s Φ ≤ m²`: `200 T^{2φ-1} ≤ ℓ`
  have hsΦ : 100 * (D ^ φ + 1) * (n * T ^ (2 * φ)) ≤ (m : ℝ) ^ 2 := by
    have hDφD : D ^ φ ≤ D := by
      have := rpow_le_rpow_of_exponent_le hD1 (show φ ≤ 1 by linarith); rwa [rpow_one] at this
    have hTe : T ^ (2 * φ - 1) ≤ T ^ (1 / 2 : ℝ) := rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have hTℓ' : T ^ (1 / 2 : ℝ) ≤ ℓ / 200 := by
      have hs : T ^ (1 / 2 : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) := rpow_le_rpow hT0.le hTℓ (by norm_num)
      have hsq : ((ℓ : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = ℓ := by
        rw [← rpow_natCast, ← rpow_mul hℓ0.le]; norm_num
      have hℓs : (ℓ : ℝ) ^ (1 / 2 : ℝ) ≤ ℓ / 200 := by
        have h0 : 0 ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) := by positivity
        have h200 : 200 ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      exact hs.trans hℓs
    have e : (n : ℝ) * T ^ (2 * φ) = m * T ^ (2 * φ - 1) := by
      rw [hmT, show 2 * φ = (2 * φ - 1) + 1 by ring, rpow_add_one hT0.ne']; ring
    rw [e]
    have hT2 : 0 ≤ T ^ (2 * φ - 1) := by positivity
    have h1 : 100 * (D ^ φ + 1) * (m * T ^ (2 * φ - 1)) ≤ 200 * D * (m * T ^ (2 * φ - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 200 * D * (m * T ^ (2 * φ - 1)) ≤ D * m * ℓ := by
      have : 200 * T ^ (2 * φ - 1) ≤ ℓ := by linarith
      nlinarith [mul_nonneg hD0.le hm0.le]
    calc _ ≤ _ := h1
      _ ≤ D * m * ℓ := h2
      _ = (m : ℝ) ^ 2 := by rw [hmD]; ring
  have hμ' : 2000 * (m : ℝ) ≤ ℓ * n := hμ
  have key := bhratio_real (ℓ := ℓ) (n := n) (m := m) (D := D) (s := D ^ φ + 1) (sa := d.1 a)
    (sb := d.1 b) (F := F) (Φ := n * T ^ (2 * φ)) (by linarith) (by linarith) hmD hD1 hμ' hs1'
    hsD (hsdev a) (hsdev b) (by positivity) hFΦ hmΦ hsΦ
  -- identify the two sides
  have hmℓn : m < ℓ * n := by
    have : (m : ℝ) < ℓ * n := by linarith
    exact_mod_cast this
  have hℓ1 : 1 ≤ ℓ := by exact_mod_cast (by linarith : (1 : ℝ) ≤ ℓ)
  have hn1 : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
  have hlhs := HB_ratio_eq hℓ1 hn1 (by exact_mod_cast hm) hmℓn hM1 hM2 hs1 hsn ht0 htℓ a b
  have hdbar1 : dbar d.1 = (m + 1) / ℓ := by rw [dbar, hM1]; push_cast; ring
  have hdbar2 : dbar d.2 = m / n := by simp [dbar, hM2]
  have hrhs : Rst a b d = rhoB ((2 * m + 1) / (2 * ℓ * n)) (ℓ / (m + 1)) (F / (m * ℓ)) (1 / ℓ)
      (((d.1 a : ℝ) - (m + 1) / ℓ) / ((m + 1) / ℓ)) (((d.1 b : ℝ) - (m + 1) / ℓ) / ((m + 1) / ℓ)) := by
    have hmu : mu d = (2 * m + 1) / (2 * ℓ * n) := by rw [mu, hM1, hM2]; push_cast; ring
    have hδ : 1 / dbar d.1 = ℓ / (m + 1) := by rw [hdbar1, one_div_div]
    have hσ : sigma2 d.2 = F / n := by rw [sigma2, hdbar2]
    have hsT : sT d = F / (m * ℓ) := by rw [sT, hσ, hdbar2]; field_simp
    have heps : ∀ c, eps d.1 c = ((d.1 c : ℝ) - (m + 1) / ℓ) / ((m + 1) / ℓ) := fun c => by
      rw [eps, hdbar1]
    simp only [Rst]
    rw [hmu, hδ, hsT, heps, heps]
  rw [hlhs, hrhs]
  refine key.mono ?_
  -- `s ≤ 2 D^φ`
  have hs2 : D ^ φ + 1 ≤ 2 * D ^ φ := by
    linarith [one_le_rpow hD1 (by linarith : (0 : ℝ) ≤ φ)]
  have hs0 : 0 ≤ D ^ φ + 1 := by linarith
  have hΦ0 : 0 ≤ (n : ℝ) * T ^ (2 * φ) := by positivity
  have hD2φ : D ^ (2 * φ) = (D ^ φ) ^ 2 := by
    rw [← rpow_natCast, ← rpow_mul hD0.le]; norm_num; ring_nf
  unfold errH
  rw [hD2φ]
  have h1 : (D ^ φ + 1) ^ 2 ≤ 4 * (D ^ φ) ^ 2 := by nlinarith
  have hA : (D ^ φ + 1) ^ 2 * (n * T ^ (2 * φ)) ^ 2 / m ^ 4 ≤
      4 * ((D ^ φ) ^ 2 * (n * T ^ (2 * φ)) ^ 2 / m ^ 4) := by
    rw [← mul_div_assoc, ← mul_assoc]
    gcongr
  have hB : (D ^ φ + 1) * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n) ≤
      4 * (D ^ φ * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n)) := by
    rw [show 4 * (D ^ φ * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n)) =
      (4 * D ^ φ) * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n) by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hΦ0)
      (by positivity)
  have hC : (D ^ φ + 1) / (m * n) ≤ 4 * (D ^ φ / (m * n)) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

end LW.Bip
