import MajorityDynamics.Literature.LWFormal.Nbhd
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit true

/-!
# (7.4) and (7.5): `P = P^gr(1 + O(μ₁ε⁴))` on `𝔇` and `R = R^gr(1 + O(μ₁ε⁴))` on `Q₁¹`
-/

namespace LW

open Finset Real Filter

variable {n : ℕ}

/-- Number of contraction steps: `2^kIter n ≥ 128 n²`. -/
def kIter (n : ℕ) : ℕ := 2 * (Nat.log 2 n + 1) + 7

/-- Radius of the neighbourhood of `d₀ ∈ 𝔇` on which Claim 6.4 is run. -/
def rad (n : ℕ) : ℕ := 8 * Nat.log 2 n + 40

theorem two_pow_kIter (n : ℕ) : 128 * (n : ℝ) ^ 2 ≤ 2 ^ kIter n := by
  have h : (n : ℝ) ≤ 2 ^ (Nat.log 2 n + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num) n).le
  calc 128 * (n : ℝ) ^ 2 ≤ 128 * (2 ^ (Nat.log 2 n + 1)) ^ 2 := by gcongr
    _ = 2 ^ kIter n := by unfold kIter; ring

theorem natLog_le (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ 2 * log n := by
  have h : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have := log_le_log (by positivity) h
  rw [log_pow] at this
  have h2 := log_two_gt_d9
  nlinarith [(Nat.cast_nonneg (Nat.log 2 n) : (0 : ℝ) ≤ _)]

theorem inv_sq_le_err71 {α : ℝ} (hα : 1 / 2 ≤ α) {d : Seq n} (hn : (2 : ℝ) ≤ n)
    (hB1 : 1 ≤ dbar d) (hBn : dbar d ≤ n) : 1 / (n : ℝ) ^ 2 ≤ err71 α d := by
  have hB0 : 0 < dbar d := by linarith
  have h1 : dbar d / n ≤ mu d := by
    unfold mu; exact div_le_div_of_nonneg_left hB0.le (by linarith) (by linarith)
  have h2 : (dbar d ^ 2)⁻¹ ≤ dbar d ^ (4 * α - 4) := by
    have := rpow_le_rpow_of_exponent_le hB1 (show (-2 : ℝ) ≤ 4 * α - 4 by linarith)
    rwa [rpow_neg hB0.le, rpow_two] at this
  calc 1 / (n : ℝ) ^ 2 ≤ 1 / (n * dbar d) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = dbar d / n * (dbar d ^ 2)⁻¹ := by field_simp
    _ ≤ mu d * dbar d ^ (4 * α - 4) :=
        mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)

/-- For `n` large and `(n, m)` in range, every `d₀ ∈ 𝔇` is the centre of an admissible
neighbourhood of radius `rad n`, with `ε = 4C·err71(d₀) ≤ 1/1000` and `err71(d₀) ≥ 1/n²`. -/
theorem eventually_nbhd (α : ℝ) (hα₁ : 1 / 2 < α) (hα₂ : α < 3 / 5) {ω : ℕ → ℝ}
    (hω : Tendsto ω atTop atTop) (D₀ C : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω (1 / (4 * 10 ^ 9)) n m → ∀ d₀ ∈ Dset α n m,
      Nbhd α d₀ (rad n) D₀ ∧ 4 * C * err71 α d₀ ≤ 1 / 1000 ∧
        1 / (n : ℝ) ^ 2 ≤ err71 α d₀ := by
  have hL : ∀ᶠ n : ℕ in atTop,
      max 35000 (max (64 / 63 * |D₀|) (8000 * |C|)) ≤ log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hω4 : ∀ᶠ n : ℕ in atTop, 4 ≤ ω n := hω.eventually (eventually_ge_atTop 4)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_ge_atTop 48).and (hL.and hω4))
  refine ⟨N, fun n hn m hR d₀ hd₀ => ?_⟩
  obtain ⟨hn48, hlog, hω4⟩ := hN n hn
  have hn' : (48 : ℝ) ≤ n := by exact_mod_cast hn48
  have hl1 : 35000 ≤ log n := le_trans (le_max_left _ _) hlog
  have hlD : 64 / 63 * |D₀| ≤ log n := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hlog
  have hlC : 8000 * |C| ≤ log n := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hlog
  have hB : dbar d₀ = 2 * m / n := by simp [dbar, hd₀.2.1]
  have hB4 : log n ^ (4 : ℝ) ≤ dbar d₀ := by
    rw [hB]; exact (rpow_le_rpow_of_exponent_le (by linarith) hω4).trans hR.1
  have hBlog : log n ≤ dbar d₀ := by
    have := rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ log n) (show (1 : ℝ) ≤ 4 by norm_num)
    rw [rpow_one] at this; exact this.trans hB4
  have hBn : dbar d₀ ≤ n / (4 * 10 ^ 9) := by rw [hB]; linarith [hR.2]
  have hnb : Nbhd α d₀ (rad n) D₀ :=
    { α₁ := hα₁.le
      α₂ := hα₂
      n48 := hn48
      nonneg := hd₀.1
      spread := by rw [hB]; exact hd₀.2.2
      dbar_ge := by linarith
      D₀_le := by linarith [le_abs_self D₀]
      r_le := by
        have h1 : dbar d₀ ^ (1 / 2 : ℝ) ≤ dbar d₀ ^ α :=
          rpow_le_rpow_of_exponent_le (by linarith) hα₁.le
        have h2 : (log n ^ (4 : ℝ)) ^ (1 / 2 : ℝ) ≤ dbar d₀ ^ (1 / 2 : ℝ) :=
          rpow_le_rpow (by positivity) hB4 (by norm_num)
        rw [← rpow_mul (by linarith), show (4 : ℝ) * (1 / 2) = 2 by norm_num, rpow_two] at h2
        have h3 := natLog_le (by omega : 1 ≤ n)
        have : (rad n : ℝ) = 8 * Nat.log 2 n + 40 := by unfold rad; push_cast; ring
        rw [this]; nlinarith
      mu_le := by
        unfold mu; rw [div_le_iff₀ (by linarith)]; linarith }
  refine ⟨hnb, ?_, inv_sq_le_err71 hα₁.le (by linarith) (by linarith) (by linarith)⟩
  have hmu1 : mu d₀ ≤ 1 := by linarith [hnb.mu_le]
  have hβ : dbar d₀ ^ (4 * α - 4) ≤ (dbar d₀)⁻¹ := by
    have := rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ dbar d₀)
      (show 4 * α - 4 ≤ -1 by linarith)
    rwa [rpow_neg_one] at this
  have hCB : |C| * (dbar d₀)⁻¹ ≤ 1 / 8000 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith
  have he : err71 α d₀ ≤ (dbar d₀)⁻¹ := by
    unfold err71
    calc mu d₀ * dbar d₀ ^ (4 * α - 4) ≤ 1 * (dbar d₀)⁻¹ :=
          mul_le_mul hmu1 hβ (rpow_nonneg (by linarith) _) zero_le_one
      _ = _ := one_mul _
  have he0 : 0 ≤ err71 α d₀ := by
    unfold err71; exact mul_nonneg hnb.mu_pos.le (rpow_nonneg (by linarith) _)
  calc 4 * C * err71 α d₀ ≤ 4 * |C| * err71 α d₀ := by gcongr; exact le_abs_self C
    _ ≤ 4 * |C| * (dbar d₀)⁻¹ := by gcongr
    _ ≤ 1 / 1000 := by linarith

/-- The constants of Lemma 7.1(a)–(c) combined; `C ≥ 1`. -/
theorem lemma_7_1_combined (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 3 / 5) :
    ∃ C D₀ : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (d : Seq n), D₀ ≤ dbar d → Spread α d → 0 ≤ err71 α d →
      (∀ a b, Close (opR Pgr Ygr a b d) (Rgr a b d) (C * err71 α d)) ∧
      (∀ a v, a ≠ v → Close (opP Pgr Rgr a v d) (Pgr a v d) (C * err71 α d)) ∧
      (∀ a v b, a ≠ v → a ≠ b → v ≠ b →
        Close (opY Pgr Ygr a v b d) (Ygr a v b d) (C * err71 α d)) := by
  obtain ⟨Ca, Da, ha⟩ := lemma_7_1a α hα₁ hα₂
  obtain ⟨Cb, Db, hb⟩ := lemma_7_1b α hα₁ hα₂
  obtain ⟨Cc, Dc, hc⟩ := lemma_7_1c α hα₁ hα₂
  refine ⟨max 1 (max Ca (max Cb Cc)), max Da (max Db Dc), le_max_left _ _,
    fun n d hD hs he => ⟨fun a b => ?_, fun a v hav => ?_, fun a v b hav hab hvb => ?_⟩⟩
  · exact (ha n d (le_trans (le_max_left _ _) hD) hs a b).mono
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) he)
  · exact (hb n d (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hD) hs a v hav).mono
      (mul_le_mul_of_nonneg_right
        (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) he)
  · exact (hc n d (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hD) hs a v b hav hab
      hvb).mono (mul_le_mul_of_nonneg_right
        (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) he)

/-- Claim 6.4 on the ball around `d₀ ∈ 𝔇`: `χ⁽²⁺⁴ᵏ⁾ ≤ 128/2^k + 884·ε`. -/
theorem claim_6_4 {α D₀ C : ℝ} (hC : 1 ≤ C)
    (h71 : ∀ (n : ℕ) (d : Seq n), D₀ ≤ dbar d → Spread α d → 0 ≤ err71 α d →
      (∀ a b, Close (opR Pgr Ygr a b d) (Rgr a b d) (C * err71 α d)) ∧
      (∀ a v, a ≠ v → Close (opP Pgr Rgr a v d) (Pgr a v d) (C * err71 α d)) ∧
      (∀ a v b, a ≠ v → a ≠ b → v ≠ b →
        Close (opY Pgr Ygr a v b d) (Ygr a v b d) (C * err71 α d)))
    {d₀ : Seq n} (hnb : Nbhd α d₀ (rad n) D₀) (hε1 : 4 * C * err71 α d₀ ≤ 1 / 1000) :
    OK α (2 * mu d₀) (4 * C * err71 α d₀) (Ball d₀ (rad n)) := by
  have h71' := fun d (hd : d ∈ Ball d₀ (rad n)) =>
    h71 n d (hnb.dbar_ge' hd).2 (hnb.spread' hd) (hnb.err71_pos hd).le
  exact hnb.ok (by linarith) (fun d hd => (h71' d hd).1) (fun d hd => (h71' d hd).2.1)
    (fun d hd => (h71' d hd).2.2) (mul_pos (by linarith) (hnb.err71_pos (Ball_self d₀))) hε1

/-- (7.4): `P_{av}(d) = P^gr_{av}(d)(1 + O(μ₁ε⁴))` uniformly on `𝔇`. -/
theorem eq_7_4 :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω μ₀ n m →
          ∀ d ∈ Dset α n m, ∀ a v, a ≠ v →
            Close (P a v d) (Pgr a v d) (C * err71 α d) := by
  refine ⟨1 / (4 * 10 ^ 9), by norm_num, fun α hα₁ hα₂ ω hω => ?_⟩
  obtain ⟨C, D₀, hC, h71⟩ := lemma_7_1_combined α hα₁.le hα₂
  obtain ⟨N, hN⟩ := eventually_nbhd α hα₁ hα₂ hω D₀ C
  refine ⟨4 + 14160 * C, N, fun n hn m hR d hd a v hav => ?_⟩
  obtain ⟨hnb, hε1, herr⟩ := hN n hn m hR d hd
  have hok := claim_6_4 hC h71 hnb hε1
  have hmem : d ∈ Omega (Ball d (rad n)) (2 + 4 * kIter n) :=
    mem_Omega_Ball (by rw [dist1_self]; unfold rad kIter; push_cast; omega)
  have hev : IsEven d := ⟨m, by rw [hd.2.1]; ring⟩
  refine ((hok.iterate (kIter n)).1 d hmem hev a v hav).mono ?_
  have hn2 : (0 : ℝ) < 1 / n ^ 2 := by have := hnb.n_ge; positivity
  have h1 : 128 / (2 : ℝ) ^ kIter n ≤ 1 / n ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (pow_pos (by linarith [hnb.n_ge]) 2)]
    linarith [two_pow_kIter n]
  have hCe : 0 ≤ C * err71 α d := mul_nonneg (by linarith) (by linarith)
  linarith

/-- (7.5): `R_{ab}(d) = R^gr_{ab}(d)(1 + O(μ₁ε⁴))` uniformly on `Q₁¹`. -/
theorem eq_7_5 :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω μ₀ n m →
          ∀ d ∈ Q1D α n m, ∀ a b,
            Close (R a b d) (Rgr a b d) (C * err71 α d) := by
  refine ⟨1 / (4 * 10 ^ 9), by norm_num, fun α hα₁ hα₂ ω hω => ?_⟩
  obtain ⟨C, D₀, hC, h71⟩ := lemma_7_1_combined α hα₁.le hα₂
  obtain ⟨N, hN⟩ := eventually_nbhd α hα₁ hα₂ hω D₀ C
  refine ⟨4 + 14160 * C, N, fun n hn m hR d ⟨a₀, hd₀⟩ a b => ?_⟩
  obtain ⟨hnb, hε1, herr⟩ := hN n hn m hR _ hd₀
  have hok := claim_6_4 hC h71 hnb hε1
  have hmem : d ∈ Omega (Ball (d - e a₀) (rad n)) (2 + 4 * kIter n + 1) :=
    mem_Omega_Ball (by rw [dist1_comm, dist1_sub_e]; unfold rad kIter; push_cast; omega)
  have hd : d ∈ Ball (d - e a₀) (rad n) := hmem.1
  have hodd : ¬ IsEven d := by
    have : M1 d = 2 * m + 1 := by linarith [M1_sub_e d a₀, hd₀.2.1]
    unfold IsEven; rw [this, Int.even_add_one]; exact not_not.2 (even_two_mul _)
  set ε := 4 * C * err71 α (d - e a₀) with hε
  set ξ := 128 / (2 : ℝ) ^ kIter n + 884 * ε with hξ
  have hn : (48 : ℝ) ≤ n := hnb.n_ge
  have hn0 : (0 : ℝ) < n ^ 2 := pow_pos (by linarith) 2
  have h1 : 128 / (2 : ℝ) ^ kIter n ≤ 1 / n ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hn0]; linarith [two_pow_kIter n]
  have hn2 : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_one hn0]; nlinarith
  have hε0 : 0 < ε := hok.ε_pos
  have hξ0 : 0 < ξ := by positivity
  have hξ2 : ξ ≤ 2 := by linarith
  have hμ := hnb.mu_pos
  have hμ1 := hnb.mu_le
  have hR := hok.R_close (s := 2 + 4 * kIter n) (by omega) hξ0 (by nlinarith)
    (hok.iterate (kIter n)) hmem hodd a b
  refine hR.mono ?_
  have hA : 20 * (64 * (2 * mu (d - e a₀))) * ξ * (1 + ε) ≤ ξ := by
    rw [show 20 * (64 * (2 * mu (d - e a₀))) * ξ * (1 + ε) = ξ * (2560 * mu (d - e a₀) * (1 + ε))
      by ring]
    exact mul_le_of_le_one_right hξ0.le (by nlinarith)
  have hge := hnb.err71_ge hd
  have hCe := mul_le_mul_of_nonneg_left hge (by linarith : (0 : ℝ) ≤ C)
  linarith

/-- Every `d ∈ 𝔇` is graphical (Lemma 2.4(a)). -/
theorem Dset_graphical :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ m, Range ω μ₀ n m → ∀ d ∈ Dset α n m, 0 < N d := by
  refine ⟨1 / (4 * 10 ^ 9), by norm_num, fun α hα₁ hα₂ ω hω => ?_⟩
  obtain ⟨N, hN⟩ := eventually_nbhd α hα₁ hα₂ hω 0 0
  refine ⟨N, fun n hn m hR d hd => ?_⟩
  exact (hN n hn m hR d hd).1.N_pos (r := rad n) (Ball_self d) ⟨m, by rw [hd.2.1]; ring⟩

end LW
