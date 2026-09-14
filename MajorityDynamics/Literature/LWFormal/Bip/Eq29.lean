import MajorityDynamics.Literature.LWFormal.Bip.Nbhd
import MajorityDynamics.Literature.LWFormal.Bip.Statement
import MajorityDynamics.Literature.LWFormal.Eq74

set_option autoImplicit true

/-!
# (29)–(31): `P = P*(1 + O(με⁴))` on `𝔇` and `R = R*(1 + O(με⁴))` on `Q₁¹` (bipartite)
-/

namespace LW.Bip

open Finset Real Filter

variable {ℓ n : ℕ}

/-- `𝔇`: balanced nonnegative sequences with row/column sums `m` and both sides `φ`-spread. -/
def Dset (φ : ℝ) (ℓ n m : ℕ) : Set (BSeq ℓ n) :=
  {d | (∀ a, 0 ≤ d.1 a) ∧ (∀ v, 0 ≤ d.2 v) ∧ M1 d.1 = m ∧ M1 d.2 = m ∧
    (∀ a, |(d.1 a : ℝ) - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ) ∧
    ∀ v, |(d.2 v : ℝ) - m / n| ≤ (m / n : ℝ) ^ φ}

/-- `Q₁¹`: sequences `d` with `d - e_a ∈ 𝔇` for some left vertex `a`. -/
def Q1D (φ : ℝ) (ℓ n m : ℕ) : Set (BSeq ℓ n) := {d | ∃ a, d - eS a ∈ Dset φ ℓ n m}

/-- The hypotheses of Theorem 1.1 on `(ℓ, n, m)`. -/
def Range (φ : ℝ) (ω : ℕ → ℝ) (μ₀ : ℝ) (ℓ n m : ℕ) : Prop :=
  (m / (n * ℓ) : ℝ) < μ₀ ∧
  ω n * ((ℓ : ℝ) + n) ^ (5 - 5 * φ) ≤ ℓ * n * (m : ℝ) ^ (3 - 5 * φ) ∧
  (ℓ : ℝ) * log n ^ ω n + n * log ℓ ^ ω n ≤ m

/-- The integer sequence pair of `(s, t)`. -/
def toSeq (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : BSeq ℓ n := (fun a => (s a : ℤ), fun v => (t v : ℤ))

theorem toSeq_mem_Dset {φ : ℝ} {m : ℕ} {s : Fin ℓ → ℕ} {t : Fin n → ℕ}
    (h : InD φ ℓ n m s t) : toSeq s t ∈ Dset φ ℓ n m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun a => Int.natCast_nonneg _, fun v => Int.natCast_nonneg _, ?_, ?_, h3, h4⟩
  · show ∑ a, ((s a : ℕ) : ℤ) = (m : ℤ); exact_mod_cast h1
  · show ∑ v, ((t v : ℕ) : ℤ) = (m : ℤ); exact_mod_cast h2

theorem dbar_fst_Dset {φ : ℝ} {m : ℕ} {d : BSeq ℓ n} (hd : d ∈ Dset φ ℓ n m) :
    dbar d.1 = m / ℓ := by simp [dbar, hd.2.2.1]

theorem dbar_snd_Dset {φ : ℝ} {m : ℕ} {d : BSeq ℓ n} (hd : d ∈ Dset φ ℓ n m) :
    dbar d.2 = m / n := by simp [dbar, hd.2.2.2.1]

theorem bal_Dset {φ : ℝ} {m : ℕ} {d : BSeq ℓ n} (hd : d ∈ Dset φ ℓ n m) : Bal d := by
  unfold Bal; rw [hd.2.2.1, hd.2.2.2.1]

theorem mu_Dset {φ : ℝ} {m : ℕ} {d : BSeq ℓ n} (hd : d ∈ Dset φ ℓ n m) (hℓ : (ℓ : ℝ) ≠ 0)
    (hn : (n : ℝ) ≠ 0) : mu d = m / (ℓ * n) := by
  unfold mu; rw [hd.2.2.1, hd.2.2.2.1]; field_simp; push_cast; ring

/-- Consequences of `Range` for `n` large: `ℓ ≥ 2√n`, `n ≥ 2√ℓ`, `m ≤ ℓn`. -/
theorem range_sizes {φ : ℝ} (hφ₁ : 1 / 2 ≤ φ) (hφ₂ : φ < 3 / 5) {ω : ℕ → ℝ} {μ₀ : ℝ}
    (hμ₀ : μ₀ ≤ 1) {ℓ n m : ℕ} (hn : (1 : ℝ) ≤ n) (hω : 4 ≤ ω n) (hR : Range φ ω μ₀ ℓ n m) :
    (1 : ℝ) ≤ ℓ ∧ 4 * (n : ℝ) ≤ ℓ ^ 2 ∧ 4 * (ℓ : ℝ) ≤ n ^ 2 ∧ (m : ℝ) ≤ ℓ * n := by
  obtain ⟨h1, h2, h3⟩ := hR
  set x : ℝ := (ℓ : ℝ)
  set y : ℝ := (n : ℝ)
  set M : ℝ := (m : ℝ)
  have hy : 0 < y := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hβ : (2 : ℝ) < 5 - 5 * φ := by linarith
  have hγ : (0 : ℝ) ≤ 3 - 5 * φ := by linarith
  have hx1 : (1 : ℝ) ≤ x := by
    by_contra hlt
    have hx : x = 0 := by
      have : ℓ = 0 := by
        by_contra hne
        have : (1 : ℝ) ≤ ℓ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
        exact hlt this
      simp [x, this]
    rw [hx] at h2
    have : 0 < ω n * y ^ (5 - 5 * φ) := mul_pos (by linarith) (rpow_pos_of_pos hy _)
    simp at h2; linarith
  have hx : 0 < x := by linarith
  have hMxy : M ≤ x * y := by
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [mul_le_mul_of_nonneg_right hμ₀ (by positivity : (0 : ℝ) ≤ n * ℓ)]
  refine ⟨hx1, ?_, ?_, hMxy⟩
  · -- `ω n · y^β ≤ x^{β-1} y^{β-1}` hence `4 y ≤ x^{β-1} ≤ x²`
    have hA : ω n * y ^ (5 - 5 * φ) ≤ x * y * M ^ (3 - 5 * φ) :=
      (mul_le_mul_of_nonneg_left (rpow_le_rpow hy.le (by linarith : y ≤ x + y) (by linarith))
        (by linarith)).trans h2
    have hB : M ^ (3 - 5 * φ) ≤ x ^ (3 - 5 * φ) * y ^ (3 - 5 * φ) := by
      rw [← mul_rpow hx0 hy.le]; exact rpow_le_rpow hM0 hMxy hγ
    have hC : x * y * (x ^ (3 - 5 * φ) * y ^ (3 - 5 * φ)) =
        x ^ (4 - 5 * φ) * (y ^ (4 - 5 * φ)) := by
      rw [show (4 - 5 * φ) = 1 + (3 - 5 * φ) by ring, rpow_add hx, rpow_add hy, rpow_one,
        rpow_one]; ring
    have hD : y ^ (5 - 5 * φ) = y * y ^ (4 - 5 * φ) := by
      rw [show (5 - 5 * φ) = 1 + (4 - 5 * φ) by ring, rpow_add hy, rpow_one]
    have hE : ω n * y * y ^ (4 - 5 * φ) ≤ x ^ (4 - 5 * φ) * y ^ (4 - 5 * φ) := by
      calc ω n * y * y ^ (4 - 5 * φ) = ω n * y ^ (5 - 5 * φ) := by rw [hD]; ring
        _ ≤ x * y * M ^ (3 - 5 * φ) := hA
        _ ≤ x * y * (x ^ (3 - 5 * φ) * y ^ (3 - 5 * φ)) := by gcongr
        _ = _ := hC
    have hF : ω n * y ≤ x ^ (4 - 5 * φ) :=
      le_of_mul_le_mul_right hE (rpow_pos_of_pos hy _)
    have hG : x ^ (4 - 5 * φ) ≤ x ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [rpow_two] at hG
    nlinarith
  · have hA : ω n * x ^ (5 - 5 * φ) ≤ x * y * M ^ (3 - 5 * φ) :=
      (mul_le_mul_of_nonneg_left (rpow_le_rpow hx0 (by linarith : x ≤ x + y) (by linarith))
        (by linarith)).trans h2
    have hB : M ^ (3 - 5 * φ) ≤ x ^ (3 - 5 * φ) * y ^ (3 - 5 * φ) := by
      rw [← mul_rpow hx0 hy.le]; exact rpow_le_rpow hM0 hMxy hγ
    have hC : x * y * (x ^ (3 - 5 * φ) * y ^ (3 - 5 * φ)) =
        x ^ (4 - 5 * φ) * (y ^ (4 - 5 * φ)) := by
      rw [show (4 - 5 * φ) = 1 + (3 - 5 * φ) by ring, rpow_add hx, rpow_add hy, rpow_one,
        rpow_one]; ring
    have hD : x ^ (5 - 5 * φ) = x * x ^ (4 - 5 * φ) := by
      rw [show (5 - 5 * φ) = 1 + (4 - 5 * φ) by ring, rpow_add hx, rpow_one]
    have hE : ω n * x * x ^ (4 - 5 * φ) ≤ y ^ (4 - 5 * φ) * x ^ (4 - 5 * φ) := by
      calc ω n * x * x ^ (4 - 5 * φ) = ω n * x ^ (5 - 5 * φ) := by rw [hD]; ring
        _ ≤ x * y * M ^ (3 - 5 * φ) := hA
        _ ≤ x * y * (x ^ (3 - 5 * φ) * y ^ (3 - 5 * φ)) := by gcongr
        _ = _ := by rw [hC]; ring
    have hF : ω n * x ≤ y ^ (4 - 5 * φ) :=
      le_of_mul_le_mul_right hE (rpow_pos_of_pos hx _)
    have hG : y ^ (4 - 5 * φ) ≤ y ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le hn (by linarith)
    rw [rpow_two] at hG
    nlinarith

theorem natLog_mul_le {ℓ n : ℕ} (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) (hℓn : (ℓ : ℝ) ≤ n ^ 2) :
    (Nat.log 2 (ℓ * n) : ℝ) ≤ 6 * log n := by
  have h := natLog_le (n := ℓ * n) (Nat.one_le_iff_ne_zero.2 (by positivity))
  have h2 : log ((ℓ * n : ℕ) : ℝ) ≤ 3 * log n := by
    push_cast
    rw [log_mul (by positivity) (by positivity)]
    have : log ℓ ≤ log ((n : ℝ) ^ 2) := log_le_log (by positivity) hℓn
    rw [log_pow] at this; push_cast at this; linarith
  linarith

theorem inv_sq_le_err41 {φ : ℝ} (hφ : 1 / 2 ≤ φ) {m : ℕ} {d : BSeq ℓ n} (hd : d ∈ Dset φ ℓ n m)
    (hℓ : (1 : ℝ) ≤ ℓ) (hn : (1 : ℝ) ≤ n) (hm1 : (1 : ℝ) ≤ dmin d) (hm : (m : ℝ) ≤ ℓ * n) :
    1 / ((ℓ : ℝ) * n) ^ 2 ≤ err41 φ d := by
  have hS := dbar_fst_Dset hd
  have hT := dbar_snd_Dset hd
  have hμ := mu_Dset hd (by linarith) (by linarith)
  have hD0 : 0 < dmin d := by linarith
  have hm0 : (0 : ℝ) < m := by
    have : (1 : ℝ) ≤ dbar d.1 := le_trans hm1 (min_le_left _ _)
    rw [hS, le_div_iff₀ (by linarith)] at this; linarith
  have h2 : (dmin d ^ 2)⁻¹ ≤ dmin d ^ (4 * φ - 4) := by
    have := rpow_le_rpow_of_exponent_le hm1 (show (-2 : ℝ) ≤ 4 * φ - 4 by linarith)
    rwa [rpow_neg hD0.le, rpow_two] at this
  have hm1S : dmin d ≤ dbar d.1 := min_le_left _ _
  have hm1T : dmin d ≤ dbar d.2 := min_le_right _ _
  have h3 : dmin d ^ 2 ≤ dbar d.1 * dbar d.2 := by
    rw [pow_two]; exact mul_le_mul hm1S hm1T hD0.le (by linarith)
  rw [hS, hT] at h3
  have hμ0 : 0 ≤ mu d := by rw [hμ]; positivity
  have h4 : (1 : ℝ) / m ≤ mu d * (dmin d ^ 2)⁻¹ := by
    rw [hμ]
    calc (1 : ℝ) / m = m / (ℓ * n) * ((m : ℝ) / ℓ * ((m : ℝ) / n))⁻¹ := by field_simp
      _ ≤ m / (ℓ * n) * (dmin d ^ 2)⁻¹ := by gcongr
  have hℓn1 : (1 : ℝ) ≤ ℓ * n := by nlinarith
  calc 1 / ((ℓ : ℝ) * n) ^ 2 ≤ 1 / m := by
        apply one_div_le_one_div_of_le hm0; nlinarith
    _ ≤ mu d * (dmin d ^ 2)⁻¹ := h4
    _ ≤ err41 φ d := mul_le_mul_of_nonneg_left h2 hμ0

/-- Elementary bounds on `log n` used below. -/
theorem log_bounds {L : ℝ} (hL : 35000 ≤ L) :
    35000 * L ≤ L ^ (4 : ℝ) / 16 ∧ (L ^ (4 : ℝ) / 16) ^ (1 / 2 : ℝ) = L ^ 2 / 4 ∧
      L ≤ L ^ (4 : ℝ) / 16 := by
  have hL0 : 0 ≤ L := by linarith
  have h4 : L ^ (4 : ℝ) = L ^ 2 * L ^ 2 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]; ring
  have h2 : 35000 * L ≤ L ^ 2 := by nlinarith
  have hA : 35000 * L ≤ L ^ (4 : ℝ) / 16 := by
    rw [h4]; nlinarith [mul_le_mul h2 h2 (by positivity) (by positivity)]
  refine ⟨hA, ?_, by linarith⟩
  rw [show L ^ (4 : ℝ) / 16 = (L ^ 2 / 4) ^ (2 : ℝ) by rw [rpow_two, h4]; ring,
    ← rpow_mul (by positivity)]
  norm_num

/-- Size conditions on `(ℓ, n, m)`, symmetric in `(ℓ, n)`: both logs `≥ B ≥ 35000`,
`4n ≤ ℓ²`, `4ℓ ≤ n²`, `μ ≤ 1/(2·10⁹)`, and both means `≥ (max log)^K` with `K ≥ 4`. -/
structure Sizes (ℓ n m : ℕ) (K B : ℝ) : Prop where
  B_ge : 35000 ≤ B
  logℓ : B ≤ log ℓ
  logn : B ≤ log n
  ℓn : 4 * (n : ℝ) ≤ ℓ ^ 2
  nℓ : 4 * (ℓ : ℝ) ≤ n ^ 2
  mu_le : (m : ℝ) / (ℓ * n) ≤ 1 / (2 * 10 ^ 9)
  K_ge : 4 ≤ K
  s_ge : max (log ℓ) (log n) ^ K ≤ m / ℓ
  t_ge : max (log ℓ) (log n) ^ K ≤ m / n

theorem Sizes.swap {ℓ n m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) : Sizes n ℓ m K B where
  B_ge := h.B_ge
  logℓ := h.logn
  logn := h.logℓ
  ℓn := h.nℓ
  nℓ := h.ℓn
  mu_le := by rw [mul_comm]; exact h.mu_le
  K_ge := h.K_ge
  s_ge := by rw [max_comm]; exact h.t_ge
  t_ge := by rw [max_comm]; exact h.s_ge

theorem natCast_ge_of_log {n : ℕ} {B : ℝ} (hB : 1 ≤ B) (h : B ≤ log n) :
    1 + B + B ^ 2 / 2 ≤ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp at h; linarith
  · have := quadratic_le_exp_of_nonneg (by linarith : 0 ≤ B)
    have h2 := exp_le_exp.2 h
    rw [exp_log (by exact_mod_cast hn)] at h2
    linarith

/-- Basic consequences of `Sizes`. -/
theorem Sizes.basic {ℓ n m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) :
    (576 : ℝ) ≤ ℓ ∧ (576 : ℝ) ≤ n ∧ (m : ℝ) ≤ ℓ * n ∧ (ℓ : ℝ) ≤ n ^ 2 ∧
      log n ^ (4 : ℝ) ≤ m / ℓ ∧ log n ^ (4 : ℝ) / 16 ≤ m / n ∧ 35000 ≤ log n := by
  have hB := h.B_ge
  have hℓ := natCast_ge_of_log (by linarith) h.logℓ
  have hn := natCast_ge_of_log (by linarith) h.logn
  have hln : 35000 ≤ log n := hB.trans h.logn
  have hℓn : (0 : ℝ) < ℓ * n := mul_pos (by nlinarith) (by nlinarith)
  have hm : (m : ℝ) ≤ ℓ * n := by
    have := h.mu_le
    rw [div_le_iff₀ hℓn] at this
    nlinarith
  have hnℓ := h.nℓ
  have hpow : log n ^ (4 : ℝ) ≤ max (log ℓ) (log n) ^ K :=
    (rpow_le_rpow_of_exponent_le (by linarith) h.K_ge).trans
      (rpow_le_rpow (by linarith) (le_max_right _ _) (by linarith [h.K_ge]))
  refine ⟨by nlinarith, by nlinarith, hm, by nlinarith, hpow.trans h.s_ge, ?_, hln⟩
  have := hpow.trans h.t_ge
  have h0 : 0 ≤ log n ^ (4 : ℝ) := by positivity
  linarith

/-- `Range` implies `Sizes ℓ n m K B` for `n` large. -/
theorem sizes_of_range (φ : ℝ) (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) {ω : ℕ → ℝ}
    (hω : Tendsto ω atTop atTop) {K B : ℝ} (hK : 4 ≤ K) (hB : 35000 ≤ B) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ℓ m, Range φ ω (1 / (2 * 10 ^ 9)) ℓ n m → Sizes ℓ n m K B := by
  have hL : ∀ᶠ n : ℕ in atTop, max (2 * B) ((2 : ℝ) ^ K) ≤ log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hω' : ∀ᶠ n : ℕ in atTop, 2 * K + 2 ≤ ω n := hω.eventually (eventually_ge_atTop _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_ge_atTop 1).and (hL.and hω'))
  refine ⟨N, fun n hn ℓ m hR => ?_⟩
  obtain ⟨hn1, hlog, hωK⟩ := hN n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlB : 2 * B ≤ log n := (le_max_left _ _).trans hlog
  have hl2K : (2 : ℝ) ^ K ≤ log n := (le_max_right _ _).trans hlog
  have hω4 : 4 ≤ ω n := by linarith
  obtain ⟨hℓ1, hℓn, hnℓ, hmℓn⟩ := range_sizes hφ₁.le hφ₂ (by norm_num) hn' hω4 hR
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogℓ : log n / 2 ≤ log ℓ := by
    have : log (4 * n) ≤ log ((ℓ : ℝ) ^ 2) := log_le_log (by positivity) hℓn
    rw [log_pow, log_mul (by norm_num) hn0.ne'] at this
    push_cast at this; linarith [log_pos (by norm_num : (1 : ℝ) < 4)]
  have hlogℓ' : log ℓ ≤ 2 * log n := by
    have : log (4 * ℓ) ≤ log ((n : ℝ) ^ 2) := log_le_log (by positivity) hnℓ
    rw [log_pow, log_mul (by norm_num) hℓ0.ne'] at this
    push_cast at this; linarith [log_pos (by norm_num : (1 : ℝ) < 4)]
  have hL1 : 1 ≤ log n := by linarith
  have hmax : max (log ℓ) (log n) ≤ 2 * log n := max_le hlogℓ' (by linarith)
  have hmax0 : 0 ≤ max (log ℓ) (log n) := le_max_of_le_right (by linarith)
  -- `(2 log n)^K ≤ (log n)^{K+1} ≤ (log n)^{ω n}`
  have hK0 : 0 ≤ K := by linarith
  have hkey : max (log ℓ) (log n) ^ K ≤ log n ^ ω n := by
    calc max (log ℓ) (log n) ^ K ≤ (2 * log n) ^ K := rpow_le_rpow hmax0 hmax hK0
      _ = 2 ^ K * log n ^ K := mul_rpow (by norm_num) (by linarith)
      _ ≤ log n * log n ^ K := by gcongr
      _ = log n ^ (K + 1) := by rw [rpow_add_one (by linarith), mul_comm]
      _ ≤ log n ^ ω n := rpow_le_rpow_of_exponent_le hL1 (by linarith)
  -- `(log n)^{K+1} ≤ (log n / 2)^{2K+2} ≤ (log ℓ)^{ω n}`
  have hkey2 : max (log ℓ) (log n) ^ K ≤ log ℓ ^ ω n := by
    have h1 : log n ^ (K + 1) ≤ (log n / 2) ^ (2 * K + 2) := by
      rw [show 2 * K + 2 = 2 * (K + 1) by ring, rpow_mul (by linarith), rpow_two]
      exact rpow_le_rpow (by linarith) (by nlinarith) (by linarith)
    calc max (log ℓ) (log n) ^ K ≤ (2 * log n) ^ K := rpow_le_rpow hmax0 hmax hK0
      _ = 2 ^ K * log n ^ K := mul_rpow (by norm_num) (by linarith)
      _ ≤ log n * log n ^ K := by gcongr
      _ = log n ^ (K + 1) := by rw [rpow_add_one (by linarith), mul_comm]
      _ ≤ (log n / 2) ^ (2 * K + 2) := h1
      _ ≤ (log n / 2) ^ ω n := rpow_le_rpow_of_exponent_le (by linarith) hωK
      _ ≤ log ℓ ^ ω n := rpow_le_rpow (by linarith) hlogℓ (by linarith)
  have h3 := hR.2.2
  exact
    { B_ge := hB
      logℓ := by linarith
      logn := by linarith
      ℓn := hℓn
      nℓ := hnℓ
      mu_le := by rw [mul_comm]; exact hR.1.le
      K_ge := hK
      s_ge := by
        rw [le_div_iff₀ hℓ0]
        have h0 : 0 ≤ (n : ℝ) * log ℓ ^ ω n := by positivity
        nlinarith
      t_ge := by
        rw [le_div_iff₀ hn0]
        have h0 : 0 ≤ (ℓ : ℝ) * log n ^ ω n := by positivity
        nlinarith }

/-- Under `Sizes`, every `d₀ ∈ 𝔇` is the centre of an admissible neighbourhood of radius
`rad (ℓ n)`, with `ε = 4C·err41(d₀) ≤ 1/1000` and `err41(d₀) ≥ 1/(ℓn)²`. -/
theorem nbhd_of_sizes (φ : ℝ) (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) (D₀ C : ℝ) {ℓ n m : ℕ}
    {K B : ℝ} (hSz : Sizes ℓ n m K B) (hlD : 64 / 63 * |D₀| ≤ B) (hlC : 8000 * |C| ≤ B) :
    ∀ d₀ ∈ Dset φ ℓ n m,
      Nbhd φ d₀ (rad (ℓ * n)) D₀ ∧ 4 * C * err41 φ d₀ ≤ 1 / 1000 ∧
        1 / ((ℓ : ℝ) * n) ^ 2 ≤ err41 φ d₀ := by
  intro d₀ hd₀
  obtain ⟨hℓ576, hn', hmℓn, hℓn2, hS4, hT4, hl1⟩ := hSz.basic
  have hlD : 64 / 63 * |D₀| ≤ log n := hlD.trans hSz.logn
  have hlC : 8000 * |C| ≤ log n := hlC.trans hSz.logn
  have hℓ1 : (1 : ℝ) ≤ ℓ := by linarith
  have hℓ48 : (48 : ℝ) ≤ ℓ := by linarith
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hS := dbar_fst_Dset hd₀
  have hT := dbar_snd_Dset hd₀
  have hμ := mu_Dset hd₀ hℓ0.ne' hn0.ne'
  rw [← hS] at hS4
  rw [← hT] at hT4
  obtain ⟨hbig, hsqrt, hlogle⟩ := log_bounds hl1
  have hl40 : 0 ≤ log n ^ (4 : ℝ) := by positivity
  have hdmin : log n ^ (4 : ℝ) / 16 ≤ dmin d₀ := le_min (by linarith) hT4
  have hD35 : 35000 ≤ dmin d₀ := by nlinarith
  have hlogdmin : log n ≤ dmin d₀ := by linarith
  have hmu : mu d₀ ≤ 1 / (2 * 10 ^ 9) := by rw [hμ]; exact hSz.mu_le
  have hrad : (rad (ℓ * n) : ℝ) ≤ 48 * log n + 40 := by
    have h4 := natLog_mul_le (by exact_mod_cast hℓ1) (by exact_mod_cast hn0) hℓn2
    have : (rad (ℓ * n) : ℝ) = 8 * Nat.log 2 (ℓ * n) + 40 := by unfold rad; push_cast; ring
    rw [this]; linarith
  have hnb : Nbhd φ d₀ (rad (ℓ * n)) D₀ :=
    { φ₁ := hφ₁.le
      φ₂ := hφ₂
      ℓ48 := by exact_mod_cast hℓ48
      n48 := by exact_mod_cast (by linarith : (48 : ℝ) ≤ n)
      bal := bal_Dset hd₀
      spreadS := by rw [hS]; exact hd₀.2.2.2.2.1
      spreadT := by rw [hT]; exact hd₀.2.2.2.2.2
      dmin_ge := hD35
      D₀_le := by linarith [le_abs_self D₀]
      r_le := by
        have h1 : dmin d₀ ^ (1 / 2 : ℝ) ≤ dmin d₀ ^ φ :=
          rpow_le_rpow_of_exponent_le (by linarith) hφ₁.le
        have h2 : (log n ^ (4 : ℝ) / 16) ^ (1 / 2 : ℝ) ≤ dmin d₀ ^ (1 / 2 : ℝ) :=
          rpow_le_rpow (by positivity) hdmin (by norm_num)
        rw [hsqrt] at h2
        nlinarith
      mu_le := hmu }
  have hD1 : (1 : ℝ) ≤ dmin d₀ := by linarith
  refine ⟨hnb, ?_, inv_sq_le_err41 hφ₁.le hd₀ hℓ1 (by linarith) hD1 hmℓn⟩
  have hmu1 : mu d₀ ≤ 1 := by linarith
  have hβ : dmin d₀ ^ (4 * φ - 4) ≤ (dmin d₀)⁻¹ := by
    have := rpow_le_rpow_of_exponent_le hD1 (show 4 * φ - 4 ≤ -1 by linarith)
    rwa [rpow_neg_one] at this
  have hCB : |C| * (dmin d₀)⁻¹ ≤ 1 / 8000 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith
  have he : err41 φ d₀ ≤ (dmin d₀)⁻¹ := by
    unfold err41
    calc mu d₀ * dmin d₀ ^ (4 * φ - 4) ≤ 1 * (dmin d₀)⁻¹ :=
          mul_le_mul hmu1 hβ (rpow_nonneg (by linarith) _) zero_le_one
      _ = _ := one_mul _
  have he0 : 0 ≤ err41 φ d₀ := by
    unfold err41; exact mul_nonneg hnb.mu_pos.le (rpow_nonneg (by linarith) _)
  calc 4 * C * err41 φ d₀ ≤ 4 * |C| * err41 φ d₀ := by gcongr; exact le_abs_self C
    _ ≤ 4 * |C| * (dmin d₀)⁻¹ := by gcongr
    _ ≤ 1 / 1000 := by linarith

/-- The constants of Lemma 4.1(a)–(c) combined; `C ≥ 1`. -/
theorem lemma_4_1_combined (φ : ℝ) (hφ₁ : 1 / 2 ≤ φ) (hφ₂ : φ < 3 / 5) :
    ∃ C D₀ : ℝ, 1 ≤ C ∧ ∀ (ℓ n : ℕ) (d : BSeq ℓ n), D₀ ≤ dmin d → Spread φ d → 0 ≤ err41 φ d →
      (SH d → ∀ a b, Close (opR Pst Yst a b d) (Rst a b d) (C * err41 φ d)) ∧
      (Bal d → ∀ a v, Close (opP Pst Rst a v d) (Pst a v d) (C * err41 φ d)) ∧
      (Bal d → ∀ a v b, a ≠ b →
        Close (opY Pst Yst a v b d) (Yst a v b d) (C * err41 φ d)) := by
  obtain ⟨Ca, Da, ha⟩ := lemma_4_1a φ hφ₁ hφ₂
  obtain ⟨Cb, Db, hb⟩ := lemma_4_1b φ hφ₁ hφ₂
  obtain ⟨Cc, Dc, hc⟩ := lemma_4_1c φ hφ₁ hφ₂
  refine ⟨max 1 (max Ca (max Cb Cc)), max Da (max Db Dc), le_max_left _ _,
    fun ℓ n d hD hs he => ⟨fun hSH a b => ?_, fun hbal a v => ?_, fun hbal a v b hab => ?_⟩⟩
  · exact (ha ℓ n d (le_trans (le_max_left _ _) hD) hs hSH a b).mono
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) he)
  · exact (hb ℓ n d (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hD) hs hbal a v).mono
      (mul_le_mul_of_nonneg_right
        (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) he)
  · exact (hc ℓ n d (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hD) hs hbal a v b
      hab).mono (mul_le_mul_of_nonneg_right
        (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) he)

/-- Claim 4.2 on the ball around `d₀ ∈ 𝔇`. -/
theorem claim_4_2 {φ D₀ C : ℝ} (hC : 1 ≤ C)
    (h41 : ∀ (ℓ n : ℕ) (d : BSeq ℓ n), D₀ ≤ dmin d → Spread φ d → 0 ≤ err41 φ d →
      (SH d → ∀ a b, Close (opR Pst Yst a b d) (Rst a b d) (C * err41 φ d)) ∧
      (Bal d → ∀ a v, Close (opP Pst Rst a v d) (Pst a v d) (C * err41 φ d)) ∧
      (Bal d → ∀ a v b, a ≠ b →
        Close (opY Pst Yst a v b d) (Yst a v b d) (C * err41 φ d)))
    {d₀ : BSeq ℓ n} {r : ℕ} (hnb : Nbhd φ d₀ r D₀) (hε1 : 4 * C * err41 φ d₀ ≤ 1 / 1000) :
    OK φ (2 * mu d₀) (4 * C * err41 φ d₀) (Ball d₀ r) := by
  have h41' := fun d (hd : d ∈ Ball d₀ r) =>
    h41 ℓ n d (hnb.dmin_ge' hd).2 (hnb.spread' hd) (hnb.err41_pos hd).le
  exact hnb.ok (by linarith) (fun d hd => (h41' d hd).1) (fun d hd => (h41' d hd).2.1)
    (fun d hd => (h41' d hd).2.2) (mul_pos (by linarith) (hnb.err41_pos (Ball_self d₀))) hε1

/-- (29): `P_{av}(d) = P*_{av}(d)(1 + O(με⁴))` uniformly on `𝔇`. -/
theorem eq_29 (φ : ℝ) (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) :
    ∃ C B₀ : ℝ, ∀ {ℓ n m : ℕ} {K B : ℝ}, Sizes ℓ n m K B → B₀ ≤ B →
      ∀ d ∈ Dset φ ℓ n m, ∀ a v, Close (P a v d) (Pst a v d) (C * err41 φ d) := by
  obtain ⟨C, D₀, hC, h41⟩ := lemma_4_1_combined φ hφ₁.le hφ₂
  refine ⟨4 + 14160 * C, max (64 / 63 * |D₀|) (8000 * |C|),
    fun {ℓ n m K B} hS hB d hd a v => ?_⟩
  obtain ⟨hnb, hε1, herr⟩ := nbhd_of_sizes φ hφ₁ hφ₂ D₀ C hS ((le_max_left _ _).trans hB)
    ((le_max_right _ _).trans hB) d hd
  have hok := claim_4_2 hC h41 hnb hε1
  have hmem : d ∈ Omega (Ball d (rad (ℓ * n))) (2 + 4 * kIter (ℓ * n)) :=
    mem_Omega_Ball (by rw [dist1_self]; unfold rad kIter; push_cast; omega)
  refine ((hok.iterate (kIter (ℓ * n))).1 d hmem (bal_Dset hd) a v).mono ?_
  have hℓn : (0 : ℝ) < ℓ * n := by
    have := hnb.ℓ_ge; have := hnb.n_ge; positivity
  have h1 : 128 / (2 : ℝ) ^ kIter (ℓ * n) ≤ 1 / (ℓ * n) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (pow_pos hℓn 2)]
    have := two_pow_kIter (ℓ * n); push_cast at this; linarith
  have he0 : 0 ≤ err41 φ d := (hnb.err41_pos (Ball_self d)).le
  have hCe : 0 ≤ C * err41 φ d := mul_nonneg (by linarith) he0
  linarith

/-- (30): `R_{ab}(d) = R*_{ab}(d)(1 + O(με⁴))` uniformly on `Q₁¹`. -/
theorem eq_30 (φ : ℝ) (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) :
    ∃ C B₀ : ℝ, ∀ {ℓ n m : ℕ} {K B : ℝ}, Sizes ℓ n m K B → B₀ ≤ B →
      ∀ d ∈ Q1D φ ℓ n m, ∀ a b, Close (R a b d) (Rst a b d) (C * err41 φ d) := by
  obtain ⟨C, D₀, hC, h41⟩ := lemma_4_1_combined φ hφ₁.le hφ₂
  refine ⟨4 + 14160 * C, max (64 / 63 * |D₀|) (8000 * |C|),
    fun {ℓ n m K B} hS hB d ⟨a₀, hd₀⟩ a b => ?_⟩
  obtain ⟨hnb, hε1, herr⟩ := nbhd_of_sizes φ hφ₁ hφ₂ D₀ C hS ((le_max_left _ _).trans hB)
    ((le_max_right _ _).trans hB) _ hd₀
  have hok := claim_4_2 hC h41 hnb hε1
  have hmem : d ∈ Omega (Ball (d - eS a₀) (rad (ℓ * n))) (2 + 4 * kIter (ℓ * n) + 1) :=
    mem_Omega_Ball (by rw [dist1_comm, dist1_sub_eS]; unfold rad kIter; push_cast; omega)
  have hd : d ∈ Ball (d - eS a₀) (rad (ℓ * n)) := hmem.1
  have hSH : SH d := by
    have h1 := bal_Dset hd₀
    unfold SH; unfold Bal at h1; rw [M1_sub_eS_fst, sub_eS_snd] at h1; omega
  set ε := 4 * C * err41 φ (d - eS a₀) with hε
  set ξ := 128 / (2 : ℝ) ^ kIter (ℓ * n) + 884 * ε with hξ
  have hℓn : (1 : ℝ) ≤ ℓ * n := by
    have := hnb.ℓ_ge; have := hnb.n_ge; nlinarith
  have hn0 : (0 : ℝ) < (ℓ * n) ^ 2 := by positivity
  have h1 : 128 / (2 : ℝ) ^ kIter (ℓ * n) ≤ 1 / (ℓ * n) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hn0]
    have := two_pow_kIter (ℓ * n); push_cast at this; linarith
  have hn2 : 1 / ((ℓ : ℝ) * n) ^ 2 ≤ 1 := by rw [div_le_one hn0]; nlinarith
  have hε0 : 0 < ε := hok.ε_pos
  have hξ0 : 0 < ξ := by positivity
  have hξ2 : ξ ≤ 2 := by linarith
  have hμ := hnb.mu_pos
  have hμ1 := hnb.mu_le
  have hR := hok.R_close (s := 2 + 4 * kIter (ℓ * n)) (by omega) hξ0 (by nlinarith)
    (hok.iterate (kIter (ℓ * n))) hmem hSH a b
  refine hR.mono ?_
  have hA : 20 * (64 * (2 * mu (d - eS a₀))) * ξ * (1 + ε) ≤ ξ := by
    rw [show 20 * (64 * (2 * mu (d - eS a₀))) * ξ * (1 + ε) =
      ξ * (2560 * mu (d - eS a₀) * (1 + ε)) by ring]
    exact mul_le_of_le_one_right hξ0.le (by nlinarith)
  have hge := hnb.err41_ge hd
  have hCe := mul_le_mul_of_nonneg_left hge (by linarith : (0 : ℝ) ≤ C)
  linarith

/-- Every `d ∈ 𝔇` is realizable (Gale–Ryser). -/
theorem Dset_realizable (φ : ℝ) (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) {ℓ n m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) : ∀ d ∈ Dset φ ℓ n m, 0 < N d := fun d hd =>
  (nbhd_of_sizes φ hφ₁ hφ₂ 0 0 hS (by simp; linarith [hS.B_ge])
    (by simp; linarith [hS.B_ge]) d hd).1.N_pos (r := rad (ℓ * n)) (Ball_self d) (bal_Dset hd)

end LW.Bip
