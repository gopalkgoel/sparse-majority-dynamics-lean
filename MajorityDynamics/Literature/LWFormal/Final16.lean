import MajorityDynamics.Literature.LWFormal.Final

set_option autoImplicit true

/-!
# Theorem 1.6: conditional edge probability

A by-product of the proof of Theorem 1.4: the conditional edge probability is `P_{ab}(d)`,
`eq_7_4` gives `P = P^gr(1 + O(μ d̄^{4α-4}))` on `𝔇`, and `P^gr` reparameterises to the bracket of
`Theorem16`. Only the card-ratio link and the reparameterisation are new.
-/

namespace LW

open Finset Filter Real

variable {n : ℕ}

/-- The conditional edge probability is `N_{ab}(d)/N(d)`. -/
theorem probEdge_eq_P {m : ℕ} {d : Fin n → ℕ} (hs : ∑ i, d i = 2 * m) (hN : 0 < N (toZ d))
    (a b : Fin n) : probEdge n m d a b = P a b (toZ d) := by
  have key : (Gnm n m).filter (fun E => degSeq E = d ∧ s(a, b) ∈ E) =
      graphsWith (toZ d) {s(a, b)} := by
    ext E
    simp only [mem_filter, mem_graphsWith, HasDegSeq, degSeq, toZ, singleton_subset_iff, Gnm_eq,
      mem_univ, true_and, Nat.cast_inj]
    constructor
    · rintro ⟨⟨hsi, -⟩, hdeg, hab⟩; exact ⟨⟨hsi, fun v => congrFun hdeg v⟩, hab⟩
    · rintro ⟨⟨hsi, hdeg⟩, hab⟩
      have h : deg E = d := funext hdeg
      refine ⟨⟨hsi, ?_⟩, h, hab⟩
      have := sum_deg_eq hsi
      rw [h, hs] at this; omega
  have hG : (0 : ℝ) < (Gnm n m).card := by
    obtain ⟨G, hG⟩ := card_pos.1 hN
    have hG' : G ∈ (Gnm n m).filter (degSeq · = d) := by
      rw [Gnm_filter_degSeq n m d hs]; exact hG
    exact_mod_cast card_pos.2 ⟨G, filter_subset _ _ hG'⟩
  rw [probEdge, prob, key, probGnm_eq n m d hs, ← card_Gnm, div_div_div_cancel_right₀ hG.ne']
  rfl

/-- `P^gr` in the coordinates of Theorem 1.6: `μ(1+ε_a)(1+ε_b) = d_a d_b/(d(n-1))` and
`P^gr = edgeMain · edgeBracket`. -/
theorem Pgr_eq_bracket {m : ℕ} {d : Fin n → ℕ} (hs : ∑ i, d i = 2 * m) (hn : (n : ℝ) ≠ 0)
    (hn1 : (n : ℝ) - 1 ≠ 0) (hD : (2 * m / n : ℝ) ≠ 0) (hnD : (n : ℝ) - 1 - 2 * m / n ≠ 0)
    (a b : Fin n) :
    mu (toZ d) * (1 + eps (toZ d) a) * (1 + eps (toZ d) b) = edgeMain n m d a b ∧
      Pgr a b (toZ d) = edgeMain n m d a b * edgeBracket n m d a b := by
  have hs' : ∑ i, (d i : ℝ) = 2 * m := by exact_mod_cast hs
  have hM : (M1 (toZ d) : ℝ) = 2 * m := by
    simp only [M1, toZ]; push_cast; exact hs'
  have hdbar : dbar (toZ d) = 2 * m / n := by unfold dbar; rw [hM]
  have hμ : mu (toZ d) = 2 * m / n / (n - 1) := by unfold mu; rw [hdbar]
  have hσ : sigma2 (toZ d) = var d := by
    unfold sigma2 var avgDeg; rw [hdbar, hs']; simp [toZ]
  have hεa : eps (toZ d) a = ((d a : ℝ) - 2 * m / n) / (2 * m / n) := by
    unfold eps; rw [hdbar]; simp [toZ]
  have hεb : eps (toZ d) b = ((d b : ℝ) - 2 * m / n) / (2 * m / n) := by
    unfold eps; rw [hdbar]; simp [toZ]
  simp only [Pgr, piF, edgeMain, edgeBracket, edgeBracket0, hμ, hdbar, hσ, hεa, hεb]
  generalize (2 * (m : ℝ) / n) = D at hD hnD ⊢
  have h1 : 1 - D / (n - 1) ≠ 0 := by
    rw [show 1 - D / (n - 1) = (n - 1 - D) / (n - 1) by field_simp]
    exact div_ne_zero hnD hn1
  constructor <;> field_simp <;> ring

/-- `err71 = μ d̄^{4α-4} ≤ 2 · err16` when `d̄ = 2m/n`. -/
theorem err71_le_err16 {α : ℝ} {m : ℕ} {d : Seq n} (hdbar : dbar d = 2 * m / n)
    (hD : 0 < (2 * m / n : ℝ)) (hn : (2 : ℝ) ≤ n) : err71 α d ≤ 2 * err16 α n (2 * m / n) := by
  unfold err71 err16 mu
  rw [hdbar, show 4 * α - 3 = (4 * α - 4) + 1 by ring, rpow_add_one hD.ne']
  have hX : 0 ≤ (2 * m / n : ℝ) ^ (4 * α - 4) * (2 * m / n) := mul_nonneg (rpow_nonneg hD.le _) hD.le
  rw [show (2 * m / n : ℝ) / (n - 1) * (2 * m / n) ^ (4 * α - 4) =
    (2 * m / n : ℝ) ^ (4 * α - 4) * (2 * m / n) / (n - 1) by ring]
  calc (2 * m / n : ℝ) ^ (4 * α - 4) * (2 * m / n) / (n - 1)
      ≤ (2 * m / n : ℝ) ^ (4 * α - 4) * (2 * m / n) / (n / 2) :=
        div_le_div_of_nonneg_left hX (by linarith) (by linarith)
    _ = _ := by field_simp

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.6** (by-product form). -/
theorem theorem_1_6 : Theorem16 := by
  unfold Theorem16
  obtain ⟨μ₁, hμ₁, h74⟩ := eq_7_4
  refine ⟨min μ₁ (1 / (4 * 10 ^ 9)), by positivity, fun α hα₁ hα₂ ω hω => ?_⟩
  obtain ⟨C₁, N₁, h₁⟩ := h74 α hα₁ hα₂ ω hω
  obtain ⟨N₂, h₂⟩ := eventually_nbhd α hα₁ hα₂ hω 0 0
  refine ⟨3 * |C₁|, max N₁ N₂, fun n hn m hR1 hR2 d hd a b hab => ?_⟩
  have hR : Range ω _ n m := ⟨hR1, hR2⟩
  obtain ⟨hsum, hdev⟩ := hd
  set u := toZ d with hu
  have hdD : u ∈ Dset α n m :=
    ⟨fun i => Int.natCast_nonneg _, by simp only [hu, M1, toZ]; exact_mod_cast hsum,
      fun i => by simpa [hu, toZ] using hdev i⟩
  obtain ⟨hnb, -, -⟩ := h₂ n (le_of_max_le_right hn) m (hR.mono (min_le_right _ _)) u hdD
  have h74' := h₁ n (le_of_max_le_left hn) m (hR.mono (min_le_left _ _)) u hdD a b hab
  have hev : IsEven u := ⟨m, by rw [hdD.2.1]; ring⟩
  have hN : 0 < N u := hnb.N_pos (r := rad n) (Ball_self u) hev
  have hμ8 : 2 * mu u ≤ 1 / 8 := by linarith [hnb.mu_le]
  obtain ⟨hE1, hE2⟩ := abs_le.1 (hnb.grOK.abs_piCorr_le hμ8 (Ball_self u) a b)
  -- basic bounds
  set D : ℝ := 2 * m / n with hD
  have hn48 : (48 : ℝ) ≤ n := hnb.n_ge
  have hdbar : dbar u = D := by simp [dbar, hdD.2.1, hD]
  have hD0 : 0 < D := by rw [← hdbar]; exact hnb.D_pos
  have hDn : D ≤ n / 10 ^ 9 := by rw [← hdbar]; exact hnb.mu_bound
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnD : (n : ℝ) - 1 - D ≠ 0 := by linarith
  -- reparameterisation
  obtain ⟨hq, hPb⟩ := Pgr_eq_bracket hsum hn0 hn1 hD0.ne' hnD a b
  set q := edgeMain n m d a b with hq'
  set X := edgeBracket n m d a b with hX
  have hPpos : 0 < Pgr a b u := by
    linarith [(hnb.grOK.Pgr_bounds hμ8 (Ball_self u) a b).1, hnb.mu_pos]
  have hq0 : q ≠ 0 := fun h => by rw [hPb, h, zero_mul] at hPpos; exact lt_irrefl _ hPpos
  have hXE : X = 1 + piCorr (eps u a) (eps u b) (mu u) (sigma2 u) (dbar u) n := by
    apply mul_left_cancel₀ hq0
    rw [← hPb, ← hq]; exact piF_eq_corr _ _ _ _ _ _
  have hXb : |X| ≤ 101 / 100 := by rw [hXE, abs_le]; constructor <;> linarith
  -- error conversion
  unfold Close at h74'
  have herr : 0 ≤ err16 α n D := div_nonneg (rpow_nonneg hD0.le _) (by positivity)
  have h71 : err71 α u ≤ 2 * err16 α n D := err71_le_err16 hdbar hD0 (by linarith)
  have herr71 : 0 ≤ err71 α u := mul_nonneg hnb.mu_pos.le (rpow_nonneg hnb.D_pos.le _)
  refine ⟨(P a b u - Pgr a b u) / q, ?_, ?_⟩
  · rw [abs_div, div_le_iff₀ (abs_pos.2 hq0)]
    calc |P a b u - Pgr a b u| ≤ C₁ * err71 α u * |Pgr a b u| := h74'
      _ = C₁ * err71 α u * |X| * |q| := by rw [hPb, abs_mul]; ring
      _ ≤ |C₁| * (2 * err16 α n D) * (101 / 100) * |q| := by
        gcongr
        · exact le_abs_self C₁
      _ ≤ 3 * |C₁| * err16 α n D * |q| := by
        have := abs_nonneg C₁; have := abs_nonneg q
        nlinarith [mul_nonneg (mul_nonneg this ‹0 ≤ |C₁|›) herr]
  · rw [probEdge_eq_P hsum hN a b, mul_add, ← hPb, mul_div_cancel₀ _ hq0]; ring

#print axioms theorem_1_6

set_option maxHeartbeats 2000000 in
/-- **Theorem 1.6** as printed, on `𝔇` of Theorem 6.3: from `theorem_1_6` with `α = 11/20`. -/
theorem theorem_1_6' : Theorem16' := by
  unfold Theorem16'
  obtain ⟨μ₁, hμ₁, h16⟩ := theorem_1_6
  refine ⟨min μ₁ (1 / (4 * 10 ^ 9)), by positivity, fun C₀ ω hω => ?_⟩
  obtain ⟨C₁, N₁, h₁⟩ := h16 (11 / 20) (by norm_num) (by norm_num) ω hω
  obtain ⟨N₂, h₂⟩ := eventually_nbhd (11 / 20) (by norm_num) (by norm_num) hω 0 0
  obtain ⟨N₃, h₃⟩ := eventually_atTop.1 (hω.eventually_ge_atTop 20)
  refine ⟨96 * |C₀| + 8 * |C₁|, max (max N₁ N₂) (max N₃ ⌈exp (max (C₀ ^ 2) 1)⌉₊),
    fun n hn m hR1 hR2 d hd a b hab => ?_⟩
  have hR : Range ω _ n m := ⟨hR1, hR2⟩
  obtain ⟨hsum, hdev, hvar⟩ := hd
  set D : ℝ := 2 * m / n with hD
  -- `n` is large
  have hN₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hN₂ : N₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hN₃ : N₃ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hN₄ : ⌈exp (max (C₀ ^ 2) 1)⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hω20 : (20 : ℝ) ≤ ω n := h₃ n hN₃
  have hlog : max (C₀ ^ 2) 1 ≤ log n := by
    have hn0 : (0 : ℝ) < n := by
      have : 0 < ⌈exp (max (C₀ ^ 2) 1)⌉₊ := Nat.ceil_pos.2 (exp_pos _)
      exact_mod_cast lt_of_lt_of_le this hN₄
    rw [le_log_iff_exp_le hn0]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN₄)
  have hlog1 : 1 ≤ log n := (le_max_right _ _).trans hlog
  have hlogC : C₀ ^ 2 ≤ log n := (le_max_left _ _).trans hlog
  -- `𝔇` of Theorem 6.3 is inside `𝔇` of Theorem 1.4 with `α = 11/20`
  have hD20 : log n ^ (20 : ℝ) ≤ D := (rpow_le_rpow_of_exponent_le hlog1 hω20).trans hR1
  have hD1 : 1 ≤ D := (one_le_rpow hlog1 (by norm_num)).trans hD20
  have hD0 : 0 < D := by linarith
  have hlogD : log n ≤ D ^ (1 / 20 : ℝ) := by
    calc log n = (log n ^ (20 : ℝ)) ^ (1 / 20 : ℝ) := by
          rw [← rpow_mul (by linarith), show (20 : ℝ) * (1 / 20) = 1 by norm_num, rpow_one]
      _ ≤ D ^ (1 / 20 : ℝ) := rpow_le_rpow (by positivity) hD20 (by norm_num)
  set S := √(D * log n) with hS
  have hS0 : 0 ≤ S := sqrt_nonneg _
  have hSmul : S = D ^ (1 / 2 : ℝ) * √(log n) := by rw [hS, sqrt_mul hD0.le, sqrt_eq_rpow]
  have hC₀ : |C₀| ≤ √(log n) := abs_le_sqrt hlogC
  have hdev' : ∀ i, |(d i : ℝ) - D| ≤ |C₀| * S := fun i =>
    (hdev i).trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) hS0)
  have hspread : ∀ i, |(d i : ℝ) - D| ≤ D ^ (11 / 20 : ℝ) := fun i => by
    refine (hdev' i).trans ?_
    calc |C₀| * S = D ^ (1 / 2 : ℝ) * (|C₀| * √(log n)) := by rw [hSmul]; ring
      _ ≤ D ^ (1 / 2 : ℝ) * (√(log n) * √(log n)) := by gcongr
      _ = D ^ (1 / 2 : ℝ) * log n := by rw [mul_self_sqrt (by linarith)]
      _ ≤ D ^ (1 / 2 : ℝ) * D ^ (1 / 20 : ℝ) := by gcongr
      _ = D ^ (11 / 20 : ℝ) := by rw [← rpow_add hD0]; norm_num
  have hInD : InD (11 / 20) n m d := ⟨hsum, hspread⟩
  obtain ⟨θ, hθ, hP⟩ := h₁ n hN₁ m hR1 (hR2.trans (by gcongr; exact min_le_left _ _)) d hInD a b hab
  set u := toZ d with hu
  have hdD : u ∈ Dset (11 / 20) n m :=
    ⟨fun i => Int.natCast_nonneg _, by simp only [hu, M1, toZ]; exact_mod_cast hsum,
      fun i => by simpa [hu, toZ] using hspread i⟩
  obtain ⟨hnb, -, -⟩ := h₂ n hN₂ m (hR.mono (min_le_right _ _)) u hdD
  have hn48 : (48 : ℝ) ≤ n := hnb.n_ge
  have hdbar : dbar u = D := by simp [dbar, hdD.2.1, hD]
  have hDn : D ≤ n / 10 ^ 9 := by rw [← hdbar]; exact hnb.mu_bound
  -- sizes
  have hn0 : (0 : ℝ) < n := by linarith
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  have hD0' : D ≠ 0 := hD0.ne'
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  set A : ℝ := n - 1 - D with hA
  have hA0 : 0 < A := by rw [hA]; linarith
  have hA2 : (n : ℝ) - 1 ≤ 2 * A := by rw [hA]; linarith
  have hD11 : D ^ (11 / 20 : ℝ) ≤ D := by
    calc D ^ (11 / 20 : ℝ) ≤ D ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hD1 (by norm_num)
      _ = D := rpow_one D
  have hda : (d a : ℝ) ≤ 2 * D := by linarith [(abs_le.1 (hspread a)).2]
  have hdb : (d b : ℝ) ≤ 2 * D := by linarith [(abs_le.1 (hspread b)).2]
  have hda0 : (0 : ℝ) ≤ d a := Nat.cast_nonneg _
  have hdb0 : (0 : ℝ) ≤ d b := Nat.cast_nonneg _
  have hvar0 : 0 ≤ var d := by unfold var; positivity
  have hvar' : var d ≤ 2 * D := hvar
  set q := edgeMain n m d a b with hq
  have hq0 : 0 ≤ q := by
    rw [hq, edgeMain, ← hD]; exact div_nonneg (by positivity) (mul_nonneg hD0.le hn1.le)
  have hqle : q ≤ 8 * D / n := by
    rw [hq, edgeMain, ← hD, div_le_div_iff₀ (mul_pos hD0 hn1) hn0]
    have h1 : (d a : ℝ) * d b ≤ 2 * D * (2 * D) := mul_le_mul hda hdb hdb0 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right h1 hn0.le,
      mul_nonneg (mul_nonneg hD0.le hD0.le) (by linarith : (0 : ℝ) ≤ n - 2)]
  -- the two omitted bracket terms and the error, all `O(S/(Dn))`
  set Δ : ℝ := (d a : ℝ) + d b - 2 * D with hΔ
  have hΔle : |Δ| ≤ 2 * |C₀| * S := by
    rw [hΔ, show (d a : ℝ) + d b - 2 * D = ((d a : ℝ) - D) + ((d b : ℝ) - D) by ring]
    linarith [abs_add_le ((d a : ℝ) - D) ((d b : ℝ) - D), hdev' a, hdev' b]
  set B : ℝ := S / (D * n) with hB
  have hB0 : 0 ≤ B := by positivity
  set T1 : ℝ := Δ * (n - 1) * var d / (D ^ 2 * n * A) with hT1
  set T2 : ℝ := Δ / (D * (n - 1)) with hT2
  have hT1le : |T1| ≤ 8 * |C₀| * B := by
    have hden : 0 < D ^ 2 * n * A := by positivity
    rw [hT1, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_mul, abs_mul, abs_of_nonneg hvar0,
      abs_of_nonneg hn1.le]
    calc |Δ| * (n - 1) * var d ≤ 2 * |C₀| * S * (n - 1) * (2 * D) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hΔle hn1.le) hvar' hvar0 (by positivity)
      _ = 4 * |C₀| * S * D * (n - 1) := by ring
      _ ≤ 4 * |C₀| * S * D * (2 * A) := mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ = 8 * |C₀| * B * (D ^ 2 * n * A) := by rw [hB]; field_simp; ring
  have hT2le : |T2| ≤ 4 * |C₀| * B := by
    have hden : 0 < D * (n - 1) := mul_pos hD0 hn1
    rw [hT2, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h1 : (1 / 2 : ℝ) ≤ (n - 1) / n := by rw [le_div_iff₀ hn0]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * |C₀| * S)
    calc |Δ| ≤ 2 * |C₀| * S := hΔle
      _ ≤ 4 * |C₀| * S * ((n - 1) / n) := by linarith
      _ = 4 * |C₀| * B * (D * (n - 1)) := by rw [hB]; field_simp
  have hθ' : |θ| ≤ |C₁| * B := by
    refine hθ.trans ?_
    have h1 : err16 (11 / 20) n D = D ^ (1 / 5 : ℝ) / (D * n) := by
      unfold err16
      rw [show (4 * (11 / 20 : ℝ) - 3) = 1 / 5 - 1 by norm_num, rpow_sub hD0, rpow_one, div_div]
    have h2 : D ^ (1 / 5 : ℝ) ≤ S := by
      rw [hSmul]
      calc D ^ (1 / 5 : ℝ) ≤ D ^ (1 / 2 : ℝ) := rpow_le_rpow_of_exponent_le hD1 (by norm_num)
        _ ≤ D ^ (1 / 2 : ℝ) * √(log n) :=
          le_mul_of_one_le_right (by positivity) (one_le_sqrt.2 hlog1)
    calc C₁ * err16 (11 / 20) n D ≤ |C₁| * err16 (11 / 20) n D :=
          mul_le_mul_of_nonneg_right (le_abs_self C₁) (by rw [h1]; positivity)
      _ ≤ |C₁| * B := by rw [h1, hB]; gcongr
  -- assembly
  have hX : edgeBracket n m d a b = edgeBracket0 n m d a b + T1 + T2 := rfl
  have hqB : q * B ≤ 8 * S / n ^ 2 := by
    calc q * B ≤ 8 * D / n * B := mul_le_mul_of_nonneg_right hqle hB0
      _ = 8 * S / n ^ 2 := by rw [hB]; field_simp
  have herr : S / n ^ 2 ≤ err16' n D := by
    unfold err16'; have : 0 ≤ S ^ 3 / n ^ 3 := by positivity
    linarith
  have h3 : |T1 + T2 + θ| ≤ (12 * |C₀| + |C₁|) * B := by
    linarith [abs_add_three T1 T2 θ]
  refine ⟨q * (T1 + T2 + θ), ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg hq0]
    calc q * |T1 + T2 + θ| ≤ q * ((12 * |C₀| + |C₁|) * B) := mul_le_mul_of_nonneg_left h3 hq0
      _ = (12 * |C₀| + |C₁|) * (q * B) := by ring
      _ ≤ (12 * |C₀| + |C₁|) * (8 * S / n ^ 2) := mul_le_mul_of_nonneg_left hqB (by positivity)
      _ = (96 * |C₀| + 8 * |C₁|) * (S / n ^ 2) := by ring
      _ ≤ (96 * |C₀| + 8 * |C₁|) * err16' n D := mul_le_mul_of_nonneg_left herr (by positivity)
  · rw [hP, hX]; ring

#print axioms theorem_1_6'

end LW
