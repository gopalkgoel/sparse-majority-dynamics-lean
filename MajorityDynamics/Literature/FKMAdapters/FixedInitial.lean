import MajorityDynamics.Literature.FKMFormal.Final

/-! Fixed-initial-coloring consequence of the supplied FKM proof.
Uses its round-two estimate and deterministic cleanup directly. No conditioning
on a random initial majority, and no extra probabilistic hypothesis. -/
noncomputable section
open Finset Real
namespace MD

set_option maxHeartbeats 800000 in
theorem fixed_initial_dense (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      ∀ p : ℝ, lam / √n ≤ p → p ≤ 1 → ∀ s₀ : Fin n → Bool,
        c * √n ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) →
        Pr (q n p) (fun x => ¬ ∀ v, Sfix x s₀ 4 v = true) ≤ ε := by
  have hξ : 0 < ξ₀ := by unfold ξ₀ c4; positivity
  set L : ℝ := 1220 + 100 * (1 / 2 + 36 * exp 12) / (ξ₀ ^ 2 * c ^ 2 * ε) with hL
  have hL0 : 0 < L := by positivity
  set lam : ℝ := 10000 / c + √L with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamc : 10000 ≤ lam * c := by
    have : 10000 / c * c = 10000 := div_mul_cancel₀ _ hc0.ne'
    have : 0 ≤ √L * c := by positivity
    rw [hlam]; nlinarith
  have hlamL : L ≤ lam ^ 2 := by
    have h1 : √L ^ 2 = L := Real.sq_sqrt hL0.le
    have h2 : 0 ≤ 10000 / c := by positivity
    rw [hlam]; nlinarith [Real.sqrt_nonneg L]
  refine ⟨lam, hlam0, ?_⟩
  set n₀ : ℕ := 144 + ⌈(2 / c) ^ 2⌉₊ + ⌈(20 * exp 6 / ε) ^ 2⌉₊ + ⌈25 / ε⌉₊ +
    ⌈240 * 40 ^ 4 / (lam ^ 4 * ε)⌉₊ + ⌈(2400 / lam) ^ 2⌉₊ with hn₀
  refine ⟨n₀, fun n hn p hp hp1 s₀ hlead => ?_⟩
  -- basic facts about `n` and `p`
  have hn144 : 144 ≤ n := by omega
  have hnR : (144 : ℝ) ≤ n := by exact_mod_cast hn144
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hsn2 : √(n : ℝ) * √n = n := Real.mul_self_sqrt hn0.le
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hpn : lam ≤ p * √n := by
    have := (div_le_iff₀ hsn).1 hp; linarith
  have hnp2 : lam ^ 2 ≤ n * p ^ 2 := by
    calc lam ^ 2 ≤ (p * √n) ^ 2 := pow_le_pow_left₀ hlam0.le hpn 2
      _ = n * p ^ 2 := by rw [mul_pow, Real.sq_sqrt hn0.le]; ring
  have hnp : lam ^ 2 ≤ n * p := by
    calc lam ^ 2 ≤ n * p ^ 2 := hnp2
      _ ≤ n * p := by nlinarith
  have hL1220 : (1220 : ℝ) ≤ n * p ^ 2 := by
    have h1 : 0 ≤ 100 * (1 / 2 + 36 * exp 12) / (ξ₀ ^ 2 * c ^ 2 * ε) := by positivity
    have h2 : (1220 : ℝ) ≤ L := by rw [hL]; linarith
    linarith
  have hceil : ∀ a : ℝ, ⌈a⌉₊ ≤ n₀ → a ≤ n := by
    intro a ha
    have h1 : (⌈a⌉₊ : ℝ) ≤ n := by exact_mod_cast (ha.trans hn.le)
    exact (Nat.le_ceil a).trans h1
  have hF2 : (2 / c) ^ 2 ≤ n := hceil _ (by omega)
  have hF3 : (20 * exp 6 / ε) ^ 2 ≤ n := hceil _ (by omega)
  have hF4 : 25 / ε ≤ n := hceil _ (by omega)
  have hF5 : 240 * 40 ^ 4 / (lam ^ 4 * ε) ≤ n := hceil _ (by omega)
  have hF6 : (2400 / lam) ^ 2 ≤ n := hceil _ (by omega)
  have hsq : ∀ a : ℝ, 0 ≤ a → a ^ 2 ≤ n → a ≤ √n := fun a ha h =>
    Real.le_sqrt_of_sq_le h
  have hcn : 2 ≤ c * √n := by
    have := hsq _ (by positivity) hF2
    rwa [div_le_iff₀ hc0, mul_comm] at this
  have hcsn : 0 < c * √n := by positivity
  have hK : 10000 ≤ c * √n * p := by
    calc (10000 : ℝ) ≤ lam * c := hlamc
      _ ≤ p * √n * c := mul_le_mul_of_nonneg_right hpn hc0.le
      _ = c * √n * p := by ring
  -- the threshold `w`
  set w : ℕ := ⌈60 / p⌉₊ with hw
  have hw1 : 60 / p ≤ w := Nat.le_ceil _
  have hw2 : (w : ℝ) ≤ 60 / p + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hwp : 60 ≤ (w : ℝ) * p := by
    have := (div_le_iff₀ hp0).1 hw1; linarith
  have hinvp : 1 / p ≤ √n / lam := by
    rw [div_le_div_iff₀ hp0 hlam0]; linarith
  have hW1 : 20 * w ≤ n := by
    have h2400 : 2400 / lam ≤ √n := hsq _ (by positivity) hF6
    have h1 : 1200 / p ≤ n / 2 := by
      calc 1200 / p = 1200 * (1 / p) := by ring
        _ ≤ 1200 * (√n / lam) := by gcongr
        _ = √n * (1200 / lam) := by ring
        _ ≤ √n * (√n / 2) := by
            apply mul_le_mul_of_nonneg_left _ hsn.le
            rw [div_le_div_iff₀ hlam0 (by norm_num)]
            have := (div_le_iff₀ hlam0).1 h2400; linarith
        _ = n / 2 := by linear_combination hsn2 / 2
    have : (20 : ℝ) * w ≤ n := by
      calc (20 : ℝ) * w ≤ 20 * (60 / p + 1) := by gcongr
        _ = 1200 / p + 20 := by ring
        _ ≤ n / 2 + n / 2 := add_le_add h1 (by linarith)
        _ = n := by ring
    exact_mod_cast this
  have hW2 : 20 * (w : ℝ) ≤ n * p := by
    have h1 : 1200 / p ≤ n * p - 20 := by
      rw [div_le_iff₀ hp0]
      have : 20 * p ≤ 20 := by linarith
      linarith [show (n * p - 20) * p = n * p ^ 2 - 20 * p by ring]
    calc (20 : ℝ) * w ≤ 20 * (60 / p + 1) := by gcongr
      _ = 1200 / p + 20 := by ring
      _ ≤ n * p := by linarith
  have hW4 : 4 * (w : ℝ) ≤ (n - 1) * p := by
    have h1 : 240 / p ≤ (n - 1) * p - 4 := by
      rw [div_le_iff₀ hp0]
      have : p ^ 2 ≤ 1 := pow_le_one₀ hp0.le hp1
      have : 4 * p ≤ 4 := by linarith
      linarith [show ((n - 1) * p - 4) * p = n * p ^ 2 - p ^ 2 - 4 * p by ring]
    calc (4 : ℝ) * w ≤ 4 * (60 / p + 1) := by gcongr
      _ = 240 / p + 4 := by ring
      _ ≤ (n - 1) * p := by linarith
  -- the four probability bounds
  have hR2 : 10 * ((1 / (2 * n * p) + 36 * exp 12 / n) / (ξ₀ ^ 2 * (c * √p) ^ 2)) ≤ ε / 10 := by
    have hsp : √p ^ 2 = p := Real.sq_sqrt hp0.le
    have heq : 10 * ((1 / (2 * n * p) + 36 * exp 12 / n) / (ξ₀ ^ 2 * (c * √p) ^ 2)) =
        10 * (1 / (2 * (n * p ^ 2)) + 36 * exp 12 / (n * p)) / (ξ₀ ^ 2 * c ^ 2) := by
      rw [mul_pow, hsp]; field_simp
    have h1 : 1 / (2 * (n * p ^ 2)) ≤ 1 / (2 * lam ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : 36 * exp 12 / (n * p) ≤ 36 * exp 12 / lam ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hnp
    have h3 : 10 * (1 / (2 * lam ^ 2) + 36 * exp 12 / lam ^ 2) / (ξ₀ ^ 2 * c ^ 2) =
        10 * (1 / 2 + 36 * exp 12) / (ξ₀ ^ 2 * c ^ 2 * lam ^ 2) := by
      field_simp
    have h4 : 10 * (1 / 2 + 36 * exp 12) / (ξ₀ ^ 2 * c ^ 2 * lam ^ 2) ≤ ε / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 100 * (1 / 2 + 36 * exp 12) / (ξ₀ ^ 2 * c ^ 2 * ε) ≤ lam ^ 2 := by
        have : 0 ≤ (1220 : ℝ) := by norm_num
        linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    rw [heq]
    calc 10 * (1 / (2 * (n * p ^ 2)) + 36 * exp 12 / (n * p)) / (ξ₀ ^ 2 * c ^ 2)
        ≤ 10 * (1 / (2 * lam ^ 2) + 36 * exp 12 / lam ^ 2) / (ξ₀ ^ 2 * c ^ 2) := by gcongr
      _ ≤ ε / 10 := h3 ▸ h4
  have hP1 : Pr (q n p) (fun x => ¬ P1 n w x) ≤ ε / 10 := by
    refine (Pr_not_P1_le hp0.le hp1 hW1 hW2).trans ?_
    have h1 : exp (-(w * n * p / 30)) ≤ exp (-(2 * n)) := by
      apply exp_le_exp.2; apply neg_le_neg
      have : 60 * n ≤ (w : ℝ) * p * n := mul_le_mul_of_nonneg_right hwp hn0.le
      linarith
    have h2 : (4 : ℝ) ^ n * (2 * exp (-(w * n * p / 30))) ≤ 2 * (5 / (4 * n)) := by
      calc (4 : ℝ) ^ n * (2 * exp (-(w * n * p / 30))) ≤ (4 : ℝ) ^ n * (2 * exp (-(2 * n))) := by
            gcongr
        _ = 2 * ((4 : ℝ) ^ n * exp (-(2 * n))) := by ring
        _ ≤ 2 * (5 / (4 * n)) := by gcongr; exact four_pow_exp_le (by omega)
    have h3 : 2 * (5 / (4 * (n : ℝ))) ≤ ε / 10 := by
      rw [show 2 * (5 / (4 * (n : ℝ))) = 5 / (2 * n) by field_simp; ring,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      have := (div_le_iff₀ hε0).1 hF4; linarith
    linarith
  have hP2 : Pr (q n p) (fun x => ¬ P2 n w x) ≤ ε / 10 := by
    refine (Pr_not_P2_le hp0.le hp1 (by omega) hW4).trans ?_
    set y : ℝ := lam * √n / 40 with hy
    have hy0 : 0 < y := by positivity
    have hy1 : y ≤ (n - 1) * p / 20 := by
      have h1 : (n : ℝ) / 2 ≤ n - 1 := by linarith
      have h2 : lam * √n ≤ n * p := by
        calc lam * √n ≤ p * √n * √n := mul_le_mul_of_nonneg_right hpn hsn.le
          _ = n * p := by rw [mul_assoc, hsn2]; ring
      rw [hy]
      have : (n : ℝ) * p / 2 ≤ (n - 1) * p := by nlinarith
      linarith
    have h1 : exp (-((n - 1) * p / 20)) ≤ exp (-y) := exp_le_exp.2 (neg_le_neg hy1)
    have h2 : exp (-y) ≤ 24 / y ^ 4 := exp_neg_le_of_pos hy0
    have h3 : (n : ℝ) * (24 / y ^ 4) = 24 * 40 ^ 4 / (lam ^ 4 * n) := by
      rw [hy]; field_simp
      rw [show (√(n : ℝ)) ^ 4 = (√n * √n) ^ 2 by ring, hsn2]
    have h4 : 24 * 40 ^ 4 / (lam ^ 4 * (n : ℝ)) ≤ ε / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := (div_le_iff₀ (by positivity)).1 hF5; nlinarith
    calc (n : ℝ) * exp (-((n - 1) * p / 20)) ≤ n * (24 / y ^ 4) := by
          gcongr; exact h1.trans h2
      _ = 24 * 40 ^ 4 / (lam ^ 4 * n) := h3
      _ ≤ ε / 10 := h4
  have hγ0 : 0 < c * √p := by positivity
  have hγ1 : c * √p ≤ 1 :=
    mul_le_one₀ hc1 (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hp1)
  have hab : (sset s₀ false).card ≤ (sset s₀ true).card := by
    have hpos : (0 : ℝ) < c * √n := by positivity
    have hh : ((sset s₀ false).card : ℝ) ≤ (sset s₀ true).card := by linarith
    exact_mod_cast hh
  have hK' := hK.trans (mul_le_mul_of_nonneg_right hlead hp0.le)
  have hγ : c * √p * √(n * p) ≤
      (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p := by
    have hsp : √p * √p = p := Real.mul_self_sqrt hp0.le
    calc c * √p * √(n * p) = c * √n * p := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n)]
          linear_combination (c * √n) * hsp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlead hp0.le
  have hB2 := Pr_many_false_le hp0 hp1 s₀ hγ0 hγ1 (by omega) hab hK' hγ
  have hq := isProb_q (n := n) hp0.le hp1
  have hbad : Pr (q n p) (fun x => ¬ ∀ v, Sfix x s₀ 4 v = true) ≤
      Pr (q n p) (fun x => ¬ 10 * (sset (Sfix x s₀ 2) false).card ≤ n) +
        Pr (q n p) (fun x => ¬ P1 n w x) + Pr (q n p) (fun x => ¬ P2 n w x) := by
    refine le_trans (Pr_mono hq (B := fun x =>
      ((¬ 10 * (sset (Sfix x s₀ 2) false).card ≤ n) ∨ ¬ P1 n w x) ∨
        ¬ P2 n w x) fun x hx => ?_)
      ((Pr_or_le hq _ _).trans (add_le_add (Pr_or_le hq _ _) le_rfl))
    by_contra h
    rw [not_or, not_or, not_not, not_not, not_not] at h
    exact hx (final_rounds x (Sfix x s₀ 2) h.1.2 h.2 h.1.1)
  linarith

end MD
