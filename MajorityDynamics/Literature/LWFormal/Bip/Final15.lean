import MajorityDynamics.Literature.LWFormal.Bip.Final

set_option autoImplicit true

/-!
# Theorem 1.5 (bipartite case): conditional edge probability

A by-product of the proof of Theorem 1.1: the conditional edge probability is `P_{av}(d)`,
`eq_29` gives `P = P*(1 + O(μ ε⁴))` on `𝔇`, and `P*` reparameterises to the bracket of
Theorem 1.5. Only the card-ratio link and the reparameterisation are new.
-/

namespace LW.Bip

open Finset Filter Real

variable {ℓ n : ℕ}

/-- The conditional edge probability is `N_{av}(d)/N(d)`. -/
theorem probEdge_eq_P {m : ℕ} {s : Fin ℓ → ℕ} {t : Fin n → ℕ} (hs : ∑ a, s a = m)
    (hN : 0 < N (toSeq s t)) (a : Fin ℓ) (v : Fin n) :
    probEdge ℓ n m s t a v = P a v (toSeq s t) := by
  have key : (Gm ℓ n m).filter (fun E => ldeg E = s ∧ rdeg E = t ∧ (a, v) ∈ E) =
      graphsWith (toSeq s t) {(a, v)} := by
    ext E
    simp only [mem_filter, mem_Gm, mem_graphsWith, HasDeg, toSeq, Nat.cast_inj,
      singleton_subset_iff]
    constructor
    · rintro ⟨-, h1, h2, h3⟩; exact ⟨⟨fun a => congrFun h1 a, fun v => congrFun h2 v⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h1' : ldeg E = s := funext h1
      exact ⟨by rw [← sum_ldeg, h1', hs], h1', funext h2, h3⟩
  have hG : (0 : ℝ) < (Gm ℓ n m).card := by
    obtain ⟨G, hG⟩ := card_pos.1 hN
    have h1 : ldeg G = s := funext fun a => by
      have := (mem_graphs.1 hG).1 a
      simpa [toSeq] using this
    have : G ∈ Gm ℓ n m := mem_Gm.2 (by rw [← sum_ldeg, h1, hs])
    exact_mod_cast card_pos.2 ⟨G, this⟩
  rw [probEdge, probG_eq_N hs, prob, key, P, Nav, NE, div_div_div_cancel_right₀ hG.ne']

/-- `P*` in the coordinates of Theorem 1.5: `μ(1+ε_a)(1+ε_v) = s_a t_v / m` and
`P* = (s_a t_v / m) · bracket`. -/
theorem Pst_eq_bracket {m : ℕ} {s : Fin ℓ → ℕ} {t : Fin n → ℕ} (hs : ∑ a, s a = m)
    (ht : ∑ v, t v = m) (hℓ : (ℓ : ℝ) ≠ 0) (hn : (n : ℝ) ≠ 0) (hm : (m : ℝ) ≠ 0)
    (hmℓn : (ℓ : ℝ) * n - m ≠ 0) (a : Fin ℓ) (v : Fin n) :
    mu (toSeq s t) * (1 + eps (toSeq s t).1 a) * (1 + eps (toSeq s t).2 v) =
        (s a : ℝ) * t v / m ∧
      Pst a v (toSeq s t) = (s a : ℝ) * t v / m * edgeBracket ℓ n m s t a v := by
  set d := toSeq s t with hd
  have h1 : (M1 d.1 : ℝ) = m := by
    rw [M1_cast]; simp only [hd, toSeq, Int.cast_natCast]; exact_mod_cast hs
  have h2 : (M1 d.2 : ℝ) = m := by
    rw [M1_cast]; simp only [hd, toSeq, Int.cast_natCast]; exact_mod_cast ht
  have hμ : mu d = m / (ℓ * n) := by unfold mu; rw [h1, h2]; field_simp; ring
  have hds : dbar d.1 = m / ℓ := by unfold dbar; rw [h1]
  have hdt : dbar d.2 = m / n := by unfold dbar; rw [h2]
  have hσs : sigma2 d.1 = var s := by
    have := var_toN (d := d.1) fun a => Int.natCast_nonneg _
    rw [hd, toN_toSeq_fst] at this; exact this.symm
  have hσt : sigma2 d.2 = var t := by
    have := var_toN (d := d.2) fun v => Int.natCast_nonneg _
    rw [hd, toN_toSeq_snd] at this; exact this.symm
  have hεa : eps d.1 a = ((s a : ℝ) - m / ℓ) / (m / ℓ) := by
    unfold eps; rw [hds]; simp [hd, toSeq]
  have hεv : eps d.2 v = ((t v : ℝ) - m / n) / (m / n) := by
    unfold eps; rw [hdt]; simp [hd, toSeq]
  have h2' : (m : ℝ) - m / n * (m / ℓ) ≠ 0 := by
    rw [show (m : ℝ) - m / n * (m / ℓ) = m * (ℓ * n - m) / (ℓ * n) by field_simp]
    exact div_ne_zero (mul_ne_zero hm hmℓn) (mul_ne_zero hℓ hn)
  have h3 : (ℓ : ℝ) - m / n ≠ 0 := by
    rw [show (ℓ : ℝ) - m / n = (ℓ * n - m) / n by field_simp]
    exact div_ne_zero hmℓn hn
  have h4 : (n : ℝ) - m / ℓ ≠ 0 := by
    rw [show (n : ℝ) - m / ℓ = (ℓ * n - m) / ℓ by field_simp]
    exact div_ne_zero hmℓn hℓ
  have h5 : 1 - (m : ℝ) / (ℓ * n) ≠ 0 := by
    rw [show 1 - (m : ℝ) / (ℓ * n) = (ℓ * n - m) / (ℓ * n) by field_simp]
    exact div_ne_zero hmℓn (mul_ne_zero hℓ hn)
  simp only [Pst, piB, AcorrB, sS, sT, edgeBracket, hμ, hds, hdt, hσs, hσt, hεa, hεv]
  constructor <;> field_simp <;> ring

/-- On `𝔇`, `err41 φ d` is exactly `err15 φ ℓ n m`. -/
theorem err41_eq_err15 {φ : ℝ} {m : ℕ} {d : BSeq ℓ n} (hd : d ∈ Dset φ ℓ n m)
    (hℓ : (ℓ : ℝ) ≠ 0) (hn : (n : ℝ) ≠ 0) : err41 φ d = err15 φ ℓ n m := by
  unfold err41 err15 dmin dbar
  rw [mu_Dset hd hℓ hn, hd.2.2.1, hd.2.2.2.1]
  push_cast
  rw [mul_comm (n : ℝ) ℓ]; ring

set_option maxHeartbeats 1000000 in
theorem theorem_1_5 : Theorem15 := by
  unfold Theorem15
  refine ⟨1 / (2 * 10 ^ 9), by norm_num, fun φ hφ₁ hφ₂ ω hω => ?_⟩
  obtain ⟨C₁, B₀, h29⟩ := eq_29 φ hφ₁ hφ₂
  obtain ⟨N₁, hN₁⟩ := sizes_of_range φ hφ₁ hφ₂ hω (K := 4) (B := max 35000 B₀) le_rfl
    (le_max_left _ _)
  refine ⟨2 * |C₁|, N₁, fun n hn ℓ m hR1 hR2 hR3 s t hd a v => ?_⟩
  have hS := hN₁ n hn ℓ m ⟨hR1, hR2, hR3⟩
  have hB : B₀ ≤ max 35000 B₀ := le_max_right _ _
  obtain ⟨hℓ, hn', hm, hmℓn, -, -, -, -, -, -⟩ := hS.bounds
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hℓnm : (ℓ : ℝ) * n - m ≠ 0 := by nlinarith
  set d := toSeq s t with hd'
  have hdD : d ∈ Dset φ ℓ n m := toSeq_mem_Dset hd
  have hnb := (nbhd_of_sizes φ hφ₁ hφ₂ 0 0 hS (by simp) (by simp) d hdD).1
  have hN : 0 < N d := hnb.N_pos (r := rad (ℓ * n)) (Ball_self d) (bal_Dset hdD)
  have hst : StOK φ (2 * mu d) (Ball d (rad (ℓ * n))) := hnb.stOK
  have hμ8 : 2 * mu d ≤ 1 / 8 := by
    rw [mu_Dset hdD hℓ0 hn0]; linarith [hS.mu_le]
  obtain ⟨hA1, hA2⟩ := abs_le.1 (hst.abs_AcorrB_le hμ8 (Ball_self d) a v)
  obtain ⟨hP1, -⟩ := hst.Pst_bounds hμ8 (Ball_self d) a v
  obtain ⟨hs0, ht0, hμ0, -, -, -, -, -⟩ := hst.basic (Ball_self d)
  obtain ⟨hq, hPb⟩ := Pst_eq_bracket hd.1 hd.2.1 hℓ0 hn0 hm0 hℓnm a v
  set q := (s a : ℝ) * t v / m with hq'
  set X := edgeBracket ℓ n m s t a v with hX
  have hPpos : 0 < Pst a v d := by linarith
  have hq0 : q ≠ 0 := fun h => by rw [hPb, h, zero_mul] at hPpos; exact lt_irrefl _ hPpos
  have hXA : X = 1 + AcorrB (mu d) (sS d) (sT d) (eps d.1 a) (eps d.2 v) := by
    apply mul_left_cancel₀ hq0
    rw [← hPb, ← hq]; rfl
  have hXb : |X| ≤ 101 / 100 := by rw [hXA, abs_le]; constructor <;> linarith
  have h29' := h29 hS hB d hdD a v
  unfold Close at h29'
  have herr : 0 ≤ err41 φ d := mul_nonneg hμ0.le (rpow_nonneg (le_min hs0.le ht0.le) _)
  refine ⟨(P a v d - Pst a v d) / q, ?_, ?_⟩
  · rw [abs_div, div_le_iff₀ (abs_pos.2 hq0), ← err41_eq_err15 hdD hℓ0 hn0]
    calc |P a v d - Pst a v d| ≤ C₁ * err41 φ d * |Pst a v d| := h29'
      _ = C₁ * err41 φ d * |X| * |q| := by rw [hPb, abs_mul]; ring
      _ ≤ |C₁| * err41 φ d * (101 / 100) * |q| := by
        gcongr
        · exact le_abs_self C₁
      _ ≤ 2 * |C₁| * err41 φ d * |q| := by
        have := abs_nonneg C₁; have := abs_nonneg q
        nlinarith [mul_nonneg (mul_nonneg this ‹0 ≤ |C₁|›) herr]
  · rw [probEdge_eq_P hd.1 hN a v, mul_add, ← hPb, mul_div_cancel₀ _ hq0]; ring

#print axioms theorem_1_5

end LW.Bip
