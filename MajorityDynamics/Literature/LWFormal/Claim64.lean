import MajorityDynamics.Literature.LWFormal.FixedPoint

set_option autoImplicit true

/-!
# Claim 6.4: contraction of `𝒞` around `(P^gr, Y^gr)`

On a set `Ω₀` where the exact `(P, Y)` is a fixed point of `𝒞` and Lemma 7.1 holds with error
`ε`, repeated application of Lemma 5.3 gives `P = P^gr(1 + O(ε))` on `Ω⁽⁴ᵏ⁺²⁾` after `k` steps.
-/

namespace LW

open Finset

variable {n : ℕ}

/-- Hypotheses of Claim 6.4 on `Ω₀`. -/
structure OK (α μ ε : ℝ) (Ω₀ : Set (Seq n)) : Prop where
  ex : ExactOK μ Ω₀
  gr : GrOK α μ Ω₀
  μ_pos : 0 < μ
  μ_le : μ ≤ 1 / 10 ^ 9
  ε_pos : 0 < ε
  ε_le : ε ≤ 1 / 1000
  a : ∀ d ∈ Ω₀, ∀ a b, Close (opR Pgr Ygr a b d) (Rgr a b d) ε
  b : ∀ d ∈ Ω₀, ∀ a v, a ≠ v → Close (opP Pgr Rgr a v d) (Pgr a v d) ε
  c : ∀ d ∈ Ω₀, ∀ a v b, a ≠ v → a ≠ b → v ≠ b → Close (opY Pgr Ygr a v b d) (Ygr a v b d) ε

theorem step_bound {μ ξ ε c : ℝ} (hμ1 : μ ≤ 1 / 10 ^ 9) (hξ : 0 < ξ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 1000) (hc : 0 ≤ c) (hc1 : c ≤ 442) :
    8000 * (64 * μ) * ξ * (1 + c * ε) + c * ε ≤ ξ / 2 + 442 * ε := by
  have h1 : 8000 * (64 * μ) * ξ ≤ 512000 / 10 ^ 9 * ξ := by
    nlinarith [mul_le_mul_of_nonneg_right hμ1 hξ.le]
  have h2 : c * ε ≤ 442 / 1000 := by nlinarith
  have h3 : 0 ≤ c * ε := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ 1 + c * ε),
    mul_le_mul_of_nonneg_left h2 hξ.le, mul_le_mul_of_nonneg_right hc1 hε]

namespace OK

variable {α μ ε : ℝ} {Ω₀ : Set (Seq n)} (h : OK α μ ε Ω₀)
include h

theorem μ8 : μ ≤ 1 / 8 := h.μ_le.trans (by norm_num)

/-- `p̂ = 𝒫(P^gr, ℛ(P^gr, Y^gr)) = P^gr(1 ± 22ε)` on even sequences of `Ω⁽²⁾`. -/
theorem Phat_close {d : Seq n} (hd : d ∈ Omega Ω₀ 2) (hev : IsEven d) {a v : Fin n}
    (hav : a ≠ v) : Close (opP Pgr (opR Pgr Ygr) a v d) (Pgr a v d) (22 * ε) := by
  have hμ0 := h.μ_pos
  have hε0 := h.ε_pos
  have hε1 := h.ε_le
  have hμ1 := h.μ_le
  have hμ₀ : (0 : ℝ) < 64 * μ := by positivity
  have hcancel : 64 * μ * (ε / (64 * μ)) = ε := mul_div_cancel₀ _ hμ₀.ne'
  have h52 := (lemma_5_2_explicit d (h.ex.two_le d hd.1) (ξ := ε / (64 * μ)) (by positivity) hμ₀
    (by linarith) (by rw [hcancel]; linarith) Pgr Pgr Ygr Ygr (opR Pgr Ygr) Rgr).2.1 hev
    ((h.gr.inPi h.μ8 le_rfl).mono fun d' hd' => (Q0_subset_Omega (s := 0) hd hd').1) a v hav
    (fun d' hd' c => h.gr.Rgr_nonneg h.μ8 (Q1_subset_Omega (s := 1) hd hd').1 c a)
    (fun _ _ _ _ => Close.refl _ (by positivity))
    (fun d' hd' c _ => (h.a d' (Q1_subset_Omega (s := 1) hd hd').1 c a).mono hcancel.symm.le)
  have h20 : 20 * (64 * μ) * (ε / (64 * μ)) = 20 * ε := by rw [mul_assoc, hcancel]
  refine (h52.trans' (h.b d hd.1 a v hav) (by positivity)).mono ?_
  rw [h20]; nlinarith

/-- `𝒴(p̂, Y^gr) = Y^gr(1 ± 442ε)` on even sequences of `Ω⁽⁴⁾`. -/
theorem Yhat_close {d : Seq n} (hd : d ∈ Omega Ω₀ 4) (hev : IsEven d) {a v b : Fin n}
    (hav : a ≠ v) (hab : a ≠ b) (hvb : v ≠ b) :
    Close (opY (opP Pgr (opR Pgr Ygr)) Ygr a v b d) (Ygr a v b d) (442 * ε) := by
  have hμ0 := h.μ_pos
  have hε0 := h.ε_pos
  have hε1 := h.ε_le
  have hμ1 := h.μ_le
  have hμ₀ : (0 : ℝ) < 64 * μ := by positivity
  have hcancel : 64 * μ * (22 * ε / (64 * μ)) = 22 * ε := mul_div_cancel₀ _ hμ₀.ne'
  have h52 := (lemma_5_2_explicit d (h.ex.two_le d hd.1) (ξ := 22 * ε / (64 * μ)) (by positivity)
    hμ₀ (by linarith) (by rw [hcancel]; linarith) (opP Pgr (opR Pgr Ygr)) Pgr Ygr Ygr
    (opR Pgr Ygr) Rgr).2.2 hev
    ((h.gr.inPi h.μ8 le_rfl).mono fun d' hd' => (Q0_subset_Omega (s := 2) hd hd').1) a v b hav hab
    hvb (fun d' hd' c hcv => (h.Phat_close (Q0_subset_Omega (s := 2) hd hd') hd'.1 hcv).mono
      hcancel.symm.le)
    (fun _ _ _ _ _ _ _ _ => Close.refl _ (by positivity))
  have h440 : 20 * (64 * μ) * (22 * ε / (64 * μ)) = 440 * ε := by rw [mul_assoc, hcancel]; ring
  refine (h52.trans' (h.c d hd.1 a v b hav hab hvb) (by positivity)).mono ?_
  rw [h440]; nlinarith

/-- One contraction step: `χ⁽ˢ⁾ ≤ ξ ⇒ χ⁽ˢ⁺⁴⁾ ≤ ξ/2 + 442ε` (`s ≥ 2`). -/
theorem step {s : ℕ} (hs : 2 ≤ s) {ξ : ℝ} (hξ : 0 < ξ) (hμξ : 64 * μ * ξ ≤ 1 / 8000)
    (hχ : ChiLe Ω₀ s P Pgr Y Ygr ξ) : ChiLe Ω₀ (s + 4) P Pgr Y Ygr (ξ / 2 + 442 * ε) := by
  have hμ0 := h.μ_pos
  have hε0 := h.ε_pos
  have hε1 := h.ε_le
  have hμ1 := h.μ_le
  have h53 := lemma_5_3_explicit Ω₀ h.ex.two_le hξ (μ₀ := 64 * μ) (by positivity) (by linarith)
    hμξ s P Pgr Y Ygr ((h.gr.inPi h.μ8 le_rfl).mono (Omega_subset _ _))
    (h.gr.inPi_of_close h.μ8 le_rfl (Omega_subset _ _) (opP Pgr (opR Pgr Ygr))
      fun d hd hev a v hav =>
        (h.Phat_close (Omega_mono (by omega) hd) hev hav).mono (by linarith)) hχ
  have hfix : ∀ d ∈ Omega Ω₀ (s + 4), IsEven d →
      (∀ a v, a ≠ v → (opC P Y).1 a v d = P a v d) ∧
      (∀ a v b, a ≠ v → a ≠ b → v ≠ b → (opC P Y).2 a v b d = Y a v b d) :=
    fun d hd hev => h.ex.opC_fixed h.μ8 (Omega_mono (by omega) hd) hev
  have hA : 0 ≤ 8000 * (64 * μ) * ξ := by positivity
  refine ⟨fun d hd hev c w hcw => ?_, fun d hd hev c w b hcw hcb hwb => ?_⟩
  · have h1 := h53.1 d hd hev c w hcw
    rw [(hfix d hd hev).1 c w hcw] at h1
    have h2 := h.Phat_close (Omega_mono (by omega) hd) hev hcw
    exact (h1.trans' h2 hA).mono
      (step_bound hμ1 hξ hε0.le hε1 (by norm_num) (by norm_num))
  · have h1 := h53.2 d hd hev c w b hcw hcb hwb
    rw [(hfix d hd hev).2 c w b hcw hcb hwb] at h1
    have h2 := h.Yhat_close (Omega_mono (by omega) hd) hev hcw hcb hwb
    exact (h1.trans' h2 hA).mono
      (step_bound hμ1 hξ hε0.le hε1 (by norm_num) (by norm_num))

/-- The a-priori bound `χ⁽²⁾ ≤ 128`. -/
theorem init : ChiLe Ω₀ 2 P Pgr Y Ygr 128 := by
  refine ⟨fun d hd hev a v hav => ?_, fun d hd hev a v b hav hab hvb => ?_⟩
  · obtain ⟨h1, h2⟩ := h.gr.Pgr_bounds h.μ8 hd.1 a v
    have h3 := h.ex.P_le d hd.1 hev a v
    have h4 := P_nonneg a v d
    have h5 := (h.gr.basic hd.1).2.1
    unfold Close
    rw [abs_of_pos (by linarith : 0 < Pgr a v d), abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := h.gr.Ygr_bounds h.μ8 hd.1 a v b
    have h3 := h.ex.Y_le h.μ8 hd hev hav hab hvb
    have h4 := Y_nonneg a v b d
    have h5 := (h.gr.basic hd.1).2.1
    have h6 := h.ex.P_le d hd.1 hev a v
    have h7 := P_nonneg a v d
    have h8 : Y a v b d ≤ 6 * mu d ^ 2 := by nlinarith
    have h9 : 0 < Ygr a v b d := lt_of_lt_of_le (by positivity) h1
    unfold Close
    rw [abs_of_pos h9, abs_le]
    constructor <;> linarith

/-- `k` contraction steps: `χ⁽⁴ᵏ⁺²⁾ ≤ 128/2ᵏ + 884ε`. -/
theorem iterate (k : ℕ) : ChiLe Ω₀ (2 + 4 * k) P Pgr Y Ygr (128 / 2 ^ k + 884 * ε) := by
  have hε0 := h.ε_pos
  induction k with
  | zero =>
    have hb : (128 : ℝ) ≤ 128 / 2 ^ 0 + 884 * ε := by norm_num; linarith
    exact And.imp (fun h1 d hd hev c w hcw => (h1 d hd hev c w hcw).mono hb)
      (fun h2 d hd hev c w b hcw hcb hwb => (h2 d hd hev c w b hcw hcb hwb).mono hb) h.init
  | succ k ih =>
    have hε1 := h.ε_le
    have hμ1 := h.μ_le
    have hμ0 := h.μ_pos
    have hk : (0 : ℝ) < 128 / 2 ^ k := by positivity
    have hk1 : 128 / 2 ^ k ≤ (128 : ℝ) :=
      div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have hξ : 128 / 2 ^ k + 884 * ε ≤ (129 : ℝ) := by linarith
    have := h.step (by omega) (by positivity)
      (by nlinarith [mul_le_mul hμ1 hξ (by positivity) (by norm_num)]) ih
    rw [show 2 + 4 * (k + 1) = 2 + 4 * k + 4 by ring]
    have hb : (128 / 2 ^ k + 884 * ε) / 2 + 442 * ε = 128 / 2 ^ (k + 1) + 884 * ε := by
      rw [pow_succ]; ring
    rw [hb] at this
    exact this

/-- `R = R^gr(1 + O(μξ + ε))` on odd sequences of `Ω⁽ˢ⁺¹⁾`, given `χ⁽ˢ⁾ ≤ ξ`. -/
theorem R_close {s : ℕ} (hs : 2 ≤ s) {ξ : ℝ} (hξ : 0 < ξ) (hμξ : 64 * μ * ξ ≤ 1 / 20)
    (hχ : ChiLe Ω₀ s P Pgr Y Ygr ξ) {d : Seq n} (hd : d ∈ Omega Ω₀ (s + 1)) (hodd : ¬ IsEven d)
    (a b : Fin n) : Close (R a b d) (Rgr a b d) (20 * (64 * μ) * ξ * (1 + ε) + ε) := by
  have hμ0 := h.μ_pos
  have hμ1 := h.μ_le
  rw [← h.ex.opR_eq h.μ8 (Omega_mono (by omega) hd) hodd a b]
  have h52 := (lemma_5_2_explicit d (h.ex.two_le d hd.1) hξ (μ₀ := 64 * μ) (by positivity)
    (by linarith) hμξ P Pgr Y Ygr (opR P Y) Rgr).1 hodd
    ((h.gr.inPi h.μ8 le_rfl).mono fun d' hd' => (Q0_subset_Omega hd hd').1)
    (fun d' hd' c w hcw => hχ.1 d' (Q0_subset_Omega hd hd') hd'.1 c w hcw)
    (fun d' hd' c w e hcw hce hwe => hχ.2 d' (Q0_subset_Omega hd hd') hd'.1 c w e hcw hce hwe) a b
  exact h52.trans' (h.a d hd.1 a b) (by positivity)

end OK

end LW
