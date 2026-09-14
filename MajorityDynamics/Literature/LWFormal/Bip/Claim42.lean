import MajorityDynamics.Literature.LWFormal.Bip.FixedPoint
import MajorityDynamics.Literature.LWFormal.Claim64

set_option autoImplicit true

/-!
# Claim 4.2 (bipartite): contraction of `𝒞` around `(P*, Y*)`

On a set `Ω₀` where the exact `(P, Y)` is a fixed point of `𝒞` and Lemma 4.1 holds with error
`ε`, repeated application of the contraction gives `P = P*(1 + O(ε))` on `Ω⁽⁴ᵏ⁺²⁾`.
-/

namespace LW.Bip

open Finset

variable {ℓ n : ℕ}

/-- Hypotheses of Claim 4.2 on `Ω₀`. -/
structure OK (φ μ ε : ℝ) (Ω₀ : Set (BSeq ℓ n)) : Prop where
  ex : ExactOK μ Ω₀
  st : StOK φ μ Ω₀
  μ_pos : 0 < μ
  μ_le : μ ≤ 1 / 10 ^ 9
  ε_pos : 0 < ε
  ε_le : ε ≤ 1 / 1000
  a : ∀ d ∈ Ω₀, SH d → ∀ a b, Close (opR Pst Yst a b d) (Rst a b d) ε
  b : ∀ d ∈ Ω₀, Bal d → ∀ a v, Close (opP Pst Rst a v d) (Pst a v d) ε
  c : ∀ d ∈ Ω₀, Bal d → ∀ a v b, a ≠ b → Close (opY Pst Yst a v b d) (Yst a v b d) ε

namespace OK

variable {φ μ ε : ℝ} {Ω₀ : Set (BSeq ℓ n)} (h : OK φ μ ε Ω₀)
include h

theorem μ8 : μ ≤ 1 / 8 := h.μ_le.trans (by norm_num)

theorem one_le : ∀ d ∈ Ω₀, ∀ a, 1 ≤ d.1 a := fun _ hd a => h.ex.one_le hd a

/-- `p̂ = 𝒫(P*, ℛ(P*, Y*)) = P*(1 ± 22ε)` on balanced sequences of `Ω⁽²⁾`. -/
theorem Phat_close {d : BSeq ℓ n} (hd : d ∈ Omega Ω₀ 2) (hbal : Bal d) (a : Fin ℓ) (v : Fin n) :
    Close (opP Pst (opR Pst Yst) a v d) (Pst a v d) (22 * ε) := by
  have hμ0 := h.μ_pos
  have hε0 := h.ε_pos
  have hε1 := h.ε_le
  have hμ1 := h.μ_le
  have hμ₀ : (0 : ℝ) < 64 * μ := by positivity
  have hcancel : 64 * μ * (ε / (64 * μ)) = ε := mul_div_cancel₀ _ hμ₀.ne'
  have h52 := (lemma_2_8_explicit d (h.one_le d hd.1) (ξ := ε / (64 * μ)) (by positivity) hμ₀
    (by linarith) (by rw [hcancel]; linarith) Pst Pst Yst Yst (opR Pst Yst) Rst).2.1 hbal
    ((h.st.inPi h.μ8 le_rfl).mono fun d' hd' => (Q0_subset_Omega (s := 0) hd hd').1) a v
    (fun d' hd' c => h.st.Rst_nonneg h.μ8 (Q1_subset_Omega (s := 1) hd hd').1 c a)
    (fun _ _ _ => Close.refl _ (by positivity))
    (fun d' hd' c => (h.a d' (Q1_subset_Omega (s := 1) hd hd').1 hd'.1 c a).mono hcancel.symm.le)
  have h20 : 20 * (64 * μ) * (ε / (64 * μ)) = 20 * ε := by rw [mul_assoc, hcancel]
  refine (h52.trans' (h.b d hd.1 hbal a v) (by positivity)).mono ?_
  rw [h20]; nlinarith

/-- `𝒴(p̂, Y*) = Y*(1 ± 442ε)` on balanced sequences of `Ω⁽⁴⁾`. -/
theorem Yhat_close {d : BSeq ℓ n} (hd : d ∈ Omega Ω₀ 4) (hbal : Bal d) (a : Fin ℓ) (v : Fin n)
    {b : Fin ℓ} (hab : a ≠ b) :
    Close (opY (opP Pst (opR Pst Yst)) Yst a v b d) (Yst a v b d) (442 * ε) := by
  have hμ0 := h.μ_pos
  have hε0 := h.ε_pos
  have hε1 := h.ε_le
  have hμ1 := h.μ_le
  have hμ₀ : (0 : ℝ) < 64 * μ := by positivity
  have hcancel : 64 * μ * (22 * ε / (64 * μ)) = 22 * ε := mul_div_cancel₀ _ hμ₀.ne'
  have h52 := (lemma_2_8_explicit d (h.one_le d hd.1) (ξ := 22 * ε / (64 * μ)) (by positivity)
    hμ₀ (by linarith) (by rw [hcancel]; linarith) (opP Pst (opR Pst Yst)) Pst Yst Yst
    (opR Pst Yst) Rst).2.2 hbal
    ((h.st.inPi h.μ8 le_rfl).mono fun d' hd' => (Q0_subset_Omega (s := 2) hd hd').1) a v b hab
    (fun d' hd' c => (h.Phat_close (Q0_subset_Omega (s := 2) hd hd') hd'.1 c v).mono
      hcancel.symm.le)
    (fun _ _ _ _ _ _ => Close.refl _ (by positivity))
  have h440 : 20 * (64 * μ) * (22 * ε / (64 * μ)) = 440 * ε := by rw [mul_assoc, hcancel]; ring
  refine (h52.trans' (h.c d hd.1 hbal a v b hab) (by positivity)).mono ?_
  rw [h440]; nlinarith

/-- One contraction step: `χ⁽ˢ⁾ ≤ ξ ⇒ χ⁽ˢ⁺⁴⁾ ≤ ξ/2 + 442ε` (`s ≥ 2`). -/
theorem step {s : ℕ} (hs : 2 ≤ s) {ξ : ℝ} (hξ : 0 < ξ) (hμξ : 64 * μ * ξ ≤ 1 / 8000)
    (hχ : ChiLe Ω₀ s P Pst Y Yst ξ) : ChiLe Ω₀ (s + 4) P Pst Y Yst (ξ / 2 + 442 * ε) := by
  have hμ0 := h.μ_pos
  have hε0 := h.ε_pos
  have hε1 := h.ε_le
  have hμ1 := h.μ_le
  have h53 := contraction_explicit Ω₀ h.one_le hξ (μ₀ := 64 * μ) (by positivity) (by linarith)
    hμξ s P Pst Y Yst ((h.st.inPi h.μ8 le_rfl).mono (Omega_subset _ _))
    (h.st.inPi_of_close h.μ8 le_rfl (Omega_subset _ _) (opP Pst (opR Pst Yst))
      fun d hd hbal a v => (h.Phat_close (Omega_mono (by omega) hd) hbal a v).mono (by linarith))
    hχ
  have hfix : ∀ d ∈ Omega Ω₀ (s + 4), Bal d →
      (∀ a v, (opC P Y).1 a v d = P a v d) ∧
      (∀ a v b, a ≠ b → (opC P Y).2 a v b d = Y a v b d) :=
    fun d hd hbal => h.ex.opC_fixed h.μ8 (Omega_mono (by omega) hd) hbal
  have hA : 0 ≤ 8000 * (64 * μ) * ξ := by positivity
  refine ⟨fun d hd hbal c w => ?_, fun d hd hbal c w b hcb => ?_⟩
  · have h1 := h53.1 d hd hbal c w
    rw [(hfix d hd hbal).1 c w] at h1
    have h2 := h.Phat_close (Omega_mono (by omega) hd) hbal c w
    exact (h1.trans' h2 hA).mono (step_bound hμ1 hξ hε0.le hε1 (by norm_num) (by norm_num))
  · have h1 := h53.2 d hd hbal c w b hcb
    rw [(hfix d hd hbal).2 c w b hcb] at h1
    have h2 := h.Yhat_close (Omega_mono (by omega) hd) hbal c w hcb
    exact (h1.trans' h2 hA).mono (step_bound hμ1 hξ hε0.le hε1 (by norm_num) (by norm_num))

/-- The a-priori bound `χ⁽²⁾ ≤ 128`. -/
theorem init : ChiLe Ω₀ 2 P Pst Y Yst 128 := by
  refine ⟨fun d hd hbal a v => ?_, fun d hd hbal a v b hab => ?_⟩
  · obtain ⟨h1, h2⟩ := h.st.Pst_bounds h.μ8 hd.1 a v
    have h3 := h.ex.P_le d hd.1 hbal a v
    have h4 := P_nonneg a v d
    have h5 := (h.st.basic hd.1).2.2.1
    unfold Close
    rw [abs_of_pos (by linarith : 0 < Pst a v d), abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := h.st.Yst_bounds h.μ8 hd.1 a v b
    have h3 := h.ex.Y_le h.μ8 hd hbal v hab
    have h4 := Y_nonneg a v b d
    have h5 := (h.st.basic hd.1).2.2.1
    have h6 := h.ex.P_le d hd.1 hbal a v
    have h7 := P_nonneg a v d
    have h8 : Y a v b d ≤ 6 * mu d ^ 2 := by nlinarith
    have h9 : 0 < Yst a v b d := lt_of_lt_of_le (by positivity) h1
    unfold Close
    rw [abs_of_pos h9, abs_le]
    constructor <;> linarith

/-- `k` contraction steps: `χ⁽⁴ᵏ⁺²⁾ ≤ 128/2ᵏ + 884ε`. -/
theorem iterate (k : ℕ) : ChiLe Ω₀ (2 + 4 * k) P Pst Y Yst (128 / 2 ^ k + 884 * ε) := by
  have hε0 := h.ε_pos
  induction k with
  | zero =>
    have hb : (128 : ℝ) ≤ 128 / 2 ^ 0 + 884 * ε := by norm_num; linarith
    exact And.imp (fun h1 d hd hbal c w => (h1 d hd hbal c w).mono hb)
      (fun h2 d hd hbal c w b hcb => (h2 d hd hbal c w b hcb).mono hb) h.init
  | succ k ih =>
    have hε1 := h.ε_le
    have hμ1 := h.μ_le
    have hμ0 := h.μ_pos
    have hk : (0 : ℝ) < 128 / 2 ^ k := by positivity
    have hk1 : 128 / 2 ^ k ≤ (128 : ℝ) := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have hξ : 128 / 2 ^ k + 884 * ε ≤ (129 : ℝ) := by linarith
    have := h.step (by omega) (by positivity)
      (by nlinarith [mul_le_mul hμ1 hξ (by positivity) (by norm_num)]) ih
    rw [show 2 + 4 * (k + 1) = 2 + 4 * k + 4 by ring]
    have hb : (128 / 2 ^ k + 884 * ε) / 2 + 442 * ε = 128 / 2 ^ (k + 1) + 884 * ε := by
      rw [pow_succ]; ring
    rw [hb] at this
    exact this

/-- `R = R*(1 + O(μξ + ε))` on `S`-heavy sequences of `Ω⁽ˢ⁺¹⁾`, given `χ⁽ˢ⁾ ≤ ξ`. -/
theorem R_close {s : ℕ} (hs : 2 ≤ s) {ξ : ℝ} (hξ : 0 < ξ) (hμξ : 64 * μ * ξ ≤ 1 / 20)
    (hχ : ChiLe Ω₀ s P Pst Y Yst ξ) {d : BSeq ℓ n} (hd : d ∈ Omega Ω₀ (s + 1)) (hSH : SH d)
    (a b : Fin ℓ) : Close (R a b d) (Rst a b d) (20 * (64 * μ) * ξ * (1 + ε) + ε) := by
  have hμ0 := h.μ_pos
  have hμ1 := h.μ_le
  rw [← h.ex.opR_eq h.μ8 (Omega_mono (by omega) hd) hSH a b]
  have h52 := (lemma_2_8_explicit d (h.one_le d hd.1) hξ (μ₀ := 64 * μ) (by positivity)
    (by linarith) hμξ P Pst Y Yst (opR P Y) Rst).1 hSH
    ((h.st.inPi h.μ8 le_rfl).mono fun d' hd' => (Q0_subset_Omega hd hd').1)
    (fun d' hd' c w e hce => hχ.2 d' (Q0_subset_Omega hd hd') hd'.1 c w e hce) a b
  exact h52.trans' (h.a d hd.1 hSH a b) (by positivity)

end OK

end LW.Bip
