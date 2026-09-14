import MajorityDynamics.Literature.LWFormal.Bip.Lemma41
import MajorityDynamics.Literature.LWFormal.FixedPoint

set_option autoImplicit true

/-!
# Bipartite: the exact `(P, Y)` is a fixed point of `𝒞`, and `(P,Y)`, `(P*,Y*)` lie in `Π`

Proposition 2.6 in the operator language of §2.3, on a set of sequences where every balanced
sequence is realizable, all `s_a ≥ 2` and `P_{av} ≤ 2μ`.
-/

namespace LW.Bip

open Finset Real

variable {ℓ n : ℕ}

theorem P_nonneg (a : Fin ℓ) (v : Fin n) (d : BSeq ℓ n) : 0 ≤ P a v d := by unfold P; positivity

theorem Y_nonneg (a : Fin ℓ) (v : Fin n) (b : Fin ℓ) (d : BSeq ℓ n) : 0 ≤ Y a v b d := by
  unfold Y; positivity

theorem Y_comm (a : Fin ℓ) (v : Fin n) (b : Fin ℓ) (d : BSeq ℓ n) : Y a v b d = Y b v a d := by
  simp only [Y, Navb, pair_comm]

/-- `∑_v P_{av}(d) = s_a`. -/
theorem sum_P (d : BSeq ℓ n) (hN : 0 < N d) (a : Fin ℓ) : ∑ v, P a v d = d.1 a := by
  have h := sum_Nav_T d a
  have hN' : (N d : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [P]
  rw [← sum_div, div_eq_iff hN']
  exact_mod_cast h

/-- `N_{av}(d) > 0` when `d - e_a - e_v` is realizable and `P_{av}(d - e_a - e_v) < 1`. -/
theorem Nav_pos {d : BSeq ℓ n} {a : Fin ℓ} {v : Fin n} (hN : 0 < N (d - eS a - eT v))
    (hP : P a v (d - eS a - eT v) < 1) : 0 < Nav a v d := by
  have h := lemma_2_2 a v d
  have hN' : (0 : ℝ) < N (d - eS a - eT v) := by exact_mod_cast hN
  unfold P at hP
  rw [div_lt_one hN'] at hP
  have : Nav a v (d - eS a - eT v) < N (d - eS a - eT v) := by exact_mod_cast hP
  omega

theorem mu_sub_eS_le (d : BSeq ℓ n) (a : Fin ℓ) : mu (d - eS a) ≤ mu d := by
  rw [mu_sub_eS]; linarith [(by positivity : (0 : ℝ) ≤ 1 / (2 * ℓ * n))]

theorem mu_sub_eT_le (d : BSeq ℓ n) (v : Fin n) : mu (d - eT v) ≤ mu d := by
  rw [mu_sub_eT]; linarith [(by positivity : (0 : ℝ) ≤ 1 / (2 * ℓ * n))]

theorem mu_nonneg_of_bal {d : BSeq ℓ n} (h : Bal d) (hs : ∀ a, 0 ≤ d.1 a) : 0 ≤ mu d := by
  have : (0 : ℝ) ≤ M1 d.1 := by
    unfold M1; push_cast; exact sum_nonneg fun a _ => by exact_mod_cast hs a
  have h' : (M1 d.1 : ℝ) = M1 d.2 := by exact_mod_cast h
  unfold mu; rw [← h']; positivity

/-- Hypotheses on a set of sequences making the exact `(P,Y)` a fixed point of `𝒞`. -/
structure ExactOK (μ : ℝ) (D₀ : Set (BSeq ℓ n)) : Prop where
  two_le : ∀ d ∈ D₀, ∀ a, 2 ≤ d.1 a
  mu_le : ∀ d ∈ D₀, mu d ≤ μ
  N_pos : ∀ d ∈ D₀, Bal d → 0 < N d
  P_le : ∀ d ∈ D₀, Bal d → ∀ a v, P a v d ≤ 2 * mu d

namespace ExactOK

variable {μ : ℝ} {D₀ : Set (BSeq ℓ n)} (h : ExactOK μ D₀) (hμ : μ ≤ 1 / 8)
include h hμ

omit hμ in
theorem one_le {d : BSeq ℓ n} (hd : d ∈ D₀) (a : Fin ℓ) : 1 ≤ d.1 a := by
  linarith [h.two_le d hd a]

omit hμ in
theorem mu_nonneg {d : BSeq ℓ n} (hd : d ∈ D₀) (hbal : Bal d) : 0 ≤ mu d :=
  mu_nonneg_of_bal hbal fun a => by linarith [h.two_le d hd a]

theorem P_lt_one {d : BSeq ℓ n} (hd : d ∈ D₀) (hbal : Bal d) (a : Fin ℓ) (v : Fin n) :
    P a v d < 1 := by
  have := h.P_le d hd hbal a v
  have := h.mu_le d hd
  linarith

/-- `Y_{avb}(d) ≤ 3μ(d) P_{av}(d)` for balanced `d ∈ Ω⁽²⁾`. -/
theorem Y_le {d : BSeq ℓ n} (hd : d ∈ Omega D₀ 2) (hbal : Bal d) {a b : Fin ℓ} (v : Fin n)
    (hab : a ≠ b) : Y a v b d ≤ 3 * mu d * P a v d := by
  have hd' : d - eS a - eT v ∈ D₀ :=
    Omega_subset _ _ (Q0_subset_Omega (s := 0) hd (sub_eS_sub_eT_mem_Q0 hbal a v))
  have hbal' : Bal (d - eS a - eT v) := (bal_sub_eS_sub_eT a v).2 hbal
  rw [prop_2_6c d a v hab (h.N_pos _ hd' hbal')]
  have hμd := h.mu_le d hd.1
  have hμd0 := h.mu_nonneg hd.1 hbal
  have hμ' : mu (d - eS a - eT v) ≤ mu d := (mu_sub_eT_le _ _).trans (mu_sub_eS_le _ _)
  have hPa := h.P_le _ hd' hbal' a v
  have hPb := h.P_le _ hd' hbal' b v
  have hPa0 := P_nonneg a v (d - eS a - eT v)
  have hY0 := Y_nonneg a v b (d - eS a - eT v)
  have hP0 := P_nonneg a v d
  have hden : 0 < 1 - P a v (d - eS a - eT v) := by linarith
  rw [div_le_iff₀ hden]
  have : P b v (d - eS a - eT v) - Y a v b (d - eS a - eT v) ≤ 2 * mu d := by linarith
  calc P a v d * (P b v (d - eS a - eT v) - Y a v b (d - eS a - eT v)) ≤ P a v d * (2 * mu d) :=
        mul_le_mul_of_nonneg_left this hP0
    _ ≤ 3 * mu d * P a v d * (1 - P a v (d - eS a - eT v)) := by
        nlinarith [mul_nonneg (mul_nonneg hμd0 hP0)
          (by linarith : 0 ≤ 1 - 3 * P a v (d - eS a - eT v))]

theorem inPi : InPi (3 * μ) (Omega D₀ 2) P Y where
  pa d hd hbal a v := ⟨P_nonneg a v d, by
    have := h.P_le d hd.1 hbal a v; have := h.mu_le d hd.1; have := h.mu_nonneg hd.1 hbal
    linarith⟩
  pb d hd hbal a b hab := by
    have hN := h.N_pos d hd.1 hbal
    have hμd := h.mu_le d hd.1
    have hμd0 := h.mu_nonneg hd.1 hbal
    calc ∑ v, Y a v b d ≤ ∑ v, 3 * mu d * P a v d :=
          sum_le_sum fun v _ => h.Y_le hμ hd hbal v hab
      _ = 3 * mu d * d.1 a := by rw [← mul_sum, sum_P d hN]
      _ ≤ 3 * μ * d.1 a := by
          have : (0 : ℝ) ≤ d.1 a := by exact_mod_cast (h.two_le d hd.1 a).trans' (by norm_num)
          gcongr
  pc d hd hbal a v b hab := by
    refine ⟨Y_nonneg _ _ _ _, ?_⟩
    rw [Y_comm]
    have := h.Y_le hμ hd hbal v hab.symm
    have hμd := h.mu_le d hd.1
    have := P_nonneg b v d
    nlinarith

theorem bad_lt_one {d : BSeq ℓ n} (hd : d ∈ Omega D₀ 2) (hbal : Bal d) {a b : Fin ℓ}
    (hab : a ≠ b) : bad P Y a b d < 1 := by
  have hμ0 : 0 ≤ μ := (h.mu_nonneg hd.1 hbal).trans (h.mu_le d hd.1)
  have := (bad_bounds (h.inPi hμ) (by positivity) hd hbal hab (h.one_le hd.1 a)).2
  linarith

omit h hμ in
theorem B_eq_bad {a b : Fin ℓ} (hab : a ≠ b) (d : BSeq ℓ n) : B a b d = bad P Y a b d := by
  simp [B, bad, hab]

/-- `ℛ(P,Y) = R` on `S`-heavy sequences of `Ω⁽³⁾` (Proposition 2.6(b)). -/
theorem opR_eq {d : BSeq ℓ n} (hd : d ∈ Omega D₀ 3) (hSH : SH d) (a b : Fin ℓ) :
    opR P Y a b d = R a b d := by
  have hQ : ∀ c, d - eS c ∈ Omega D₀ 2 := fun c =>
    mem_Omega_of_dist1 (s := 2) (t := 1) hd (by simp [dist1_sub_eS])
  have hNc : ∀ c, 0 < N (d - eS c) := fun c => h.N_pos _ (hQ c).1 (bal_sub_eS_of_SH hSH c)
  by_cases hab : a = b
  · subst hab
    have hN : (N (d - eS a) : ℝ) ≠ 0 := by exact_mod_cast (hNc a).ne'
    have hda : (d.1 a : ℝ) ≠ 0 := by
      exact_mod_cast (show d.1 a ≠ 0 by have := h.two_le d hd.1 a; omega)
    simp [opR, bad, R, hN, hda]
  rw [prop_2_6b d hab (hNc a) (hNc b), opR, B_eq_bad hab, B_eq_bad (Ne.symm hab)]
  rw [B_eq_bad (Ne.symm hab)]
  exact (h.bad_lt_one hμ (hQ a) (bal_sub_eS_of_SH hSH a) (Ne.symm hab)).ne

/-- `𝒫(P, ℛ(P,Y)) = P` on balanced sequences of `Ω⁽⁴⁾` (Proposition 2.6(a)). -/
theorem opP_eq {d : BSeq ℓ n} (hd : d ∈ Omega D₀ 4) (hbal : Bal d) (a : Fin ℓ) (v : Fin n) :
    opP P (opR P Y) a v d = P a v d := by
  have hd2 : d - eS a - eT v ∈ Omega D₀ 2 := Q0_subset_Omega hd (sub_eS_sub_eT_mem_Q0 hbal a v)
  have hbal2 : Bal (d - eS a - eT v) := (bal_sub_eS_sub_eT a v).2 hbal
  have hdv : d - eT v ∈ Omega D₀ 3 :=
    mem_Omega_of_dist1 (s := 3) (t := 1) hd (by simp [dist1_sub_eT])
  have hNav : 0 < Nav a v d := Nav_pos (h.N_pos _ hd2.1 hbal2) (h.P_lt_one hμ hd2.1 hbal2 a v)
  rw [prop_2_6a d a v hNav, opP]
  congr 2
  refine sum_congr rfl fun b _ => ?_
  rw [h.opR_eq hμ hdv (SH_sub_eT_of_bal hbal v)]

/-- `𝒞(P,Y) = (P,Y)` on balanced sequences of `Ω⁽⁶⁾`. -/
theorem opC_fixed {d : BSeq ℓ n} (hd : d ∈ Omega D₀ 6) (hbal : Bal d) :
    (∀ a v, (opC P Y).1 a v d = P a v d) ∧
    (∀ a v b, a ≠ b → (opC P Y).2 a v b d = Y a v b d) := by
  have hd4 : d ∈ Omega D₀ 4 := Omega_mono (by norm_num) hd
  refine ⟨fun a v => h.opP_eq hμ hd4 hbal a v, fun a v b hab => ?_⟩
  have hd2 : d - eS a - eT v ∈ Omega D₀ 4 := Q0_subset_Omega hd (sub_eS_sub_eT_mem_Q0 hbal a v)
  have hbal2 : Bal (d - eS a - eT v) := (bal_sub_eS_sub_eT a v).2 hbal
  show opY (opP P (opR P Y)) Y a v b d = Y a v b d
  rw [opY, h.opP_eq hμ hd4 hbal a v, h.opP_eq hμ hd2 hbal2 b v, h.opP_eq hμ hd2 hbal2 a v,
    ← prop_2_6c d a v hab (h.N_pos _ hd2.1 hbal2)]

end ExactOK

/-! ### `(P*, Y*) ∈ Π` -/

/-- `|AcorrB| ≤ 1/100` under the smallness hypotheses. -/
theorem abs_AcorrB_le {μ sS sT x y η : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 8) (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 32) (hx : |x| ≤ 2 * η) (hy : |y| ≤ 2 * η) (hsS : 0 ≤ sS)
    (hsS' : sS ≤ 2 * μ * η ^ 2) (hsT : 0 ≤ sT) (hsT' : sT ≤ 2 * μ * η ^ 2) :
    |AcorrB μ sS sT x y| ≤ 1 / 100 := by
  have hη2 : η ^ 2 ≤ 1 / 1024 := by nlinarith
  have h1 : |μ * x * y| ≤ 4 * μ * η ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hμ0]
    calc μ * |x| * |y| ≤ μ * (2 * η) * (2 * η) := by gcongr
      _ = 4 * μ * η ^ 2 := by ring
  have h2 : |x * sT| ≤ 2 * η * (2 * μ * η ^ 2) := by
    rw [abs_mul, abs_of_nonneg hsT]; gcongr
  have h3 : |y * sS| ≤ 2 * η * (2 * μ * η ^ 2) := by
    rw [abs_mul, abs_of_nonneg hsS]; gcongr
  have hA : |-μ * x * y + x * sT + y * sS| ≤ 4 * μ * η ^ 2 + 4 * η * (2 * μ * η ^ 2) := by
    rw [show -μ * x * y = -(μ * x * y) by ring]
    exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
      (by rw [abs_neg]; linarith))
  unfold AcorrB
  rw [abs_div, abs_of_pos (by linarith : 0 < 1 - μ), div_le_iff₀ (by linarith)]
  have : η * (2 * μ * η ^ 2) ≤ μ * η ^ 2 / 16 := by nlinarith
  have hμη : μ * η ^ 2 ≤ 1 / 8192 := by nlinarith
  nlinarith

/-- `μ/4 ≤ π ≤ 2μ` under the smallness hypotheses. -/
theorem piB_bounds {μ sS sT x y η : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 8) (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 32) (hx : |x| ≤ 2 * η) (hy : |y| ≤ 2 * η) (hsS : 0 ≤ sS)
    (hsS' : sS ≤ 2 * μ * η ^ 2) (hsT : 0 ≤ sT) (hsT' : sT ≤ 2 * μ * η ^ 2) :
    μ / 4 ≤ piB μ sS sT x y ∧ piB μ sS sT x y ≤ 2 * μ := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have hη2 : η ^ 2 ≤ 1 / 1024 := by nlinarith
  obtain ⟨hE1, hE2⟩ := abs_le.1 (abs_AcorrB_le hμ0 hμ hη hη' hx hy hsS hsS' hsT hsT')
  have hxy1 : 87 / 100 ≤ (1 + x) * (1 + y) := by nlinarith
  have hxy2 : (1 + x) * (1 + y) ≤ 114 / 100 := by nlinarith
  have hP : piB μ sS sT x y = μ * ((1 + x) * (1 + y) * (1 + AcorrB μ sS sT x y)) := by
    unfold piB; ring
  rw [hP]
  constructor
  · have : 87 / 100 * (99 / 100) ≤ (1 + x) * (1 + y) * (1 + AcorrB μ sS sT x y) :=
      mul_le_mul hxy1 (by linarith) (by norm_num) (by linarith)
    nlinarith
  · have : (1 + x) * (1 + y) * (1 + AcorrB μ sS sT x y) ≤ 114 / 100 * (101 / 100) :=
      mul_le_mul hxy2 (by linarith) (by linarith) (by norm_num)
    nlinarith

/-- `0 ≤ TcB ≤ 1` under the smallness hypotheses. -/
theorem TcB_bounds {μ δT xa xb η : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 8) (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 32) (hxa : |xa| ≤ 2 * η) (hxb : |xb| ≤ 2 * η) (hδ : 0 ≤ δT)
    (hδ' : δT ≤ η ^ 2) : 0 ≤ TcB μ δT xa xb ∧ TcB μ δT xa xb ≤ 1 := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 hxa
  obtain ⟨hb1, hb2⟩ := abs_le.1 hxb
  have hη2 : η ^ 2 ≤ 1 / 1024 := by nlinarith
  have hnum0 : 0 ≤ μ * (1 + xa) - μ ^ 2 * (1 + xa + xb) := by nlinarith
  have hnum1 : μ * (1 + xa) - μ ^ 2 * (1 + xa + xb) ≤ 1 / 4 := by nlinarith
  unfold TcB
  constructor
  · exact div_nonneg (mul_nonneg hδ hnum0) (by linarith)
  · rw [div_le_one (by linarith)]; nlinarith

/-- Hypotheses on a set of sequences under which `(P*, Y*)` is controlled. -/
structure StOK (φ μ : ℝ) (D₀ : Set (BSeq ℓ n)) : Prop where
  φ₁ : 1 / 2 ≤ φ
  φ₂ : φ < 3 / 5
  ℓ2 : 2 ≤ ℓ
  n2 : 2 ≤ n
  spread : ∀ d ∈ D₀, Spread φ d
  dmin_ge : ∀ d ∈ D₀, (32768 : ℝ) ≤ dmin d
  mu_le : ∀ d ∈ D₀, mu d ≤ μ

theorem rpow_32768 : (32768 : ℝ) ^ (-(2 / 5 : ℝ)) = 1 / 64 := by
  rw [show (32768 : ℝ) = 2 ^ (15 : ℕ) by norm_num, ← rpow_natCast, ← rpow_mul (by norm_num)]
  norm_num

namespace StOK

variable {φ μ : ℝ} {D₀ : Set (BSeq ℓ n)} (h : StOK φ μ D₀) (hμ : μ ≤ 1 / 8)
include h

/-- The scale `η = 2 · 32768^{φ-1} ≤ 1/32` on `D₀`. -/
theorem eta {d : BSeq ℓ n} (hd : d ∈ D₀) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 32 ∧ (∀ a, |eps d.1 a| ≤ η) ∧ (∀ v, |eps d.2 v| ≤ η) ∧
      1 / dbar d.1 ≤ η ^ 2 ∧ 1 / dbar d.2 ≤ η ^ 2 ∧
      sigma2 d.1 / dbar d.1 ^ 2 ≤ η ^ 2 ∧ sigma2 d.2 / dbar d.2 ^ 2 ≤ η ^ 2 := by
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by have := h.ℓ2; omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := h.n2; omega)
  have hD := h.dmin_ge d hd
  have hs : (32768 : ℝ) ≤ dbar d.1 := hD.trans (min_le_left _ _)
  have ht : (32768 : ℝ) ≤ dbar d.2 := hD.trans (min_le_right _ _)
  obtain ⟨h0, h25, -, -, -⟩ := eta_bounds (D := 32768) h.φ₁ h.φ₂ (by norm_num)
  obtain ⟨hεS, hδS, hσS⟩ := side_bounds h.φ₁ h.φ₂ (by norm_num) hs (h.spread d hd).2.1 hℓ0
  obtain ⟨hεT, hδT, hσT⟩ := side_bounds h.φ₁ h.φ₂ (by norm_num) ht (h.spread d hd).2.2 hn0
  refine ⟨_, h0, ?_, hεS, hεT, hδS, hδT, hσS, hσT⟩
  rw [rpow_32768] at h25; linarith

theorem basic {d : BSeq ℓ n} (hd : d ∈ D₀) :
    0 < dbar d.1 ∧ 0 < dbar d.2 ∧ 0 < mu d ∧ mu d ≤ μ ∧ (2 : ℝ) ≤ ℓ ∧ (2 : ℝ) ≤ n ∧
      dbar d.1 / n ≤ 2 * mu d ∧ dbar d.2 / ℓ ≤ 2 * mu d := by
  have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast h.ℓ2
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.n2
  have hD := h.dmin_ge d hd
  unfold dmin at hD
  have hs : 0 < dbar d.1 := by linarith [min_le_left (dbar d.1) (dbar d.2)]
  have ht : 0 < dbar d.2 := by linarith [min_le_right (dbar d.1) (dbar d.2)]
  have hMs : 0 < (M1 d.1 : ℝ) := by
    unfold dbar at hs; exact (div_pos_iff_of_pos_right (by linarith)).1 hs
  have hMt : 0 < (M1 d.2 : ℝ) := by
    unfold dbar at ht; exact (div_pos_iff_of_pos_right (by linarith)).1 ht
  refine ⟨hs, ht, by unfold mu; positivity, h.mu_le d hd, hℓ2, hn2, ?_, ?_⟩
  · unfold mu dbar
    rw [div_div, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  · unfold mu dbar
    rw [div_div, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith

theorem sS_le {d : BSeq ℓ n} (hd : d ∈ D₀) {η : ℝ} (hσ : sigma2 d.1 / dbar d.1 ^ 2 ≤ η ^ 2) :
    0 ≤ sS d ∧ sS d ≤ 2 * mu d * η ^ 2 := by
  obtain ⟨hs, -, hμ0, -, -, hn2, hdn, -⟩ := h.basic hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hσ0 : 0 ≤ sigma2 d.1 := sigma2_nonneg _
  refine ⟨by unfold sS; positivity, ?_⟩
  rw [sS, show sigma2 d.1 / (dbar d.1 * n) = sigma2 d.1 / dbar d.1 ^ 2 * (dbar d.1 / n) by
    field_simp]
  nlinarith [mul_le_mul hσ hdn (by positivity) (by positivity)]

theorem sT_le {d : BSeq ℓ n} (hd : d ∈ D₀) {η : ℝ} (hσ : sigma2 d.2 / dbar d.2 ^ 2 ≤ η ^ 2) :
    0 ≤ sT d ∧ sT d ≤ 2 * mu d * η ^ 2 := by
  obtain ⟨-, ht, hμ0, -, hℓ2, -, -, hdl⟩ := h.basic hd
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hσ0 : 0 ≤ sigma2 d.2 := sigma2_nonneg _
  refine ⟨by unfold sT; positivity, ?_⟩
  rw [sT, show sigma2 d.2 / (dbar d.2 * ℓ) = sigma2 d.2 / dbar d.2 ^ 2 * (dbar d.2 / ℓ) by
    field_simp]
  nlinarith [mul_le_mul hσ hdl (by positivity) (by positivity)]

include hμ

theorem Pst_bounds {d : BSeq ℓ n} (hd : d ∈ D₀) (a : Fin ℓ) (v : Fin n) :
    mu d / 4 ≤ Pst a v d ∧ Pst a v d ≤ 2 * mu d := by
  obtain ⟨η, hη0, hη1, hεS, hεT, -, -, hσS, hσT⟩ := h.eta hd
  obtain ⟨-, -, hμ0, hμd, -, -, -, -⟩ := h.basic hd
  obtain ⟨hS0, hS1⟩ := h.sS_le hd hσS
  obtain ⟨hT0, hT1⟩ := h.sT_le hd hσT
  exact piB_bounds hμ0 (hμd.trans hμ) hη0.le hη1 ((hεS a).trans (by linarith))
    ((hεT v).trans (by linarith)) hS0 hS1 hT0 hT1

theorem abs_AcorrB_le {d : BSeq ℓ n} (hd : d ∈ D₀) (a : Fin ℓ) (v : Fin n) :
    |AcorrB (mu d) (sS d) (sT d) (eps d.1 a) (eps d.2 v)| ≤ 1 / 100 := by
  obtain ⟨η, hη0, hη1, hεS, hεT, -, -, hσS, hσT⟩ := h.eta hd
  obtain ⟨-, -, hμ0, hμd, -, -, -, -⟩ := h.basic hd
  obtain ⟨hS0, hS1⟩ := h.sS_le hd hσS
  obtain ⟨hT0, hT1⟩ := h.sT_le hd hσT
  exact Bip.abs_AcorrB_le hμ0 (hμd.trans hμ) hη0.le hη1 ((hεS a).trans (by linarith))
    ((hεT v).trans (by linarith)) hS0 hS1 hT0 hT1

theorem Yst_bounds {d : BSeq ℓ n} (hd : d ∈ D₀) (a : Fin ℓ) (v : Fin n) (b : Fin ℓ) :
    mu d ^ 2 / 16 ≤ Yst a v b d ∧ Yst a v b d ≤ 8 * mu d ^ 2 := by
  obtain ⟨η, hη0, hη1, hεS, hεT, -, hδT, hσS, hσT⟩ := h.eta hd
  obtain ⟨-, ht, hμ0, hμd, -, -, -, -⟩ := h.basic hd
  obtain ⟨hS0, hS1⟩ := h.sS_le hd hσS
  obtain ⟨hT0, hT1⟩ := h.sT_le hd hσT
  have hμ8 : mu d ≤ 1 / 8 := hμd.trans hμ
  have h1 := h.Pst_bounds hμ hd a v
  have hz : |eps d.2 v - 1 / dbar d.2| ≤ 2 * η := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (one_div_pos.2 ht)]
    nlinarith [hεT v]
  have h2 := piB_bounds hμ0 hμ8 hη0.le hη1 ((hεS b).trans (by linarith)) hz hS0 hS1 hT0 hT1
  have h3 := TcB_bounds hμ0 hμ8 hη0.le hη1 ((hεS a).trans (by linarith))
    ((hεS b).trans (by linarith)) (by positivity) hδT
  unfold Yst
  constructor
  · calc mu d ^ 2 / 16 = mu d / 4 * (mu d / 4) * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul h1.1 h2.1 (by positivity) (by linarith)) (by linarith)
          (by norm_num) (by nlinarith)
  · calc Pst a v d * piB (mu d) (sS d) (sT d) (eps d.1 b) (eps d.2 v - 1 / dbar d.2) *
          (1 + TcB (mu d) (1 / dbar d.2) (eps d.1 a) (eps d.1 b))
        ≤ 2 * mu d * (2 * mu d) * 2 := by gcongr <;> linarith
      _ = 8 * mu d ^ 2 := by ring

theorem Rst_nonneg {d : BSeq ℓ n} (hd : d ∈ D₀) (a b : Fin ℓ) : 0 ≤ Rst a b d := by
  obtain ⟨η, hη0, hη1, hεS, -, hδS, -, -, hσT⟩ := h.eta hd
  obtain ⟨hs, -, hμ0, hμd, hℓ2, -, -, -⟩ := h.basic hd
  obtain ⟨hT0, hT1⟩ := h.sT_le hd hσT
  have hμ8 : mu d ≤ 1 / 8 := hμd.trans hμ
  obtain ⟨ha1, ha2⟩ := abs_le.1 (hεS a)
  obtain ⟨hb1, hb2⟩ := abs_le.1 (hεS b)
  have hη2 : η ^ 2 ≤ 1 / 1024 := by nlinarith
  have hδ0 : 0 ≤ 1 / dbar d.1 := by positivity
  have hlam0 : 0 < 1 / (ℓ : ℝ) := by positivity
  have hlam1 : 1 / (ℓ : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  unfold Rst rhoB
  have hma : mu d * (1 + eps d.1 a) ≤ 1 / 4 :=
    (mul_le_mul hμ8 (by linarith : 1 + eps d.1 a ≤ 2) (by linarith) (by norm_num)).trans
      (by norm_num)
  have hmb : mu d * (1 + eps d.1 b) ≤ 1 / 4 :=
    (mul_le_mul hμ8 (by linarith : 1 + eps d.1 b ≤ 2) (by linarith) (by norm_num)).trans
      (by norm_num)
  refine mul_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith))
    (div_nonneg (by nlinarith) (by nlinarith))) ?_
  have hsT : sT d / (1 - mu d) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hsT0 : 0 ≤ sT d / (1 - mu d) := div_nonneg hT0 (by linarith)
  have hT : |(eps d.1 a - eps d.1 b) * (sT d / (1 - mu d) - 1 / ℓ) / (1 - mu d)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by linarith : 0 < 1 - mu d), div_le_iff₀ (by linarith), abs_mul]
    have h1 : |eps d.1 a - eps d.1 b| ≤ 2 * η :=
      (abs_sub _ _).trans (by linarith [hεS a, hεS b])
    have h2 : |sT d / (1 - mu d) - 1 / ℓ| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    calc |eps d.1 a - eps d.1 b| * |sT d / (1 - mu d) - 1 / ℓ| ≤ 2 * η * 1 := by gcongr
      _ ≤ 1 / 2 * (1 - mu d) := by nlinarith
  linarith [(abs_le.1 hT).1]

theorem inPi {μp : ℝ} (hμp : 64 * μ ≤ μp) : InPi μp D₀ Pst Yst where
  pa d hd _ a v := by
    obtain ⟨h1, h2⟩ := h.Pst_bounds hμ hd a v
    have := (h.basic hd).2.2.1
    have := h.mu_le d hd
    exact ⟨by linarith, by linarith⟩
  pb d hd hbal a b _ := by
    obtain ⟨η, hη0, hη1, hεS, -, -, -, -, -⟩ := h.eta hd
    obtain ⟨hs, ht, hμ0, hμd, hℓ2, hn2, -, -⟩ := h.basic hd
    have hda : (d.1 a : ℝ) = dbar d.1 * (1 + eps d.1 a) := by unfold eps; field_simp; ring
    have hda' : dbar d.1 * (31 / 32) ≤ d.1 a := by
      rw [hda]; have := (abs_le.1 (hεS a)).1; nlinarith
    have hμn : mu d * n = dbar d.1 := by
      have := inv_n_of_bal hbal (by linarith) (by linarith) hs.ne'
      field_simp at this ⊢; linarith
    calc ∑ v, Yst a v b d ≤ ∑ _v : Fin n, 8 * mu d ^ 2 :=
          sum_le_sum fun v _ => (h.Yst_bounds hμ hd a v b).2
      _ = n * (8 * mu d ^ 2) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 8 * mu d * (mu d * n) := by ring
      _ = 8 * mu d * dbar d.1 := by rw [hμn]
      _ ≤ μp * d.1 a := by nlinarith
  pc d hd _ a v b _ := by
    obtain ⟨h1, h2⟩ := h.Yst_bounds hμ hd a v b
    obtain ⟨h3, -⟩ := h.Pst_bounds hμ hd b v
    have := (h.basic hd).2.2.1
    have := h.mu_le d hd
    exact ⟨le_trans (by positivity) h1, by nlinarith⟩

/-- `(p̂, Y*) ∈ Π` for any `p̂ = P*(1 ± 1/2)`. -/
theorem inPi_of_close {μp : ℝ} (hμp : 64 * μ ≤ μp) {D₁ : Set (BSeq ℓ n)} (hD₁ : D₁ ⊆ D₀)
    (p : PFun ℓ n) (hp : ∀ d ∈ D₁, Bal d → ∀ a v, Close (p a v d) (Pst a v d) (1 / 2)) :
    InPi μp D₁ p Yst where
  pa d hd hbal a v := by
    obtain ⟨h1, h2⟩ := h.Pst_bounds hμ (hD₁ hd) a v
    have := (h.basic (hD₁ hd)).2.2.1
    have := h.mu_le d (hD₁ hd)
    have h3 := (hp d hd hbal a v).le_of_nonneg (by linarith)
    have h4 := (hp d hd hbal a v).ge_of_nonneg (by linarith)
    exact ⟨by linarith, by linarith⟩
  pb d hd hbal a b hab := (h.inPi hμ hμp).pb d (hD₁ hd) hbal a b hab
  pc d hd hbal a v b _ := by
    obtain ⟨h1, h2⟩ := h.Yst_bounds hμ (hD₁ hd) a v b
    obtain ⟨h3, -⟩ := h.Pst_bounds hμ (hD₁ hd) b v
    have := (h.basic (hD₁ hd)).2.2.1
    have := h.mu_le d (hD₁ hd)
    have h4 := (hp d hd hbal b v).ge_of_nonneg (by linarith)
    exact ⟨le_trans (by positivity) h1, by nlinarith⟩

end StOK

end LW.Bip
