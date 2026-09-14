import MajorityDynamics.Literature.LWFormal.Bip.Eq29

set_option autoImplicit true

/-!
# Error bookkeeping for the bipartite assembly

Per-edge errors of `S`-steps, their sum along a walk of length `ℓ s̄^φ`, and the bound
`E3 ≤ 1/ω(n)` on the third term of `err11`.
-/

namespace LW.Bip

open Finset Real

/-- The (35) remainder for an `S`-step, with `s = 2 s̄^φ`, `Φ = n t̄^{2φ}`. -/
noncomputable def errH (φ : ℝ) (ℓ n m : ℕ) : ℝ :=
  1600 * ((m / ℓ : ℝ) ^ (2 * φ) * (n * (m / n : ℝ) ^ (2 * φ)) ^ 2 / m ^ 4 +
    (m / ℓ : ℝ) ^ φ * (n * (m / n : ℝ) ^ (2 * φ)) / (m ^ 2 * ℓ * n) +
    (m / ℓ : ℝ) ^ φ / (m * n))

/-- Bound for `err41` on `Q₁¹`. -/
noncomputable def errA (φ : ℝ) (ℓ n m : ℕ) : ℝ :=
  2 * (m / ℓ / n : ℝ) * min (m / ℓ : ℝ) (m / n) ^ (4 * φ - 4)

noncomputable def errS (φ : ℝ) (ℓ n m : ℕ) : ℝ := errA φ ℓ n m + errH φ ℓ n m

/-- The third term of `err11`. -/
noncomputable def E3 (φ : ℝ) (ℓ n m : ℕ) : ℝ :=
  min (m / ℓ : ℝ) (m / n) ^ (5 * φ - 5) * m ^ 2 / (ℓ * n)

theorem E3_swap (φ : ℝ) (ℓ n m : ℕ) : E3 φ n ℓ m = E3 φ ℓ n m := by
  simp only [E3, min_comm, mul_comm (n : ℝ)]

theorem err11_eq (φ : ℝ) (ℓ n m : ℕ) :
    err11 φ ℓ n m = log ℓ ^ 2 / √ℓ + log n ^ 2 / √n + E3 φ ℓ n m := rfl

theorem errH_nonneg (φ : ℝ) (ℓ n m : ℕ) : 0 ≤ errH φ ℓ n m := by unfold errH; positivity
theorem errA_nonneg (φ : ℝ) (ℓ n m : ℕ) : 0 ≤ errA φ ℓ n m := by unfold errA; positivity
theorem errS_nonneg (φ : ℝ) (ℓ n m : ℕ) : 0 ≤ errS φ ℓ n m :=
  add_nonneg (errA_nonneg _ _ _ _) (errH_nonneg _ _ _ _)
theorem E3_nonneg (φ : ℝ) (ℓ n m : ℕ) : 0 ≤ E3 φ ℓ n m := by unfold E3; positivity

/-- Quantitative consequences of `Sizes` used in the error bookkeeping. -/
theorem Sizes.bounds {ℓ n m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) :
    (40000 : ℝ) ≤ ℓ ∧ (40000 : ℝ) ≤ n ∧ (1 : ℝ) ≤ m ∧ 2000 * (m : ℝ) ≤ ℓ * n ∧
      (m / ℓ : ℝ) ≤ ℓ ^ 2 ∧ (m / n : ℝ) ≤ ℓ ∧ (m / ℓ : ℝ) ≤ n ∧
      log n ^ (4 : ℝ) ≤ m / ℓ ∧ log n ^ (4 : ℝ) / 16 ≤ m / n ∧ 35000 ≤ log n := by
  obtain ⟨-, -, hm, -, hD, hT, hlog⟩ := h.basic
  have hB := h.B_ge
  have hℓ := natCast_ge_of_log (by linarith) h.logℓ
  have hn := natCast_ge_of_log (by linarith) h.logn
  have hℓ' : (40000 : ℝ) ≤ ℓ := by nlinarith
  have hn' : (40000 : ℝ) ≤ n := by nlinarith
  have hℓn : (0 : ℝ) < ℓ * n := by positivity
  have hμ := h.mu_le
  rw [div_le_iff₀ hℓn] at hμ
  have h1 : (1 : ℝ) ≤ log n ^ (4 : ℝ) := one_le_rpow (by linarith) (by norm_num)
  have hm1 : (1 : ℝ) ≤ m := by
    have : (1 : ℝ) ≤ m / ℓ := h1.trans hD
    rw [le_div_iff₀ (by linarith)] at this; linarith
  refine ⟨hℓ', hn', hm1, by nlinarith, ?_, ?_, ?_, hD, hT, hlog⟩
  · rw [div_le_iff₀ (by linarith)]
    have := h.ℓn; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-- `x^e ≤ x^f` for `x ≥ 1`, `e ≤ f`. -/
theorem rpow_mono_exp {x e f : ℝ} (hx : 1 ≤ x) (h : e ≤ f) : x ^ e ≤ x ^ f :=
  rpow_le_rpow_of_exponent_le hx h

theorem rpow_eq_mul {x a b c : ℝ} (hx : 0 < x) (h : a = b + c) : x ^ a = x ^ b * x ^ c := by
  rw [h, rpow_add hx]

/-- `ℓ s̄^φ · errS ≤ 5000 E3`. -/
theorem walk_errS {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) {ℓ n m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) :
    (ℓ : ℝ) * (m / ℓ : ℝ) ^ φ * errS φ ℓ n m ≤ 5000 * E3 φ ℓ n m := by
  obtain ⟨hℓ, hn, hm, -, hDℓ, hTℓ, hDn, hD4, hT4, hlog⟩ := hS.bounds
  set D : ℝ := m / ℓ with hDdef
  set T : ℝ := m / n with hTdef
  set M : ℝ := min D T with hMdef
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hD1 : 1 ≤ D := (one_le_rpow (by linarith) (by norm_num)).trans hD4
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) ≤ log n ^ (4 : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num)]
      calc (1 : ℝ) * 16 ≤ 35000 ^ (4 : ℝ) := by
            rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
        _ ≤ log n ^ (4 : ℝ) := rpow_le_rpow (by norm_num) hlog (by norm_num)
    exact this.trans hT4
  have hM1 : 1 ≤ M := le_min hD1 hT1
  have hMD : M ≤ D := min_le_left _ _
  have hMT : M ≤ T := min_le_right _ _
  have hD0 : 0 < D := by linarith
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have hmD : (m : ℝ) = ℓ * D := by rw [hDdef]; field_simp
  have hmT : (m : ℝ) = n * T := by rw [hTdef]; field_simp
  have hDT : D * T = m ^ 2 / (ℓ * n) := by rw [hDdef, hTdef]; field_simp
  have hE3 : E3 φ ℓ n m = M ^ (5 * φ - 5) * (D * T) := by rw [E3, hDT]; ring
  -- (a) the `err41` part
  have ha : (ℓ : ℝ) * D ^ φ * errA φ ℓ n m ≤ 2 * E3 φ ℓ n m := by
    have h1 : D ^ (φ - 1) ≤ M ^ (φ - 1) := rpow_le_rpow_of_nonpos hM0 hMD (by linarith)
    have e1 : D ^ φ = D * D ^ (φ - 1) := by
      rw [rpow_eq_mul hD0 (show φ = 1 + (φ - 1) by ring), rpow_one]
    have e2 : M ^ (5 * φ - 5) = M ^ (φ - 1) * M ^ (4 * φ - 4) :=
      rpow_eq_mul hM0 (by ring)
    have hℓD : (ℓ : ℝ) * D / n = T := by rw [hTdef, hmD]
    rw [hE3, errA, e2, e1]
    have : (ℓ : ℝ) * (D * D ^ (φ - 1)) * (2 * (D / n) * M ^ (4 * φ - 4)) =
        2 * (D ^ (φ - 1) * M ^ (4 * φ - 4) * (ℓ * D / n) * D) := by ring
    rw [this, hℓD]
    have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ M ^ (4 * φ - 4) * T * D)
    nlinarith
  -- the three (35) terms, times `ℓ D^φ`
  have hDpos : 0 < D ^ φ := rpow_pos_of_pos hD0 _
  have hΦ : (n : ℝ) * T ^ (2 * φ) = m * T ^ (2 * φ - 1) := by
    rw [hmT, rpow_eq_mul hT0 (show 2 * φ = (2 * φ - 1) + 1 by ring), rpow_one]; ring
  -- (b)
  have hb : (ℓ : ℝ) * D ^ φ * (D ^ (2 * φ) * (n * T ^ (2 * φ)) ^ 2 / m ^ 4) ≤ E3 φ ℓ n m := by
    have hG : (D * T) ^ ((5 * φ - 5) / 2) ≤ M ^ (5 * φ - 5) := by
      have : M ^ (5 * φ - 5) = (M ^ 2) ^ ((5 * φ - 5) / 2) := by
        rw [← rpow_natCast, ← rpow_mul hM0.le]; congr 1; push_cast; ring
      rw [this]
      exact rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
    have e : (ℓ : ℝ) * D ^ φ * (D ^ (2 * φ) * (n * T ^ (2 * φ)) ^ 2 / m ^ 4) =
        (D * T) ^ ((5 * φ - 5) / 2) * (D * T) *
          (D ^ ((φ - 1) / 2) * T ^ ((3 * φ - 1) / 2) / ℓ) := by
      rw [hΦ, mul_rpow hD0.le hT0.le, hmD]
      have : (ℓ : ℝ) * D ^ φ * (D ^ (2 * φ) * (ℓ * D * T ^ (2 * φ - 1)) ^ 2 / (ℓ * D) ^ 4) =
          D ^ φ * D ^ (2 * φ) / D ^ 2 * (T ^ (2 * φ - 1)) ^ 2 / ℓ := by
        field_simp
      rw [this, ← rpow_natCast (T ^ (2 * φ - 1)), ← rpow_mul hT0.le, ← rpow_add hD0,
        ← rpow_natCast D 2, ← rpow_sub hD0]
      have e1 : D ^ (φ + 2 * φ - (2 : ℕ)) = D ^ ((5 * φ - 5) / 2) * D * D ^ ((φ - 1) / 2) := by
        rw [← rpow_add_one hD0.ne', ← rpow_add hD0]; push_cast; ring_nf
      have e2 : T ^ ((2 * φ - 1) * (2 : ℕ)) = T ^ ((5 * φ - 5) / 2) * T * T ^ ((3 * φ - 1) / 2) := by
        rw [← rpow_add_one hT0.ne', ← rpow_add hT0]; push_cast; ring_nf
      rw [e1, e2]; ring
    have h1 : D ^ ((φ - 1) / 2) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hD1 (by linarith)
    have h2 : T ^ ((3 * φ - 1) / 2) ≤ T := by
      have := rpow_mono_exp hT1 (show (3 * φ - 1) / 2 ≤ 1 by linarith)
      rwa [rpow_one] at this
    have h3 : D ^ ((φ - 1) / 2) * T ^ ((3 * φ - 1) / 2) / ℓ ≤ 1 := by
      rw [div_le_one hℓ0]
      calc D ^ ((φ - 1) / 2) * T ^ ((3 * φ - 1) / 2) ≤ 1 * T :=
            mul_le_mul h1 h2 (by positivity) zero_le_one
        _ ≤ ℓ := by linarith
    rw [e, hE3]
    have hG' := mul_le_mul_of_nonneg_right hG (by positivity : 0 ≤ D * T)
    calc (D * T) ^ ((5 * φ - 5) / 2) * (D * T) * (D ^ ((φ - 1) / 2) * T ^ ((3 * φ - 1) / 2) / ℓ)
        ≤ (D * T) ^ ((5 * φ - 5) / 2) * (D * T) * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ M ^ (5 * φ - 5) * (D * T) := by rw [mul_one]; exact hG'
  -- lower bound `E3 ≥ D^{5φ-4} T`
  have hE3D : D ^ (5 * φ - 5) * (D * T) ≤ E3 φ ℓ n m := by
    rw [hE3]
    exact mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos hM0 hMD (by linarith))
      (by positivity)
  have hDhalf : D ^ (2 - 3 * φ) ≤ ℓ := by
    calc D ^ (2 - 3 * φ) ≤ D ^ (1 / 2 : ℝ) := rpow_mono_exp hD1 (by linarith)
      _ ≤ ((ℓ : ℝ) ^ 2) ^ (1 / 2 : ℝ) := rpow_le_rpow hD0.le hDℓ (by norm_num)
      _ = ℓ := by
          rw [← rpow_natCast, ← rpow_mul hℓ0.le]; norm_num
  -- (c)
  have hc : (ℓ : ℝ) * D ^ φ * (D ^ φ * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n)) ≤ E3 φ ℓ n m := by
    refine le_trans ?_ hE3D
    have e : (ℓ : ℝ) * D ^ φ * (D ^ φ * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n)) =
        D ^ (5 * φ - 5) * (D * T) * (D ^ (3 - 3 * φ) * T ^ (2 * φ - 2) / (ℓ * n)) := by
      have h1 : (ℓ : ℝ) * D ^ φ * (D ^ φ * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n)) =
          D ^ (φ + φ - 1) * T ^ (2 * φ - 1) / (ℓ * n) := by
        rw [hΦ, hmD, rpow_sub hD0, rpow_add hD0, rpow_one]; field_simp
      have h2 : D ^ (5 * φ - 5) * (D * T) * (D ^ (3 - 3 * φ) * T ^ (2 * φ - 2) / (ℓ * n)) =
          D ^ (5 * φ - 5 + 1 + (3 - 3 * φ)) * T ^ (1 + (2 * φ - 2)) / (ℓ * n) := by
        rw [rpow_add hD0, rpow_add hD0, rpow_one, rpow_add hT0, rpow_one]; ring
      rw [h1, h2, show φ + φ - 1 = 5 * φ - 5 + 1 + (3 - 3 * φ) by ring,
        show 2 * φ - 1 = 1 + (2 * φ - 2) by ring]
    rw [e]
    have h1 : T ^ (2 * φ - 2) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hT1 (by linarith)
    have h2 : D ^ (3 - 3 * φ) ≤ n * ℓ := by
      calc D ^ (3 - 3 * φ) = D * D ^ (2 - 3 * φ) := by
            rw [rpow_eq_mul hD0 (show 3 - 3 * φ = 1 + (2 - 3 * φ) by ring), rpow_one]
        _ ≤ n * ℓ := mul_le_mul hDn hDhalf (by positivity) hn0.le
    have h3 : D ^ (3 - 3 * φ) * T ^ (2 * φ - 2) / (ℓ * n) ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc D ^ (3 - 3 * φ) * T ^ (2 * φ - 2) ≤ n * ℓ * 1 :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = ℓ * n := by ring
    calc D ^ (5 * φ - 5) * (D * T) * (D ^ (3 - 3 * φ) * T ^ (2 * φ - 2) / (ℓ * n))
        ≤ D ^ (5 * φ - 5) * (D * T) * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := mul_one _
  -- (d)
  have hd : (ℓ : ℝ) * D ^ φ * (D ^ φ / (m * n)) ≤ E3 φ ℓ n m := by
    refine le_trans ?_ hE3D
    have e : (ℓ : ℝ) * D ^ φ * (D ^ φ / (m * n)) =
        D ^ (5 * φ - 5) * (D * T) * (D ^ (2 - 3 * φ) / ℓ) := by
      have h1 : (ℓ : ℝ) * D ^ φ * (D ^ φ / (m * n)) = D ^ (φ + φ - 1) / n := by
        rw [rpow_sub hD0, rpow_add hD0, rpow_one, hmD]; field_simp
      have h2 : D ^ (5 * φ - 5) * (D * T) * (D ^ (2 - 3 * φ) / ℓ) =
          D ^ (5 * φ - 5 + 1 + (2 - 3 * φ) + 1) / n := by
        rw [rpow_add hD0, rpow_add hD0, rpow_add hD0, rpow_one, hTdef, hmD]; field_simp
      rw [h1, h2, show φ + φ - 1 = 5 * φ - 5 + 1 + (2 - 3 * φ) + 1 by ring]
    rw [e]
    have h3 : D ^ (2 - 3 * φ) / ℓ ≤ 1 := by rw [div_le_one hℓ0]; exact hDhalf
    calc D ^ (5 * φ - 5) * (D * T) * (D ^ (2 - 3 * φ) / ℓ)
        ≤ D ^ (5 * φ - 5) * (D * T) * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := mul_one _
  have hE0 := E3_nonneg φ ℓ n m
  have : (ℓ : ℝ) * D ^ φ * errS φ ℓ n m =
      ℓ * D ^ φ * errA φ ℓ n m +
        1600 * ((ℓ : ℝ) * D ^ φ * (D ^ (2 * φ) * (n * T ^ (2 * φ)) ^ 2 / m ^ 4) +
          ℓ * D ^ φ * (D ^ φ * (n * T ^ (2 * φ)) / (m ^ 2 * ℓ * n)) +
          ℓ * D ^ φ * (D ^ φ / (m * n))) := by
    rw [errS, errH]; ring
  rw [this]
  linarith

/-- `errS ≤ 5000 E3`. -/
theorem errS_le {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) {ℓ n m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) : errS φ ℓ n m ≤ 5000 * E3 φ ℓ n m := by
  obtain ⟨hℓ, -, -, -, -, -, -, hD4, -, hlog⟩ := hS.bounds
  have hD1 : (1 : ℝ) ≤ m / ℓ := (one_le_rpow (by linarith) (by norm_num)).trans hD4
  have h1 : (1 : ℝ) ≤ ℓ * (m / ℓ : ℝ) ^ φ :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_rpow hD1 (by linarith))
  calc errS φ ℓ n m = 1 * errS φ ℓ n m := (one_mul _).symm
    _ ≤ ℓ * (m / ℓ : ℝ) ^ φ * errS φ ℓ n m :=
        mul_le_mul_of_nonneg_right h1 (errS_nonneg _ _ _ _)
    _ ≤ _ := walk_errS hφ₁ hφ₂ hS

/-- `err41 ≤ errA` on `Q₁¹`. -/
theorem err41_le_errA {φ : ℝ} (hφ₂ : φ ≤ 1) {ℓ n m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {d : BSeq ℓ n} (hd : d ∈ Q1D φ ℓ n m) : err41 φ d ≤ errA φ ℓ n m := by
  obtain ⟨hℓ, hn, hm, -, -, -, -, hD4, hT4, hlog⟩ := hS.bounds
  obtain ⟨a₀, hd₀⟩ := hd
  have hM1 : M1 d.1 = m + 1 := by have := M1_sub_eS_fst d a₀; have := hd₀.2.2.1; omega
  have hM2 : M1 d.2 = m := by have := hd₀.2.2.2.1; rwa [sub_eS_snd] at this
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hdbar1 : dbar d.1 = (m + 1) / ℓ := by rw [dbar, hM1]; push_cast; ring
  have hdbar2 : dbar d.2 = m / n := by simp [dbar, hM2]
  have hmu : mu d = (2 * m + 1) / (2 * ℓ * n) := by rw [mu, hM1, hM2]; push_cast; ring
  have hD1 : (1 : ℝ) ≤ m / ℓ := (one_le_rpow (by linarith) (by norm_num)).trans hD4
  have hT0 : (0 : ℝ) < m / n := by positivity
  have hmin : min (m / ℓ : ℝ) (m / n) ≤ dmin d := by
    rw [dmin, hdbar1, hdbar2]
    exact min_le_min_right _ (by gcongr; linarith)
  have hmin0 : 0 < min (m / ℓ : ℝ) (m / n) := lt_min (by linarith) hT0
  rw [err41, errA, hmu]
  refine mul_le_mul ?_ (rpow_le_rpow_of_nonpos hmin0 hmin (by linarith))
    (rpow_nonneg (hmin0.le.trans hmin) _) (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have : (m : ℝ) / ℓ / n * (2 * ℓ * n) = 2 * m := by field_simp
  rw [mul_assoc, this]; linarith

/-- `E3 ≤ 1/ω(n)` from the `o(·)` hypothesis of Theorem 1.1. -/
theorem E3_le_inv_omega {φ : ℝ} (hφ₂ : φ < 3 / 5) {ω : ℕ → ℝ} {μ₀ : ℝ} {ℓ n m : ℕ}
    (hR : Range φ ω μ₀ ℓ n m) (hω : 0 < ω n) (hℓ : (1 : ℝ) ≤ ℓ) (hn : (1 : ℝ) ≤ n)
    (hm : (1 : ℝ) ≤ m) : E3 φ ℓ n m ≤ 1 / ω n := by
  obtain ⟨-, h, -⟩ := hR
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hs : (0 : ℝ) < ((ℓ : ℝ) + n) ^ (5 - 5 * φ) := rpow_pos_of_pos (by linarith) _
  -- `m^{5φ-3} ≤ ℓ n / (ω (ℓ+n)^{5-5φ})`
  have hmm : (m : ℝ) ^ (5 * φ - 3) * m ^ (3 - 5 * φ) = 1 := by
    rw [← rpow_add hm0]; norm_num
  have key : (m : ℝ) ^ (5 * φ - 3) * (ω n * (ℓ + n) ^ (5 - 5 * φ)) ≤ ℓ * n := by
    calc (m : ℝ) ^ (5 * φ - 3) * (ω n * (ℓ + n) ^ (5 - 5 * φ))
        ≤ (m : ℝ) ^ (5 * φ - 3) * (ℓ * n * m ^ (3 - 5 * φ)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ℓ * n := by rw [show (m : ℝ) ^ (5 * φ - 3) * (ℓ * n * m ^ (3 - 5 * φ)) =
            ℓ * n * (m ^ (5 * φ - 3) * m ^ (3 - 5 * φ)) by ring, hmm, mul_one]
  -- `E3 = m^{5φ-3} x^{5-5φ} / (ℓ n)` with `x = max(ℓ, n)`-side of the minimum
  have hcase : ∀ x : ℝ, 0 < x → x ≤ ℓ + n → (m / x) ^ (5 * φ - 5) * (m : ℝ) ^ 2 / (ℓ * n) ≤ 1 / ω n := by
    intro x hx hxs
    have e : (m / x) ^ (5 * φ - 5) * (m : ℝ) ^ 2 / (ℓ * n) =
        m ^ (5 * φ - 3) * x ^ (5 - 5 * φ) / (ℓ * n) := by
      have : x ^ (5 - 5 * φ) = (x ^ (5 * φ - 5))⁻¹ := by
        rw [← rpow_neg hx.le]; congr 1; ring
      rw [this, div_rpow hm0.le hx.le, ← rpow_natCast, div_mul_eq_mul_div, ← rpow_add hm0]
      push_cast
      rw [show 5 * φ - 5 + 2 = 5 * φ - 3 by ring]
      ring
    rw [e, div_le_div_iff₀ (by positivity) hω, one_mul]
    have hx' : x ^ (5 - 5 * φ) ≤ ((ℓ : ℝ) + n) ^ (5 - 5 * φ) :=
      rpow_le_rpow hx.le hxs (by linarith)
    calc (m : ℝ) ^ (5 * φ - 3) * x ^ (5 - 5 * φ) * ω n
        ≤ (m : ℝ) ^ (5 * φ - 3) * (ℓ + n) ^ (5 - 5 * φ) * ω n := by gcongr
      _ = (m : ℝ) ^ (5 * φ - 3) * (ω n * (ℓ + n) ^ (5 - 5 * φ)) := by ring
      _ ≤ ℓ * n := key
  unfold E3
  rcases le_total (m / ℓ : ℝ) (m / n) with hle | hle
  · rw [min_eq_left hle]; exact hcase ℓ hℓ0 (by linarith)
  · rw [min_eq_right hle]; exact hcase n hn0 (by linarith)

end LW.Bip
