import MajorityDynamics.Literature.LWFormal.Bip.Claim42
import MajorityDynamics.Literature.LWFormal.Nbhd
import MajorityDynamics.Literature.LWFormal.Bip.GaleRyser

set_option autoImplicit true

/-!
# Bipartite: the `L¹`-neighbourhood of a balanced near-regular sequence satisfies Claim 4.2
-/

namespace LW.Bip

open Finset Real

variable {ℓ n : ℕ}

/-- The `L¹`-ball of radius `r` around `d₀`. -/
def Ball (d₀ : BSeq ℓ n) (r : ℕ) : Set (BSeq ℓ n) := {d | dist1 d₀ d ≤ r}

theorem Ball_self (d₀ : BSeq ℓ n) {r : ℕ} : d₀ ∈ Ball d₀ r :=
  show dist1 d₀ d₀ ≤ r by rw [dist1_self]; positivity

theorem mem_Omega_Ball {d₀ d : BSeq ℓ n} {r s : ℕ} (h : dist1 d₀ d + s ≤ r) :
    d ∈ Omega (Ball d₀ r) s :=
  ⟨show dist1 d₀ d ≤ r by linarith [(Int.natCast_nonneg s)],
    fun d' hd' => show dist1 d₀ d' ≤ r by linarith [dist1_triangle d₀ d d']⟩

theorem dist1_nonneg' {k : ℕ} (d d' : Seq k) : 0 ≤ LW.dist1 d d' :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem dist1_fst_le (d d' : BSeq ℓ n) : LW.dist1 d.1 d'.1 ≤ dist1 d d' := by
  unfold dist1; linarith [dist1_nonneg' d.2 d'.2]

theorem dist1_snd_le (d d' : BSeq ℓ n) : LW.dist1 d.2 d'.2 ≤ dist1 d d' := by
  unfold dist1; linarith [dist1_nonneg' d.1 d'.1]

/-- Hypotheses on the centre `d₀` and radius `r` of the neighbourhood used for Claim 4.2. -/
structure Nbhd (φ : ℝ) (d₀ : BSeq ℓ n) (r : ℕ) (D₀ : ℝ) : Prop where
  φ₁ : 1 / 2 ≤ φ
  φ₂ : φ < 3 / 5
  ℓ48 : 48 ≤ ℓ
  n48 : 48 ≤ n
  bal : Bal d₀
  spreadS : ∀ a, |(d₀.1 a : ℝ) - dbar d₀.1| ≤ dbar d₀.1 ^ φ
  spreadT : ∀ v, |(d₀.2 v : ℝ) - dbar d₀.2| ≤ dbar d₀.2 ^ φ
  dmin_ge : 35000 ≤ dmin d₀
  D₀_le : D₀ ≤ 63 / 64 * dmin d₀
  r_le : 4 * r ≤ dmin d₀ ^ φ
  mu_le : mu d₀ ≤ 1 / (2 * 10 ^ 9)

theorem mu_eq_S_of_bal {d : BSeq ℓ n} (h : Bal d) (hℓ : (ℓ : ℝ) ≠ 0) (hn : (n : ℝ) ≠ 0) :
    mu d = dbar d.1 / n := by
  have : (M1 d.1 : ℝ) = M1 d.2 := by exact_mod_cast h
  unfold mu dbar; rw [← this]; field_simp; ring

theorem mu_eq_T_of_bal {d : BSeq ℓ n} (h : Bal d) (hℓ : (ℓ : ℝ) ≠ 0) (hn : (n : ℝ) ≠ 0) :
    mu d = dbar d.2 / ℓ := by
  have : (M1 d.1 : ℝ) = M1 d.2 := by exact_mod_cast h
  unfold mu dbar; rw [this]; field_simp; ring

namespace Nbhd

variable {φ D₀ : ℝ} {d₀ : BSeq ℓ n} {r : ℕ} (h : Nbhd φ d₀ r D₀)
include h

theorem ℓ_ge : (48 : ℝ) ≤ ℓ := by exact_mod_cast h.ℓ48
theorem n_ge : (48 : ℝ) ≤ n := by exact_mod_cast h.n48

theorem S_ge : 35000 ≤ dbar d₀.1 := le_trans h.dmin_ge (min_le_left _ _)
theorem T_ge : 35000 ≤ dbar d₀.2 := le_trans h.dmin_ge (min_le_right _ _)
theorem S_pos : 0 < dbar d₀.1 := by linarith [h.S_ge]
theorem T_pos : 0 < dbar d₀.2 := by linarith [h.T_ge]
theorem dmin_pos : 0 < dmin d₀ := by linarith [h.dmin_ge]

theorem mu_S : mu d₀ = dbar d₀.1 / n :=
  mu_eq_S_of_bal h.bal (by linarith [h.ℓ_ge]) (by linarith [h.n_ge])
theorem mu_T : mu d₀ = dbar d₀.2 / ℓ :=
  mu_eq_T_of_bal h.bal (by linarith [h.ℓ_ge]) (by linarith [h.n_ge])

theorem mu_pos : 0 < mu d₀ := by
  rw [h.mu_S]; exact div_pos h.S_pos (by linarith [h.n_ge])

theorem rpow_le : dmin d₀ ^ φ ≤ dmin d₀ / 16 := by
  have hD := h.dmin_pos
  have h1 : dmin d₀ ^ φ ≤ dmin d₀ ^ (3 / 5 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith [h.dmin_ge]) h.φ₂.le
  have h2 : (16 : ℝ) ≤ dmin d₀ ^ (2 / 5 : ℝ) :=
    rpow_1024 ▸ rpow_le_rpow (by norm_num) (by linarith [h.dmin_ge]) (by norm_num)
  have h3 : dmin d₀ ^ (3 / 5 : ℝ) * dmin d₀ ^ (2 / 5 : ℝ) = dmin d₀ := by
    rw [← rpow_add hD]; norm_num
  have h4 : 0 ≤ dmin d₀ ^ (3 / 5 : ℝ) := by positivity
  nlinarith

theorem r_le' : (r : ℝ) ≤ dmin d₀ / 64 := by linarith [h.r_le, h.rpow_le]

theorem S_rpow_le : dbar d₀.1 ^ φ ≤ dbar d₀.1 / 16 := by
  have hD := h.S_pos
  have h1 : dbar d₀.1 ^ φ ≤ dbar d₀.1 ^ (3 / 5 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith [h.S_ge]) h.φ₂.le
  have h2 : (16 : ℝ) ≤ dbar d₀.1 ^ (2 / 5 : ℝ) :=
    rpow_1024 ▸ rpow_le_rpow (by norm_num) (by linarith [h.S_ge]) (by norm_num)
  have h3 : dbar d₀.1 ^ (3 / 5 : ℝ) * dbar d₀.1 ^ (2 / 5 : ℝ) = dbar d₀.1 := by
    rw [← rpow_add hD]; norm_num
  have h4 : 0 ≤ dbar d₀.1 ^ (3 / 5 : ℝ) := by positivity
  nlinarith

theorem T_rpow_le : dbar d₀.2 ^ φ ≤ dbar d₀.2 / 16 := by
  have hD := h.T_pos
  have h1 : dbar d₀.2 ^ φ ≤ dbar d₀.2 ^ (3 / 5 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith [h.T_ge]) h.φ₂.le
  have h2 : (16 : ℝ) ≤ dbar d₀.2 ^ (2 / 5 : ℝ) :=
    rpow_1024 ▸ rpow_le_rpow (by norm_num) (by linarith [h.T_ge]) (by norm_num)
  have h3 : dbar d₀.2 ^ (3 / 5 : ℝ) * dbar d₀.2 ^ (2 / 5 : ℝ) = dbar d₀.2 := by
    rw [← rpow_add hD]; norm_num
  have h4 : 0 ≤ dbar d₀.2 ^ (3 / 5 : ℝ) := by positivity
  nlinarith

theorem S_bound : dbar d₀.1 ≤ n / (2 * 10 ^ 9) := by
  have := h.mu_le; rw [h.mu_S, div_le_iff₀ (by linarith [h.n_ge])] at this; linarith

theorem T_bound : dbar d₀.2 ≤ ℓ / (2 * 10 ^ 9) := by
  have := h.mu_le; rw [h.mu_T, div_le_iff₀ (by linarith [h.ℓ_ge])] at this; linarith

section ball

variable {d : BSeq ℓ n} (hd : d ∈ Ball d₀ r)
include hd

omit h in
theorem dist_le : (dist1 d₀ d : ℝ) ≤ r := by exact_mod_cast hd

theorem S_close : |dbar d.1 - dbar d₀.1| ≤ r := by
  have hℓ := h.ℓ_ge
  rw [abs_sub_comm]
  calc |dbar d₀.1 - dbar d.1| ≤ LW.dist1 d₀.1 d.1 / ℓ := abs_dbar_sub_le (by linarith) _ _
    _ ≤ r / ℓ := by
        gcongr
        exact_mod_cast (dist1_fst_le d₀ d).trans hd
    _ ≤ r := div_le_self (by positivity) (by linarith)

theorem T_close : |dbar d.2 - dbar d₀.2| ≤ r := by
  have hn := h.n_ge
  rw [abs_sub_comm]
  calc |dbar d₀.2 - dbar d.2| ≤ LW.dist1 d₀.2 d.2 / n := abs_dbar_sub_le (by linarith) _ _
    _ ≤ r / n := by
        gcongr
        exact_mod_cast (dist1_snd_le d₀ d).trans hd
    _ ≤ r := div_le_self (by positivity) (by linarith)

theorem S_bounds : 63 / 64 * dbar d₀.1 ≤ dbar d.1 ∧ dbar d.1 ≤ 65 / 64 * dbar d₀.1 := by
  have := abs_le.1 (h.S_close hd); have := h.r_le'
  have := min_le_left (dbar d₀.1) (dbar d₀.2)
  unfold dmin at *; constructor <;> linarith

theorem T_bounds : 63 / 64 * dbar d₀.2 ≤ dbar d.2 ∧ dbar d.2 ≤ 65 / 64 * dbar d₀.2 := by
  have := abs_le.1 (h.T_close hd); have := h.r_le'
  have := min_le_right (dbar d₀.1) (dbar d₀.2)
  unfold dmin at *; constructor <;> linarith

theorem dmin_bounds : 63 / 64 * dmin d₀ ≤ dmin d ∧ dmin d ≤ 65 / 64 * dmin d₀ := by
  obtain ⟨hS1, hS2⟩ := h.S_bounds hd
  obtain ⟨hT1, hT2⟩ := h.T_bounds hd
  unfold dmin
  refine ⟨le_min ?_ ?_, ?_⟩
  · linarith [min_le_left (dbar d₀.1) (dbar d₀.2)]
  · linarith [min_le_right (dbar d₀.1) (dbar d₀.2)]
  · rcases min_choice (dbar d₀.1) (dbar d₀.2) with h0 | h0 <;> rw [h0]
    · linarith [min_le_left (dbar d.1) (dbar d.2)]
    · linarith [min_le_right (dbar d.1) (dbar d.2)]

theorem devS (a : Fin ℓ) : |(d.1 a : ℝ) - dbar d.1| ≤ 3 / 2 * dbar d₀.1 ^ φ := by
  have h1 : |(d.1 a : ℝ) - d₀.1 a| ≤ r := by
    rw [abs_sub_comm]
    have := (abs_sub_le_dist1 d₀.1 d.1 a).trans ((dist1_fst_le d₀ d).trans hd)
    exact_mod_cast this
  have h2 := h.spreadS a
  have h3 := h.S_close hd
  have h4 := h.r_le
  have h5 : dmin d₀ ^ φ ≤ dbar d₀.1 ^ φ :=
    rpow_le_rpow h.dmin_pos.le (min_le_left _ _) (by linarith [h.φ₁])
  calc |(d.1 a : ℝ) - dbar d.1|
      = |((d.1 a : ℝ) - d₀.1 a) + ((d₀.1 a : ℝ) - dbar d₀.1) + (dbar d₀.1 - dbar d.1)| := by
        ring_nf
    _ ≤ |(d.1 a : ℝ) - d₀.1 a| + |(d₀.1 a : ℝ) - dbar d₀.1| + |dbar d₀.1 - dbar d.1| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ 3 / 2 * dbar d₀.1 ^ φ := by rw [abs_sub_comm (dbar d₀.1)]; linarith

theorem devT (v : Fin n) : |(d.2 v : ℝ) - dbar d.2| ≤ 3 / 2 * dbar d₀.2 ^ φ := by
  have h1 : |(d.2 v : ℝ) - d₀.2 v| ≤ r := by
    rw [abs_sub_comm]
    have := (abs_sub_le_dist1 d₀.2 d.2 v).trans ((dist1_snd_le d₀ d).trans hd)
    exact_mod_cast this
  have h2 := h.spreadT v
  have h3 := h.T_close hd
  have h4 := h.r_le
  have h5 : dmin d₀ ^ φ ≤ dbar d₀.2 ^ φ :=
    rpow_le_rpow h.dmin_pos.le (min_le_right _ _) (by linarith [h.φ₁])
  calc |(d.2 v : ℝ) - dbar d.2|
      = |((d.2 v : ℝ) - d₀.2 v) + ((d₀.2 v : ℝ) - dbar d₀.2) + (dbar d₀.2 - dbar d.2)| := by
        ring_nf
    _ ≤ |(d.2 v : ℝ) - d₀.2 v| + |(d₀.2 v : ℝ) - dbar d₀.2| + |dbar d₀.2 - dbar d.2| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ 3 / 2 * dbar d₀.2 ^ φ := by rw [abs_sub_comm (dbar d₀.2)]; linarith

theorem devS' (a : Fin ℓ) : |(d.1 a : ℝ) - dbar d.1| ≤ 3 / 32 * dbar d₀.1 := by
  linarith [h.devS hd a, h.S_rpow_le]

theorem devT' (v : Fin n) : |(d.2 v : ℝ) - dbar d.2| ≤ 3 / 32 * dbar d₀.2 := by
  linarith [h.devT hd v, h.T_rpow_le]

theorem two_le (a : Fin ℓ) : 2 ≤ d.1 a := by
  have h1 := (abs_le.1 (h.devS' hd a)).1
  have h2 := (h.S_bounds hd).1
  have h3 := h.S_ge
  exact_mod_cast (by linarith : (2 : ℝ) ≤ d.1 a)

theorem two_le_T (v : Fin n) : 2 ≤ d.2 v := by
  have h1 := (abs_le.1 (h.devT' hd v)).1
  have h2 := (h.T_bounds hd).1
  have h3 := h.T_ge
  exact_mod_cast (by linarith : (2 : ℝ) ≤ d.2 v)

theorem nonneg' (a : Fin ℓ) : 0 ≤ d.1 a := by linarith [h.two_le hd a]
theorem nonneg_T' (v : Fin n) : 0 ≤ d.2 v := by linarith [h.two_le_T hd v]

omit hd in
theorem mu_eq : mu d = (ℓ * dbar d.1 + n * dbar d.2) / (2 * ℓ * n) := by
  have hℓ := h.ℓ_ge; have hn := h.n_ge
  unfold mu dbar; field_simp

theorem mu_le' : mu d ≤ 65 / 64 * mu d₀ := by
  have hℓ := h.ℓ_ge; have hn := h.n_ge
  rw [h.mu_eq (d := d), h.mu_eq (d := d₀), ← mul_div_assoc,
    div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [(h.S_bounds hd).2, (h.T_bounds hd).2]

theorem mu_ge' : mu d₀ ≤ 64 / 63 * mu d := by
  have hℓ := h.ℓ_ge; have hn := h.n_ge
  rw [h.mu_eq (d := d), h.mu_eq (d := d₀), ← mul_div_assoc,
    div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [(h.S_bounds hd).1, (h.T_bounds hd).1]

theorem mu_le2 : mu d ≤ 2 * mu d₀ := by linarith [h.mu_le' hd, h.mu_pos]

theorem spread' : Spread φ d := by
  refine ⟨by linarith [h.mu_le2 hd, h.mu_le], fun a => ?_, fun v => ?_⟩
  · have hD := h.S_pos
    have h1 : (63 / 64 * dbar d₀.1) ^ φ ≤ dbar d.1 ^ φ :=
      rpow_le_rpow (by positivity) (h.S_bounds hd).1 (by linarith [h.φ₁])
    rw [mul_rpow (by norm_num) hD.le] at h1
    have h2 : (63 / 64 : ℝ) ^ (1 : ℝ) ≤ (63 / 64) ^ φ :=
      rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [h.φ₂])
    rw [rpow_one] at h2
    have h3 : 0 ≤ dbar d₀.1 ^ φ := by positivity
    nlinarith [h.devS hd a]
  · have hD := h.T_pos
    have h1 : (63 / 64 * dbar d₀.2) ^ φ ≤ dbar d.2 ^ φ :=
      rpow_le_rpow (by positivity) (h.T_bounds hd).1 (by linarith [h.φ₁])
    rw [mul_rpow (by norm_num) hD.le] at h1
    have h2 : (63 / 64 : ℝ) ^ (1 : ℝ) ≤ (63 / 64) ^ φ :=
      rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [h.φ₂])
    rw [rpow_one] at h2
    have h3 : 0 ≤ dbar d₀.2 ^ φ := by positivity
    nlinarith [h.devT hd v]

theorem dmin_ge' : 32768 ≤ dmin d ∧ D₀ ≤ dmin d := by
  have := (h.dmin_bounds hd).1
  exact ⟨by linarith [h.dmin_ge], by linarith [h.D₀_le]⟩

/-- Realizability of balanced sequences in the ball (Gale–Ryser). -/
theorem N_pos (hbal : Bal d) : 0 < N d := by
  have hℓ := h.ℓ_ge
  have hS := h.S_ge
  have hT := h.T_ge
  have hTℓ := h.T_bound
  obtain ⟨hS1, hS2⟩ := h.S_bounds hd
  obtain ⟨hT1, hT2⟩ := h.T_bounds hd
  set S := dbar d₀.1
  set T := dbar d₀.2
  have hδ : (⌊7 / 8 * S⌋₊ : ℝ) ≤ 7 / 8 * S := Nat.floor_le (by positivity)
  have hδ' : 7 / 8 * S - 1 ≤ (⌊7 / 8 * S⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one (7 / 8 * S)]
  have hΔ : 9 / 8 * S ≤ (⌈9 / 8 * S⌉₊ : ℝ) := Nat.le_ceil _
  have hΔ' : (⌈9 / 8 * S⌉₊ : ℝ) ≤ 9 / 8 * S + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hΓ : 9 / 8 * T ≤ (⌈9 / 8 * T⌉₊ : ℝ) := Nat.le_ceil _
  have hΓ' : (⌈9 / 8 * T⌉₊ : ℝ) ≤ 9 / 8 * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  refine N_pos_of_near_regular d hbal (δ := ⌊7 / 8 * S⌋₊) (Δ := ⌈9 / 8 * S⌉₊)
    (Δ' := ⌈9 / 8 * T⌉₊) (fun a => ?_) (fun a => ?_) (h.nonneg_T' hd) (fun v => ?_) ?_ ?_
  · have := (abs_le.1 (h.devS' hd a)).1
    exact_mod_cast (by linarith : ((⌊7 / 8 * S⌋₊ : ℕ) : ℝ) ≤ d.1 a)
  · have := (abs_le.1 (h.devS' hd a)).2
    exact_mod_cast (by linarith : (d.1 a : ℝ) ≤ ((⌈9 / 8 * S⌉₊ : ℕ) : ℝ))
  · have := (abs_le.1 (h.devT' hd v)).2
    exact_mod_cast (by linarith : (d.2 v : ℝ) ≤ ((⌈9 / 8 * T⌉₊ : ℕ) : ℝ))
  · exact_mod_cast (by linarith : ((⌈9 / 8 * T⌉₊ : ℕ) : ℝ) ≤ ℓ)
  · have h1 : ((⌈9 / 8 * S⌉₊ : ℕ) : ℝ) * ⌈9 / 8 * T⌉₊ ≤ (9 / 8 * S + 1) * (9 / 8 * T + 1) :=
      mul_le_mul hΔ' hΓ' (by positivity) (by positivity)
    have h2 : (9 / 8 * S + 1) * (9 / 8 * T + 1) ≤ 2 * S * T := by nlinarith
    have h3 : 2 * S * T ≤ (ℓ : ℝ) * (7 / 8 * S - 1) := by nlinarith
    have h4 : (ℓ : ℝ) * (7 / 8 * S - 1) ≤ ℓ * ⌊7 / 8 * S⌋₊ := by gcongr
    exact_mod_cast (by linarith : ((⌈9 / 8 * S⌉₊ : ℕ) : ℝ) * ⌈9 / 8 * T⌉₊ ≤ ℓ * ⌊7 / 8 * S⌋₊)

theorem DeltaS_le : (DeltaS d : ℝ) ≤ 11 / 10 * dbar d.1 := by
  obtain ⟨a₀, -, ha₀⟩ := exists_mem_eq_sup (univ : Finset (Fin ℓ))
    ⟨⟨0, by have := h.ℓ48; omega⟩, mem_univ _⟩ fun a => (d.1 a).toNat
  have : (DeltaS d : ℝ) = d.1 a₀ := by
    unfold DeltaS; rw [ha₀]; exact_mod_cast Int.toNat_of_nonneg (h.nonneg' hd a₀)
  rw [this]
  linarith [(abs_le.1 (h.devS' hd a₀)).2, (h.S_bounds hd).1]

theorem DeltaT_le : (DeltaT d : ℝ) ≤ 11 / 10 * dbar d.2 := by
  obtain ⟨v₀, -, hv₀⟩ := exists_mem_eq_sup (univ : Finset (Fin n))
    ⟨⟨0, by have := h.n48; omega⟩, mem_univ _⟩ fun v => (d.2 v).toNat
  have : (DeltaT d : ℝ) = d.2 v₀ := by
    unfold DeltaT; rw [hv₀]; exact_mod_cast Int.toNat_of_nonneg (h.nonneg_T' hd v₀)
  rw [this]
  linarith [(abs_le.1 (h.devT' hd v₀)).2, (h.T_bounds hd).1]

/-- `P_{av}(d) ≤ 2μ(d)` on balanced sequences of the ball (Lemma 2.3). -/
theorem P_le (hbal : Bal d) (a : Fin ℓ) (v : Fin n) : P a v d ≤ 2 * mu d := by
  have hℓ := h.ℓ_ge
  have hn := h.n_ge
  have hS0 : 0 < dbar d.1 := by linarith [(h.S_bounds hd).1, h.S_ge]
  have hT0 : 0 < dbar d.2 := by linarith [(h.T_bounds hd).1, h.T_ge]
  have hTℓ : dbar d.2 ≤ ℓ / 10 ^ 9 := by linarith [h.T_bound, (h.T_bounds hd).2]
  have hΔS := h.DeltaS_le hd
  have hΔT := h.DeltaT_le hd
  have hΔS0 : (0 : ℝ) ≤ DeltaS d := by positivity
  have hΔT0 : (0 : ℝ) ≤ DeltaT d := by positivity
  have hM : (M1 d.1 : ℝ) = ℓ * dbar d.1 := by unfold dbar; field_simp
  have hμ : mu d = dbar d.2 / ℓ := mu_eq_T_of_bal hbal (by linarith) (by linarith)
  have hX : (DeltaS d * DeltaT d : ℝ) ≤ 121 / 100 * (dbar d.1 * dbar d.2) := by
    nlinarith [mul_le_mul hΔS hΔT hΔT0 (by positivity)]
  have hTS : dbar d.2 * dbar d.1 ≤ ℓ / 10 ^ 9 * dbar d.1 := by gcongr
  have hlt : 3 * (DeltaS d * DeltaT d : ℝ) < M1 d.1 := by rw [hM]; nlinarith
  refine (lemma_2_3 d hlt a v).trans ?_
  rw [hμ, hM, div_le_iff₀ (by linarith)]
  have hX' : (DeltaS d * DeltaT d : ℝ) * (1 + 6 * dbar d.2 / ℓ) ≤
      121 / 100 * (dbar d.1 * dbar d.2) * (1 + 6 * dbar d.2 / ℓ) := by gcongr
  have h6 : 6 * dbar d.2 / ℓ ≤ 6 / 10 ^ 9 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hST : 0 ≤ dbar d.1 * dbar d.2 := by positivity
  have hgoal : (DeltaS d * DeltaT d : ℝ) * (1 + 6 * dbar d.2 / ℓ) ≤ 2 * (dbar d.2 * dbar d.1) := by
    nlinarith
  have hexp : 2 * (dbar d.2 / ℓ) * (ℓ * dbar d.1 - 3 * (DeltaS d * DeltaT d : ℝ)) =
      2 * (dbar d.2 * dbar d.1) - (DeltaS d * DeltaT d : ℝ) * (6 * dbar d.2 / ℓ) := by
    field_simp; ring
  rw [hexp]; linarith

theorem err41_le : err41 φ d ≤ 4 * err41 φ d₀ := by
  have hD := h.dmin_pos
  have hB := h.dmin_bounds hd
  have hB0 : 0 < dmin d := by linarith
  have h1 : dmin d ^ (4 * φ - 4) ≤ (64 / 63) ^ 2 * dmin d₀ ^ (4 * φ - 4) :=
    rpow_le_of_le hD hB0 (by norm_num) (by linarith) (by linarith [h.φ₁]) (by linarith [h.φ₂])
  have h2 : 0 ≤ dmin d₀ ^ (4 * φ - 4) := by positivity
  have h3 := h.mu_le2 hd
  have h4 := h.mu_pos
  unfold err41
  calc mu d * dmin d ^ (4 * φ - 4) ≤ 2 * mu d₀ * ((64 / 63) ^ 2 * dmin d₀ ^ (4 * φ - 4)) :=
        mul_le_mul h3 h1 (by positivity) (by positivity)
    _ ≤ 4 * (mu d₀ * dmin d₀ ^ (4 * φ - 4)) := by nlinarith

theorem err41_ge : err41 φ d₀ ≤ 4 * err41 φ d := by
  have hD := h.dmin_pos
  have hB := h.dmin_bounds hd
  have hB0 : 0 < dmin d := by linarith
  have h1 : dmin d₀ ^ (4 * φ - 4) ≤ (65 / 64) ^ 2 * dmin d ^ (4 * φ - 4) :=
    rpow_le_of_le hB0 hD (by norm_num) (by linarith) (by linarith [h.φ₁]) (by linarith [h.φ₂])
  have h2 : 0 ≤ dmin d ^ (4 * φ - 4) := by positivity
  have h3 := h.mu_ge' hd
  have h4 := h.mu_pos
  have h5 : 0 < mu d := by linarith
  unfold err41
  calc mu d₀ * dmin d₀ ^ (4 * φ - 4) ≤ 64 / 63 * mu d * ((65 / 64) ^ 2 * dmin d ^ (4 * φ - 4)) :=
        mul_le_mul h3 h1 (by positivity) (by positivity)
    _ ≤ 4 * (mu d * dmin d ^ (4 * φ - 4)) := by nlinarith

theorem err41_pos : 0 < err41 φ d := by
  have := h.mu_pos; have := h.err41_ge hd
  have : 0 < err41 φ d₀ := by unfold err41; exact mul_pos h.mu_pos (rpow_pos_of_pos h.dmin_pos _)
  linarith

end ball

theorem exactOK : ExactOK (2 * mu d₀) (Ball d₀ r) where
  two_le _ hd := h.two_le hd
  mu_le _ hd := h.mu_le2 hd
  N_pos _ hd hbal := h.N_pos hd hbal
  P_le _ hd hbal a v := h.P_le hd hbal a v

theorem stOK : StOK φ (2 * mu d₀) (Ball d₀ r) where
  φ₁ := h.φ₁
  φ₂ := h.φ₂
  ℓ2 := by have := h.ℓ48; omega
  n2 := by have := h.n48; omega
  spread _ hd := h.spread' hd
  dmin_ge _ hd := (h.dmin_ge' hd).1
  mu_le _ hd := h.mu_le2 hd

/-- Claim 4.2's hypotheses hold on the ball, with `ε = 4C·err41(d₀)`, given Lemma 4.1. -/
theorem ok {C : ℝ} (hC : 0 ≤ C)
    (h41a : ∀ d ∈ Ball d₀ r, SH d → ∀ a b, Close (opR Pst Yst a b d) (Rst a b d) (C * err41 φ d))
    (h41b : ∀ d ∈ Ball d₀ r, Bal d → ∀ a v, Close (opP Pst Rst a v d) (Pst a v d) (C * err41 φ d))
    (h41c : ∀ d ∈ Ball d₀ r, Bal d → ∀ a v b, a ≠ b →
      Close (opY Pst Yst a v b d) (Yst a v b d) (C * err41 φ d))
    (hε0 : 0 < 4 * C * err41 φ d₀) (hε1 : 4 * C * err41 φ d₀ ≤ 1 / 1000) :
    OK φ (2 * mu d₀) (4 * C * err41 φ d₀) (Ball d₀ r) where
  ex := h.exactOK
  st := h.stOK
  μ_pos := by linarith [h.mu_pos]
  μ_le := by linarith [h.mu_le]
  ε_pos := hε0
  ε_le := hε1
  a d hd hSH a b := (h41a d hd hSH a b).mono (by nlinarith [h.err41_le hd])
  b d hd hbal a v := (h41b d hd hbal a v).mono (by nlinarith [h.err41_le hd])
  c d hd hbal a v b hab := (h41c d hd hbal a v b hab).mono (by nlinarith [h.err41_le hd])

end Nbhd

end LW.Bip
