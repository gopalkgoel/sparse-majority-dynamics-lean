import MajorityDynamics.Literature.LWFormal.Claim64

set_option autoImplicit true

/-!
# The `L¹`-neighbourhood of a sequence in `𝔇` satisfies the hypotheses of Claim 6.4
-/

namespace LW

open Finset Real

variable {n : ℕ}

/-- The `L¹`-ball of radius `r` around `d₀`. -/
def Ball (d₀ : Seq n) (r : ℕ) : Set (Seq n) := {d | dist1 d₀ d ≤ r}

theorem dist1_self (d : Seq n) : dist1 d d = 0 := by simp [dist1]

theorem Ball_self (d₀ : Seq n) {r : ℕ} : d₀ ∈ Ball d₀ r :=
  show dist1 d₀ d₀ ≤ r by rw [dist1_self]; positivity

theorem mem_Omega_Ball {d₀ d : Seq n} {r s : ℕ} (h : dist1 d₀ d + s ≤ r) :
    d ∈ Omega (Ball d₀ r) s :=
  ⟨show dist1 d₀ d ≤ r by linarith [(Int.natCast_nonneg s)],
    fun d' hd' => show dist1 d₀ d' ≤ r by linarith [dist1_triangle d₀ d d']⟩

theorem abs_sub_le_dist1 (d d' : Seq n) (i : Fin n) : |d i - d' i| ≤ dist1 d d' :=
  single_le_sum (f := fun i => |d i - d' i|) (fun _ _ => abs_nonneg _) (mem_univ i)

theorem abs_M1_sub_le (d d' : Seq n) : |M1 d - M1 d'| ≤ dist1 d d' := by
  unfold M1 dist1; rw [← sum_sub_distrib]; exact abs_sum_le_sum_abs _ _

theorem abs_dbar_sub_le (hn : (0 : ℝ) < n) (d d' : Seq n) :
    |dbar d - dbar d'| ≤ dist1 d d' / n := by
  unfold dbar
  rw [← sub_div, abs_div, abs_of_pos hn]
  gcongr
  exact_mod_cast abs_M1_sub_le d d'

theorem rpow_le_of_le {x y c β : ℝ} (hx : 0 < x) (hy : 0 < y) (hc : 1 ≤ c) (hxy : x ≤ c * y)
    (hβ : -2 ≤ β) (hβ0 : β ≤ 0) : y ^ β ≤ c ^ 2 * x ^ β := by
  have h1 : (c * y) ^ β ≤ x ^ β := rpow_le_rpow_of_nonpos hx hxy hβ0
  rw [mul_rpow (by linarith) hy.le] at h1
  have h2 : c ^ (-2 : ℝ) ≤ c ^ β := rpow_le_rpow_of_exponent_le hc hβ
  rw [rpow_neg (by linarith), rpow_two] at h2
  have hc2 : 0 < c ^ 2 := by positivity
  have hyβ : 0 < y ^ β := rpow_pos_of_pos hy β
  calc y ^ β = c ^ 2 * ((c ^ 2)⁻¹ * y ^ β) := by field_simp
    _ ≤ c ^ 2 * (c ^ β * y ^ β) := by gcongr
    _ ≤ c ^ 2 * x ^ β := by gcongr

theorem rpow_1024 : (1024 : ℝ) ^ (2 / 5 : ℝ) = 16 := by
  rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, ← rpow_natCast, ← rpow_mul (by norm_num)]
  norm_num

/-- Hypotheses on the centre `d₀` and radius `r` of the neighbourhood used for Claim 6.4. -/
structure Nbhd (α : ℝ) (d₀ : Seq n) (r : ℕ) (D₀ : ℝ) : Prop where
  α₁ : 1 / 2 ≤ α
  α₂ : α < 3 / 5
  n48 : 48 ≤ n
  nonneg : ∀ i, 0 ≤ d₀ i
  spread : ∀ i, |(d₀ i : ℝ) - dbar d₀| ≤ dbar d₀ ^ α
  dbar_ge : 35000 ≤ dbar d₀
  D₀_le : D₀ ≤ 63 / 64 * dbar d₀
  r_le : 4 * r ≤ dbar d₀ ^ α
  mu_le : mu d₀ ≤ 1 / (2 * 10 ^ 9)

namespace Nbhd

variable {α D₀ : ℝ} {d₀ : Seq n} {r : ℕ} (h : Nbhd α d₀ r D₀)
include h

theorem n_ge : (48 : ℝ) ≤ n := by exact_mod_cast h.n48

theorem D_pos : 0 < dbar d₀ := by linarith [h.dbar_ge]

theorem mu_pos : 0 < mu d₀ := by
  have := h.n_ge; unfold mu; exact div_pos h.D_pos (by linarith)

theorem rpow_le : dbar d₀ ^ α ≤ dbar d₀ / 16 := by
  have hD := h.D_pos
  have h1 : dbar d₀ ^ α ≤ dbar d₀ ^ (3 / 5 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith [h.dbar_ge]) h.α₂.le
  have h2 : (16 : ℝ) ≤ dbar d₀ ^ (2 / 5 : ℝ) :=
    rpow_1024 ▸ rpow_le_rpow (by norm_num) (by linarith [h.dbar_ge]) (by norm_num)
  have h3 : dbar d₀ ^ (3 / 5 : ℝ) * dbar d₀ ^ (2 / 5 : ℝ) = dbar d₀ := by
    rw [← rpow_add hD]; norm_num
  have h4 : 0 ≤ dbar d₀ ^ (3 / 5 : ℝ) := by positivity
  nlinarith

theorem r_le' : (r : ℝ) ≤ dbar d₀ / 64 := by linarith [h.r_le, h.rpow_le]

theorem mu_bound : dbar d₀ ≤ n / 10 ^ 9 := by
  have hn := h.n_ge
  have := h.mu_le
  unfold mu at this
  rw [div_le_iff₀ (by linarith)] at this
  nlinarith

section ball

variable {d : Seq n} (hd : d ∈ Ball d₀ r)
include hd

omit h in
theorem dist_le : (dist1 d₀ d : ℝ) ≤ r := by exact_mod_cast hd

theorem dbar_close : |dbar d - dbar d₀| ≤ r := by
  have hn := h.n_ge
  rw [abs_sub_comm]
  calc |dbar d₀ - dbar d| ≤ dist1 d₀ d / n := abs_dbar_sub_le (by linarith) _ _
    _ ≤ r / n := by gcongr; exact dist_le hd
    _ ≤ r := div_le_self (by positivity) (by linarith)

theorem dbar_bounds : 63 / 64 * dbar d₀ ≤ dbar d ∧ dbar d ≤ 65 / 64 * dbar d₀ := by
  have := abs_le.1 (h.dbar_close hd); have := h.r_le'; constructor <;> linarith

theorem dev (i : Fin n) : |(d i : ℝ) - dbar d| ≤ 3 / 2 * dbar d₀ ^ α := by
  have h1 : |(d i : ℝ) - d₀ i| ≤ r := by
    rw [abs_sub_comm]
    have := abs_sub_le_dist1 d₀ d i
    exact_mod_cast this.trans hd
  have h2 := h.spread i
  have h3 := h.dbar_close hd
  have h4 := h.r_le
  calc |(d i : ℝ) - dbar d| = |((d i : ℝ) - d₀ i) + ((d₀ i : ℝ) - dbar d₀) + (dbar d₀ - dbar d)| := by
        ring_nf
    _ ≤ |(d i : ℝ) - d₀ i| + |(d₀ i : ℝ) - dbar d₀| + |dbar d₀ - dbar d| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ 3 / 2 * dbar d₀ ^ α := by rw [abs_sub_comm (dbar d₀)]; linarith

theorem dev' (i : Fin n) : |(d i : ℝ) - dbar d| ≤ 3 / 32 * dbar d₀ := by
  linarith [h.dev hd i, h.rpow_le]

theorem two_le (i : Fin n) : 2 ≤ d i := by
  have h1 := (abs_le.1 (h.dev' hd i)).1
  have h2 := (h.dbar_bounds hd).1
  have h3 := h.dbar_ge
  exact_mod_cast (by linarith : (2 : ℝ) ≤ d i)

theorem nonneg' (i : Fin n) : 0 ≤ d i := by linarith [h.two_le hd i]

theorem mu_le' : mu d ≤ 65 / 64 * mu d₀ := by
  have hn := h.n_ge
  unfold mu
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h.dbar_bounds hd).2 (by linarith)

theorem mu_ge' : mu d₀ ≤ 64 / 63 * mu d := by
  have hn := h.n_ge
  unfold mu
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith [(h.dbar_bounds hd).1]) (by linarith)

theorem mu_le2 : mu d ≤ 2 * mu d₀ := by linarith [h.mu_le' hd, h.mu_pos]

theorem spread' : Spread α d := by
  refine ⟨by linarith [h.mu_le2 hd, h.mu_le], fun i => ?_⟩
  have hD := h.D_pos
  have h1 : (63 / 64 * dbar d₀) ^ α ≤ dbar d ^ α :=
    rpow_le_rpow (by positivity) (h.dbar_bounds hd).1 (by linarith [h.α₁])
  rw [mul_rpow (by norm_num) hD.le] at h1
  have h2 : (63 / 64 : ℝ) ^ (1 : ℝ) ≤ (63 / 64) ^ α :=
    rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [h.α₂])
  rw [rpow_one] at h2
  have h3 : 0 ≤ dbar d₀ ^ α := by positivity
  nlinarith [h.dev hd i]

theorem dbar_ge' : 32768 ≤ dbar d ∧ D₀ ≤ dbar d := by
  have := (h.dbar_bounds hd).1
  exact ⟨by linarith [h.dbar_ge], by linarith [h.D₀_le]⟩

omit hd in
theorem M1_eq : (M1 d : ℝ) = n * dbar d := by
  have hn := h.n_ge; unfold dbar; field_simp

theorem N_pos (hev : IsEven d) : 0 < N d := by
  have hn : (0 : ℝ) < n := by linarith [h.n_ge]
  have hB := (h.dbar_bounds hd).1
  have hD := h.dbar_ge
  refine lemma_2_4a (ε := 1 / 4) (by norm_num) le_rfl d (h.nonneg' hd) hev (dbar d / n) ?_ ?_ fun i => ?_
  · rw [div_mul_cancel₀ _ hn.ne']; linarith
  · rw [div_le_iff₀ hn]
    linarith [h.mu_bound, (h.dbar_bounds hd).2]
  · rw [show 1 / 4 * (dbar d / n) = dbar d / 4 / n by ring, ← sub_div, abs_div, abs_of_pos hn,
      abs_sub_comm]
    exact div_lt_div_of_pos_right (by linarith [h.dev' hd i]) hn

theorem Delta_le : (Delta d : ℝ) ≤ 11 / 10 * dbar d := by
  obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_sup (univ : Finset (Fin n))
    ⟨⟨0, by have := h.n48; omega⟩, mem_univ _⟩ fun i => (d i).toNat
  have : (Delta d : ℝ) = d i₀ := by
    unfold Delta; rw [hi₀]; exact_mod_cast Int.toNat_of_nonneg (h.nonneg' hd i₀)
  rw [this]
  linarith [(abs_le.1 (h.dev' hd i₀)).2, (h.dbar_bounds hd).1]

theorem P_le (a v : Fin n) : P a v d ≤ 2 * mu d := by
  have hn := h.n_ge
  have hB := (h.dbar_bounds hd).1
  have hB0 : 0 < dbar d := by linarith [h.dbar_ge]
  have hBn : dbar d ≤ 2 * n / 10 ^ 9 := by linarith [h.mu_bound, (h.dbar_bounds hd).2]
  have hΔ := h.Delta_le hd
  have hΔ0 : (0 : ℝ) ≤ Delta d := by positivity
  have hM := h.M1_eq (d := d)
  have hprod : ((Delta d : ℝ) + 1) * Delta d ≤ (11 / 10 * dbar d + 1) * (11 / 10 * dbar d) :=
    mul_le_mul (by linarith) hΔ hΔ0 (by linarith)
  have hBB := mul_le_mul_of_nonneg_left hBn hB0.le
  have hBn' := mul_le_mul_of_nonneg_left hn hB0.le
  have hlt : 2 * ((Delta d : ℝ) + 1) * Delta d < M1 d := by rw [hM]; nlinarith
  refine (lemma_2_3 d hlt a v).trans ?_
  have hM0 : (0 : ℝ) < M1 d := by nlinarith
  rw [mul_one_sub, mul_div_cancel₀ _ hM0.ne', hM]
  have hden : 0 < (n : ℝ) * dbar d - Delta d * (Delta d + 2) := by nlinarith
  unfold mu
  rw [← mul_div_assoc, div_le_div_iff₀ hden (by linarith)]
  have hsq : (Delta d : ℝ) ^ 2 ≤ (11 / 10 * dbar d) ^ 2 := by gcongr
  nlinarith

theorem err71_le : err71 α d ≤ 4 * err71 α d₀ := by
  have hD := h.D_pos
  have hB := h.dbar_bounds hd
  have hB0 : 0 < dbar d := by linarith
  have h1 : dbar d ^ (4 * α - 4) ≤ (64 / 63) ^ 2 * dbar d₀ ^ (4 * α - 4) :=
    rpow_le_of_le hD hB0 (by norm_num) (by linarith) (by linarith [h.α₁]) (by linarith [h.α₂])
  have h2 : 0 ≤ dbar d₀ ^ (4 * α - 4) := by positivity
  have h3 := h.mu_le2 hd
  have h4 := h.mu_pos
  unfold err71
  calc mu d * dbar d ^ (4 * α - 4) ≤ 2 * mu d₀ * ((64 / 63) ^ 2 * dbar d₀ ^ (4 * α - 4)) :=
        mul_le_mul h3 h1 (by positivity) (by positivity)
    _ ≤ 4 * (mu d₀ * dbar d₀ ^ (4 * α - 4)) := by nlinarith

theorem err71_ge : err71 α d₀ ≤ 4 * err71 α d := by
  have hD := h.D_pos
  have hB := h.dbar_bounds hd
  have hB0 : 0 < dbar d := by linarith
  have h1 : dbar d₀ ^ (4 * α - 4) ≤ (65 / 64) ^ 2 * dbar d ^ (4 * α - 4) :=
    rpow_le_of_le hB0 hD (by norm_num) (by linarith) (by linarith [h.α₁]) (by linarith [h.α₂])
  have h2 : 0 ≤ dbar d ^ (4 * α - 4) := by positivity
  have h3 := h.mu_ge' hd
  have h4 := h.mu_pos
  have h5 : 0 < mu d := by linarith
  unfold err71
  calc mu d₀ * dbar d₀ ^ (4 * α - 4) ≤ 64 / 63 * mu d * ((65 / 64) ^ 2 * dbar d ^ (4 * α - 4)) :=
        mul_le_mul h3 h1 (by positivity) (by positivity)
    _ ≤ 4 * (mu d * dbar d ^ (4 * α - 4)) := by nlinarith

theorem err71_pos : 0 < err71 α d := by
  have := h.mu_pos; have := h.err71_ge hd
  have : 0 < err71 α d₀ := by unfold err71; exact mul_pos h.mu_pos (rpow_pos_of_pos h.D_pos _)
  linarith

end ball

theorem exactOK : ExactOK (2 * mu d₀) (Ball d₀ r) where
  n2 := by have := h.n48; omega
  two_le d hd := h.two_le hd
  mu_le d hd := h.mu_le2 hd
  N_pos d hd hev := h.N_pos hd hev
  P_le d hd _ a v := h.P_le hd a v

theorem grOK : GrOK α (2 * mu d₀) (Ball d₀ r) where
  α₁ := h.α₁
  α₂ := h.α₂
  n2 := by have := h.n48; omega
  spread d hd := h.spread' hd
  dbar_ge d hd := (h.dbar_ge' hd).1
  mu_le d hd := h.mu_le2 hd

/-- Claim 6.4's hypotheses hold on the ball, with `ε = 4C·err71(d₀)`, given Lemma 7.1. -/
theorem ok {C : ℝ} (hC : 0 ≤ C)
    (h71a : ∀ d ∈ Ball d₀ r, ∀ a b, Close (opR Pgr Ygr a b d) (Rgr a b d) (C * err71 α d))
    (h71b : ∀ d ∈ Ball d₀ r, ∀ a v, a ≠ v → Close (opP Pgr Rgr a v d) (Pgr a v d) (C * err71 α d))
    (h71c : ∀ d ∈ Ball d₀ r, ∀ a v b, a ≠ v → a ≠ b → v ≠ b →
      Close (opY Pgr Ygr a v b d) (Ygr a v b d) (C * err71 α d))
    (hε0 : 0 < 4 * C * err71 α d₀) (hε1 : 4 * C * err71 α d₀ ≤ 1 / 1000) :
    OK α (2 * mu d₀) (4 * C * err71 α d₀) (Ball d₀ r) where
  ex := h.exactOK
  gr := h.grOK
  μ_pos := by linarith [h.mu_pos]
  μ_le := by linarith [h.mu_le]
  ε_pos := hε0
  ε_le := hε1
  a d hd a b := (h71a d hd a b).mono (by nlinarith [h.err71_le hd])
  b d hd a v hav := (h71b d hd a v hav).mono (by nlinarith [h.err71_le hd])
  c d hd a v b hav hab hvb := (h71c d hd a v b hav hab hvb).mono (by nlinarith [h.err71_le hd])

end Nbhd

end LW
