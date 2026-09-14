import MajorityDynamics.Literature.FKMFormal.Binom
import MajorityDynamics.Literature.FKMFormal.Chernoff

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! # Core estimates for a biased majority of independent binomials.

`X ~ Bin(K,p)`, `Y, Z ~ Bin(B,p)` independent: `P[X + Y ≥ Z + 2] ≥ 1/2 + ξ₀·γ` whenever
`γ√(Bp) ≤ Kp`, `γ ≤ 1`, `Kp` large.  Also a point-mass bound for `Y - Z`. -/

namespace MD

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ} {p : ℝ}

/-- Bulk lower-bound constant: `bin N i p ≥ c4 / sd N p` for `|i - Np| ≤ 4 sd`. -/
noncomputable def c4 : ℝ := 3 * exp (-160) / 20

/-- The bias constant of the core estimate. -/
noncomputable def ξ₀ : ℝ := 9 * c4 / 128

lemma c4_pos : 0 < c4 := by unfold c4; positivity
lemma c4_le : c4 ≤ 3 / 20 := by
  unfold c4; have := exp_le_one_iff.2 (by norm_num : (-160 : ℝ) ≤ 0); linarith
lemma ξ₀_pos : 0 < ξ₀ := by unfold ξ₀; have := c4_pos; positivity
lemma ξ₀_le : ξ₀ ≤ 1 / 4 := by unfold ξ₀; have := c4_le; linarith

lemma bin_ge_c4 {N i : ℕ} (h0 : 0 < p) (h1 : p < 1) (hσ : 20 ≤ sd N p)
    (hi : |(i : ℝ) - N * p| ≤ 4 * sd N p) : c4 / sd N p ≤ bin N i p := by
  have := bin_ge h0 h1 (R := 4) (by norm_num) (by linarith) hi
  convert this using 1
  unfold c4; norm_num; ring

/-- `P[Y + a ≥ Z + 2]` for independent `Y, Z ~ Bin(B,p)`. -/
noncomputable def Pdiff (B : ℕ) (p : ℝ) (a : ℤ) : ℝ :=
  ∑ k₂ ∈ range (B + 1), ∑ k₃ ∈ range (B + 1),
    bin B k₂ p * bin B k₃ p * if (k₃ : ℤ) + 2 ≤ k₂ + a then 1 else 0

/-- `P[|Y - Z| ≤ t]`. -/
noncomputable def Qdiff (B : ℕ) (p : ℝ) (t : ℤ) : ℝ :=
  ∑ k₂ ∈ range (B + 1), ∑ k₃ ∈ range (B + 1),
    bin B k₂ p * bin B k₃ p * if |(k₂ : ℤ) - k₃| ≤ t then 1 else 0

lemma sum_sum_bin (B : ℕ) (p : ℝ) :
    ∑ k₂ ∈ range (B + 1), ∑ k₃ ∈ range (B + 1), bin B k₂ p * bin B k₃ p = 1 := by
  simp_rw [← mul_sum, sum_bin, mul_one, sum_bin]

lemma Pdiff_add (B : ℕ) (p : ℝ) (a : ℤ) : Pdiff B p a + Pdiff B p (3 - a) = 1 := by
  have h : Pdiff B p (3 - a) = ∑ k₂ ∈ range (B + 1), ∑ k₃ ∈ range (B + 1),
      bin B k₂ p * bin B k₃ p * if (k₃ : ℤ) + 2 ≤ k₂ + a then 0 else 1 := by
    unfold Pdiff
    rw [sum_comm]
    refine sum_congr rfl fun k₂ _ => sum_congr rfl fun k₃ _ => ?_
    rw [mul_comm (bin B k₃ p)]
    congr 1
    split_ifs <;> first | rfl | omega
  rw [h]
  unfold Pdiff
  rw [← sum_add_distrib]
  calc _ = ∑ k₂ ∈ range (B + 1), ∑ k₃ ∈ range (B + 1), bin B k₂ p * bin B k₃ p := by
        refine sum_congr rfl fun k₂ _ => ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun k₃ _ => ?_
        split_ifs <;> ring
    _ = 1 := sum_sum_bin B p

lemma Pdiff_mono (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {B : ℕ} {a b : ℤ} (hab : a ≤ b) :
    Pdiff B p a ≤ Pdiff B p b := by
  unfold Pdiff
  refine sum_le_sum fun k₂ _ => sum_le_sum fun k₃ _ =>
    mul_le_mul_of_nonneg_left ?_ (mul_nonneg (bin_nonneg hp0 hp1) (bin_nonneg hp0 hp1))
  split_ifs <;> first | omega | norm_num

lemma Qdiff_mono (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {B : ℕ} {s t : ℤ} (hst : s ≤ t) :
    Qdiff B p s ≤ Qdiff B p t := by
  unfold Qdiff
  refine sum_le_sum fun k₂ _ => sum_le_sum fun k₃ _ =>
    mul_le_mul_of_nonneg_left ?_ (mul_nonneg (bin_nonneg hp0 hp1) (bin_nonneg hp0 hp1))
  split_ifs <;> first | omega | norm_num

lemma Pdiff_sub (B : ℕ) (p : ℝ) {a : ℤ} (ha : 2 ≤ a) :
    Pdiff B p a - Pdiff B p (3 - a) = Qdiff B p (a - 2) := by
  unfold Pdiff Qdiff
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun k₂ _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun k₃ _ => ?_
  rw [← mul_sub]
  congr 1
  simp only [abs_le]
  split_ifs <;> first | omega | norm_num

lemma Pdiff_half (B : ℕ) (p : ℝ) {a : ℤ} (ha : 2 ≤ a) :
    Pdiff B p a - 1 / 2 = Qdiff B p (a - 2) / 2 := by
  have h1 := Pdiff_add B p a
  have h2 := Pdiff_sub B p ha
  linarith

lemma Pdiff_ge_half (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {B : ℕ} {a : ℤ} (ha : 2 ≤ a) :
    1 / 2 ≤ Pdiff B p a := by
  have h1 := Pdiff_add B p a
  have h2 := Pdiff_mono hp0 hp1 (B := B) (by omega : 3 - a ≤ a)
  linarith

/-- Bulk lower bound on `P[|Y - Z| ≤ t]`. -/
lemma Qdiff_ge (hp0 : 0 < p) (hp1 : p < 1) {B : ℕ} (hσ : 20 ≤ sd B p) (t : ℕ)
    (ht : (t : ℝ) ≤ 2 * sd B p) :
    3 / 4 * ((t + 1) * (c4 / sd B p)) ≤ Qdiff B p t := by
  set σ := sd B p with hσdef
  have hσ2 : σ ^ 2 = B * p * (1 - p) := sd_sq hp0.le hp1.le
  have hq : 0 < 1 - p := by linarith
  have hB4 : (B : ℝ) * p + 4 * σ ≤ B := by
    have h1 : 16 ≤ (B : ℝ) * (1 - p) := by nlinarith
    have h2 : (4 * σ) ^ 2 ≤ ((B : ℝ) * (1 - p)) ^ 2 := by nlinarith
    have h3 : 4 * σ ≤ (B : ℝ) * (1 - p) := by
      by_contra h; push Not at h; nlinarith
    linarith
  have hW := sum_bin_window hp0.le hp1.le (by linarith : 0 < sd B p)
  set W := (range (B + 1)).filter (fun k : ℕ => |(k : ℝ) - B * p| < 2 * sd B p) with hWdef
  have inner : ∀ k₂ ∈ W, (t + 1) * (c4 / σ) ≤
      ∑ k₃ ∈ range (B + 1), bin B k₃ p * if |(k₂ : ℤ) - k₃| ≤ t then 1 else 0 := by
    intro k₂ hk₂
    have hk₂' : |(k₂ : ℝ) - B * p| < 2 * σ := (mem_filter.1 hk₂).2
    obtain ⟨hlo, hhi⟩ := abs_lt.1 hk₂'
    have hsub : Icc k₂ (k₂ + t) ⊆ range (B + 1) := by
      intro k hk
      rw [mem_Icc] at hk; rw [mem_range]
      have h1 : (k : ℝ) ≤ k₂ + t := by exact_mod_cast hk.2
      have : (k : ℝ) < B := by linarith
      have : k < B := by exact_mod_cast this
      omega
    calc (t + 1) * (c4 / σ) = ∑ _k₃ ∈ Icc k₂ (k₂ + t), c4 / σ := by
          rw [sum_const, Nat.card_Icc, show k₂ + t + 1 - k₂ = t + 1 by omega, nsmul_eq_mul]
          push_cast; ring
      _ ≤ ∑ k₃ ∈ Icc k₂ (k₂ + t), bin B k₃ p * if |(k₂ : ℤ) - k₃| ≤ t then 1 else 0 := by
          refine sum_le_sum fun k₃ hk₃ => ?_
          rw [mem_Icc] at hk₃
          rw [if_pos (by rw [abs_le]; omega), mul_one]
          refine bin_ge_c4 hp0 hp1 hσ ?_
          have h1 : (k₂ : ℝ) ≤ k₃ := by exact_mod_cast hk₃.1
          have h2 : (k₃ : ℝ) ≤ k₂ + t := by exact_mod_cast hk₃.2
          rw [abs_le]; constructor <;> linarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun k₃ _ _ => by
          apply mul_nonneg (bin_nonneg hp0.le hp1.le); split_ifs <;> norm_num
  have hfac : Qdiff B p t = ∑ k₂ ∈ range (B + 1), bin B k₂ p *
      ∑ k₃ ∈ range (B + 1), bin B k₃ p * if |(k₂ : ℤ) - k₃| ≤ t then 1 else 0 := by
    unfold Qdiff
    refine sum_congr rfl fun k₂ _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun k₃ _ => by ring
  rw [hfac]
  calc 3 / 4 * ((t + 1) * (c4 / σ)) ≤ (∑ k ∈ W, bin B k p) * ((t + 1) * (c4 / σ)) := by
        apply mul_le_mul_of_nonneg_right hW
        have := c4_pos; positivity
    _ = ∑ k₂ ∈ W, bin B k₂ p * ((t + 1) * (c4 / σ)) := by rw [sum_mul]
    _ ≤ ∑ k₂ ∈ W, bin B k₂ p *
        ∑ k₃ ∈ range (B + 1), bin B k₃ p * if |(k₂ : ℤ) - k₃| ≤ t then 1 else 0 :=
        sum_le_sum fun k₂ hk₂ =>
          mul_le_mul_of_nonneg_left (inner k₂ hk₂) (bin_nonneg hp0.le hp1.le)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k₂ _ _ => by
        apply mul_nonneg (bin_nonneg hp0.le hp1.le)
        apply sum_nonneg fun k₃ _ => ?_
        apply mul_nonneg (bin_nonneg hp0.le hp1.le); split_ifs <;> norm_num

set_option maxHeartbeats 1000000 in
/-- The main binomial-sum estimate (large variance case). -/
lemma core_sum (hp0 : 0 < p) (hp1 : p < 1) {K B : ℕ} (hK : 10000 ≤ (K : ℝ) * p)
    (hσ : 20 ≤ sd B p) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγ : γ * √(B * p) ≤ K * p) :
    1 / 2 + ξ₀ * γ ≤ ∑ k₁ ∈ range (K + 1), bin K k₁ p * Pdiff B p k₁ := by
  set σ := sd B p with hσdef
  have hσ2 : σ ^ 2 = B * p * (1 - p) := sd_sq hp0.le hp1.le
  have hσpos : 0 < σ := by linarith
  have hq : 0 < 1 - p := by linarith
  have hKp : (K : ℝ) * p ≤ K := by nlinarith
  have hK16 : 16 ≤ K := by
    have : (16 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  set g : ℕ → ℝ := fun k => Pdiff B p k - 1 / 2 with hg
  have hsplit : ∑ k₁ ∈ range (K + 1), bin K k₁ p * Pdiff B p k₁ =
      1 / 2 + ∑ k₁ ∈ range (K + 1), bin K k₁ p * g k₁ := by
    have : ∀ k, bin K k p * Pdiff B p k = bin K k p * (1 / 2) + bin K k p * g k := fun k => by
      simp only [hg]; ring
    simp_rw [this, sum_add_distrib, ← sum_mul, sum_bin]; ring
  rw [hsplit]
  -- nonnegativity of g on k ≥ 2
  have hg_nn : ∀ k : ℕ, 2 ≤ k → 0 ≤ g k := fun k hk => by
    simp only [hg]; linarith [Pdiff_ge_half hp0.le hp1.le (B := B) (a := k) (by omega)]
  -- low terms
  have hlow : 0 ≤ ∑ k₁ ∈ range 4, bin K k₁ p * g k₁ := by
    simp only [sum_range_succ, sum_range_zero, zero_add]
    have h03 : g 0 = -g 3 := by
      simp only [hg]; have := Pdiff_add B p 0; norm_num at this; push_cast; linarith
    have h12 : g 1 = -g 2 := by
      simp only [hg]; have := Pdiff_add B p 1; norm_num at this; push_cast; linarith
    have hm : ∀ i : ℕ, i < 3 → bin K i p ≤ bin K (i + 1) p := fun i hi =>
      bin_mono_left hp0 hp1 (by omega) (by
        have : (i : ℝ) < 3 := by exact_mod_cast hi
        linarith)
    have hb01 := hm 0 (by norm_num)
    have hb12 := hm 1 (by norm_num)
    have hb23 := hm 2 (by norm_num)
    have hg2 := hg_nn 2 le_rfl
    have hg3 := hg_nn 3 (by norm_num)
    rw [h03, h12]
    nlinarith [mul_nonneg (sub_nonneg.2 (hb01.trans (hb12.trans hb23))) hg3,
      mul_nonneg (sub_nonneg.2 hb12) hg2]
  -- window for K
  set σK := sd K p with hσK
  have hσK2 : σK ^ 2 = K * p * (1 - p) := sd_sq hp0.le hp1.le
  have hσKpos : 0 < σK := by
    rw [hσK]; unfold sd; apply sqrt_pos.2
    have : (0 : ℝ) < K := by linarith
    positivity
  have hWK := sum_bin_window hp0.le hp1.le hσKpos
  set WK := (range (K + 1)).filter (fun k : ℕ => |(k : ℝ) - K * p| < 2 * sd K p) with hWKdef
  have hσK_le : σK ≤ √(K * p) := by
    rw [hσK]; unfold sd; apply Real.sqrt_le_sqrt; nlinarith
  have hsqrt : 4 ≤ √((K : ℝ) * p) := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : √((K : ℝ) * p) ^ 2 = K * p := Real.sq_sqrt (by positivity)
  have hWK_lo : ∀ k ∈ WK, (K : ℝ) * p / 2 ≤ k := by
    intro k hk
    have := (abs_lt.1 (mem_filter.1 hk).2).1
    nlinarith
  -- lower bound for g on the window
  set m := min ((K : ℝ) * p / 4) (2 * σ) with hm
  have hm_pos : 0 ≤ m := by rw [hm]; apply le_min <;> positivity
  set t₀ := ⌊m⌋₊ with ht₀
  have ht₀_le : (t₀ : ℝ) ≤ m := Nat.floor_le hm_pos
  have ht₀_ge : m ≤ t₀ + 1 := (Nat.lt_floor_add_one m).le
  have hQ := Qdiff_ge hp0 hp1 hσ t₀ (ht₀_le.trans (min_le_right _ _))
  have hg_win : ∀ k ∈ WK, 3 / 8 * (m * (c4 / σ)) ≤ g k := by
    intro k hk
    have hk2 : (K : ℝ) * p / 2 ≤ k := hWK_lo k hk
    have hk2' : 2 ≤ k := by
      have : (2 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have ht₀k : (t₀ : ℤ) ≤ (k : ℤ) - 2 := by
      have : (t₀ : ℝ) ≤ (k : ℝ) - 2 := by
        linarith [ht₀_le.trans (min_le_left _ _)]
      exact_mod_cast this
    have := Qdiff_mono hp0.le hp1.le (B := B) ht₀k
    have hhalf := Pdiff_half B p (a := k) (by omega)
    simp only [hg]
    rw [hhalf]
    have hc : 0 ≤ c4 / σ := by have := c4_pos; positivity
    nlinarith [mul_le_mul_of_nonneg_right ht₀_ge hc]
  have hWK_sub : WK ⊆ Ico 4 (K + 1) := by
    intro k hk
    rw [mem_Ico]
    have h1 := hWK_lo k hk
    have h2 := mem_range.1 (mem_filter.1 hk).1
    have : (4 : ℝ) ≤ k := by linarith
    exact ⟨by exact_mod_cast this, h2⟩
  have hIco : ∑ k₁ ∈ range (K + 1), bin K k₁ p * g k₁ =
      ∑ k₁ ∈ range 4, bin K k₁ p * g k₁ + ∑ k₁ ∈ Ico 4 (K + 1), bin K k₁ p * g k₁ := by
    rw [range_eq_Ico, range_eq_Ico, sum_Ico_consecutive _ (by norm_num) (by omega)]
  have hhigh : 3 / 4 * (3 / 8 * (m * (c4 / σ))) ≤ ∑ k₁ ∈ Ico 4 (K + 1), bin K k₁ p * g k₁ := by
    calc 3 / 4 * (3 / 8 * (m * (c4 / σ))) ≤ (∑ k ∈ WK, bin K k p) * (3 / 8 * (m * (c4 / σ))) := by
          apply mul_le_mul_of_nonneg_right hWK
          have := c4_pos; positivity
      _ = ∑ k ∈ WK, bin K k p * (3 / 8 * (m * (c4 / σ))) := by rw [sum_mul]
      _ ≤ ∑ k ∈ WK, bin K k p * g k :=
          sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hg_win k hk) (bin_nonneg hp0.le hp1.le)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hWK_sub fun k hk _ =>
          mul_nonneg (bin_nonneg hp0.le hp1.le) (hg_nn k (by have := (mem_Ico.1 hk).1; omega))
  -- final numeric comparison
  have hσle : σ ≤ √((B : ℝ) * p) := by
    rw [hσdef]; unfold sd; apply Real.sqrt_le_sqrt; nlinarith
  have hγσ : γ * σ ≤ K * p := (mul_le_mul_of_nonneg_left hσle hγ0).trans hγ
  have hm_ge : γ / 4 * σ ≤ m := by
    rw [hm]; apply le_min <;> nlinarith
  rw [hIco]
  clear_value m t₀ σ σK g WK
  have hfin : ξ₀ * γ ≤ 3 / 4 * (3 / 8 * (m * (c4 / σ))) := by
    have hc := c4_pos
    have e : 3 / 4 * (3 / 8 * (m * (c4 / σ))) = 9 / 32 * c4 * (m / σ) := by ring
    have : γ / 4 ≤ m / σ := by rw [le_div_iff₀ hσpos]; exact hm_ge
    rw [e, ξ₀]
    calc 9 * c4 / 128 * γ = 9 / 32 * c4 * (γ / 4) := by ring
      _ ≤ 9 / 32 * c4 * (m / σ) := mul_le_mul_of_nonneg_left this (by positivity)
  linarith

/-- Core estimate on a product space: three disjoint coordinate blocks of sizes `K, B, B`. -/
theorem Pr_maj_ge (hq : IsProb q) {T₁ T₂ T₃ : Finset ι} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (h₁ : ∀ i ∈ T₁, q i = p) (h₂ : ∀ i ∈ T₂, q i = p) (h₃ : ∀ i ∈ T₃, q i = p)
    (h₁₂ : Disjoint T₁ T₂) (h₁₃ : Disjoint T₁ T₃) (h₂₃ : Disjoint T₂ T₃)
    (hB : T₂.card = T₃.card) (hK : 10000 ≤ (T₁.card : ℝ) * p)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hγ : γ * √(T₂.card * p) ≤ T₁.card * p) :
    1 / 2 + ξ₀ * γ ≤ Pr q (fun x => cnt T₃ x + 2 ≤ cnt T₁ x + cnt T₂ x) := by
  classical
  set K := T₁.card with hKdef
  set B := T₂.card with hBdef
  by_cases hσ : 20 ≤ sd B p
  · -- large variance: binomial sums
    have hp1' : p < 1 := by
      rcases hp1.eq_or_lt with h | h
      · exfalso; subst h; simp [sd] at hσ; linarith
      · exact h
    have hE : Pr q (fun x => cnt T₃ x + 2 ≤ cnt T₁ x + cnt T₂ x) =
        ∑ k₁ ∈ range (K + 1), bin K k₁ p * Pdiff B p k₁ := by
      rw [Pr_eq_E]
      rw [E_cnt3 h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (fun k₁ k₂ k₃ => if k₃ + 2 ≤ k₁ + k₂ then (1 : ℝ) else 0)]
      refine sum_congr rfl fun k₁ _ => ?_
      congr 1
      unfold Pdiff
      rw [← hB]
      refine sum_congr rfl fun k₂ _ => sum_congr rfl fun k₃ _ => ?_
      congr 1
      split_ifs <;> first | rfl | omega
    rw [hE]
    exact core_sum hp0 hp1' hK hσ hγ0 hγ1 hγ
  · -- small variance: Chernoff
    push Not at hσ
    have hσ2 : sd B p ^ 2 = B * p * (1 - p) := sd_sq hp0.le hp1
    have hσnn := sd_nonneg B p
    have hν : (B : ℝ) * min p (1 - p) ≤ 800 := by
      have : (B : ℝ) * min p (1 - p) ≤ 2 * (B * p * (1 - p)) := by
        rcases le_total p (1 - p) with h | h
        · rw [min_eq_left h]; nlinarith
        · rw [min_eq_right h]; nlinarith
      nlinarith
    set μ := (K : ℝ) * p with hμ
    -- three bad events
    have hA : Pr q (fun x => (cnt T₁ x : ℝ) ≤ μ - μ / 2) ≤ exp (-500) := by
      refine (Pr_cnt_le hq hp0.le hp1 h₁ (by positivity)).trans (exp_le_exp.2 ?_)
      rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
      nlinarith
    have ht : (0 : ℝ) ≤ μ / 4 - 1 := by linarith
    have hBC : ∀ T : Finset ι, (∀ i ∈ T, q i = p) → T.card = B →
        Pr q (fun x => μ / 4 - 1 ≤ |(cnt T x : ℝ) - T.card * p|) ≤ 2 * exp (-624) := by
      intro T hT hTB
      refine (Pr_cnt_abs_ge hq hp0.le hp1 hT ht).trans ?_
      gcongr
      rw [hTB]
      have hmin : 0 ≤ (B : ℝ) * min p (1 - p) :=
        mul_nonneg (Nat.cast_nonneg _) (le_min hp0.le (by linarith))
      set t := μ / 4 - 1 with htdef
      have ht' : 2499 ≤ t := by rw [htdef]; linarith
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.2 ht') (by linarith : (0 : ℝ) ≤ t + 1251)]
    have h2 := hBC T₂ h₂ rfl
    have h3 := hBC T₃ h₃ hB.symm
    have hunion : Pr q (fun x => ¬ (cnt T₃ x + 2 ≤ cnt T₁ x + cnt T₂ x)) ≤
        exp (-500) + 2 * exp (-624) + 2 * exp (-624) := by
      refine le_trans (Pr_mono hq (B := fun x => ((cnt T₁ x : ℝ) ≤ μ - μ / 2 ∨
        μ / 4 - 1 ≤ |(cnt T₂ x : ℝ) - T₂.card * p|) ∨
        μ / 4 - 1 ≤ |(cnt T₃ x : ℝ) - T₃.card * p|) fun x hx => ?_) ?_
      · by_contra hcon
        push Not at hcon
        obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hcon
        apply hx
        rw [abs_lt] at hc2 hc3
        rw [← hB] at hc3
        have : (cnt T₃ x : ℝ) + 2 < cnt T₁ x + cnt T₂ x := by linarith
        exact_mod_cast this.le
      · refine (Pr_or_le hq _ _).trans ?_
        linarith [Pr_or_le hq (fun x => (cnt T₁ x : ℝ) ≤ μ - μ / 2)
          (fun x => μ / 4 - 1 ≤ |(cnt T₂ x : ℝ) - T₂.card * p|)]
    rw [Pr_not] at hunion
    have e1 : exp (-500) ≤ 1 / 16 := by
      have := exp_neg_le_inv_add_one (x := 500) (by norm_num); norm_num at this ⊢; linarith
    have e2 : exp (-624) ≤ 1 / 32 := by
      have := exp_neg_le_inv_add_one (x := 624) (by norm_num); norm_num at this ⊢; linarith
    have := ξ₀_le
    nlinarith [ξ₀_pos]

/-- Point mass of a difference of two independent binomial counts. -/
lemma Pr_cnt_sub_eq_le {T₁ T₂ : Finset ι} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : ∀ i ∈ T₁, q i = p) (h₂ : ∀ i ∈ T₂, q i = p) (hd : Disjoint T₁ T₂)
    (hσ : 6 ≤ sd T₂.card p) (r : ℤ) :
    Pr q (fun x => (cnt T₁ x : ℤ) - cnt T₂ x = r) ≤ exp 6 / sd T₂.card p := by
  classical
  rw [Pr_eq_E, E_cnt2 h₁ h₂ hd (fun k₁ k₂ => if (k₁ : ℤ) - k₂ = r then (1 : ℝ) else 0)]
  have hσpos : 0 < sd T₂.card p := by linarith
  have hb : ∀ k₁, ∑ k₂ ∈ range (T₂.card + 1),
      bin T₁.card k₁ p * bin T₂.card k₂ p * (if (k₁ : ℤ) - k₂ = r then (1 : ℝ) else 0) ≤
      bin T₁.card k₁ p * (exp 6 / sd T₂.card p) := by
    intro k₁
    calc ∑ k₂ ∈ range (T₂.card + 1),
          bin T₁.card k₁ p * bin T₂.card k₂ p * (if (k₁ : ℤ) - k₂ = r then (1 : ℝ) else 0)
        ≤ ∑ k₂ ∈ range (T₂.card + 1),
          bin T₁.card k₁ p * (exp 6 / sd T₂.card p) * (if (k₁ : ℤ) - k₂ = r then (1 : ℝ) else 0) := by
          refine sum_le_sum fun k₂ _ => ?_
          apply mul_le_mul_of_nonneg_right _ (by split_ifs <;> norm_num)
          exact mul_le_mul_of_nonneg_left (bin_le hp0 hp1 hσ) (bin_nonneg hp0.le hp1.le)
      _ = bin T₁.card k₁ p * (exp 6 / sd T₂.card p) *
          ((range (T₂.card + 1)).filter fun k₂ : ℕ => (k₁ : ℤ) - k₂ = r).card := by
          rw [← mul_sum, sum_boole]
      _ ≤ bin T₁.card k₁ p * (exp 6 / sd T₂.card p) * 1 := by
          gcongr
          · exact mul_nonneg (bin_nonneg hp0.le hp1.le) (by positivity)
          · exact_mod_cast card_le_one.2 fun a ha b hb => by
              have ha' := (mem_filter.1 ha).2
              have hb' := (mem_filter.1 hb).2
              simp only [Int.subNatNat_eq_coe] at ha' hb'
              omega
      _ = _ := mul_one _
  calc _ ≤ ∑ k₁ ∈ range (T₁.card + 1), bin T₁.card k₁ p * (exp 6 / sd T₂.card p) :=
        sum_le_sum fun k₁ _ => hb k₁
    _ = exp 6 / sd T₂.card p := by rw [← sum_mul, sum_bin, one_mul]

lemma Pr_cnt_sub_eq_le' {T₁ T₂ : Finset ι} (hp0 : 0 < p) (hp1 : p < 1)
    (h₁ : ∀ i ∈ T₁, q i = p) (h₂ : ∀ i ∈ T₂, q i = p) (hd : Disjoint T₁ T₂)
    (hσ : 6 ≤ sd T₁.card p) (r : ℤ) :
    Pr q (fun x => (cnt T₁ x : ℤ) - cnt T₂ x = r) ≤ exp 6 / sd T₁.card p := by
  have := Pr_cnt_sub_eq_le hp0 hp1 h₂ h₁ hd.symm hσ (-r)
  refine le_trans (le_of_eq (Pr_congr fun x => ?_)) this
  omega

end MD
