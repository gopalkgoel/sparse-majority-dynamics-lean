import MajorityDynamics.Literature.FKMFormal.Prob

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! # Chernoff tail bounds for coordinate counts (explicit constants). -/

namespace MD

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}

lemma exp_sub_one_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : exp θ - 1 ≤ θ + θ ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le (x := θ) (by rw [abs_of_nonneg h0]; exact h1)
  linarith [(abs_le.1 this).2]

lemma exp_neg_sub_one_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : exp (-θ) - 1 ≤ -θ + θ ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le (x := -θ) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
  have h := (abs_le.1 this).2
  nlinarith [h]

/-- The exponent `μθ² - θt` optimised over `θ ∈ [0,1]`. -/
lemma exists_theta {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) :
    ∃ θ, 0 ≤ θ ∧ θ ≤ 1 ∧ μ * θ ^ 2 - θ * t ≤ -(t ^ 2 / (4 * μ + 2 * t)) := by
  by_cases hμ0 : μ = 0
  · subst hμ0
    refine ⟨1, by norm_num, le_rfl, ?_⟩
    rcases ht.eq_or_lt with h | h
    · subst h; simp
    · rw [show (4 * 0 + 2 * t) = 2 * t by ring, show t ^ 2 / (2 * t) = t / 2 by
        field_simp]
      linarith
  have hμp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hμ0)
  by_cases h : t ≤ 2 * μ
  · refine ⟨t / (2 * μ), by positivity, by rw [div_le_one (by positivity)]; exact h, ?_⟩
    have h1 : μ * (t / (2 * μ)) ^ 2 - t / (2 * μ) * t = -(t ^ 2 / (4 * μ)) := by
      field_simp; ring
    rw [h1, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    linarith
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    push Not at h
    have h2 : t ^ 2 / (4 * μ + 2 * t) ≤ t / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith

/-- Upper tail from an mgf bound `E[e^{θF}] ≤ exp (μ (e^θ - 1))` for `θ ∈ [0,1]`. -/
lemma tail_upper_of_mgf (hq : IsProb q) {F : (ι → Bool) → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hm : ∀ θ, 0 ≤ θ → θ ≤ 1 → E q (fun x => exp (θ * F x)) ≤ exp (μ * (exp θ - 1)))
    {t : ℝ} (ht : 0 ≤ t) :
    Pr q (fun x => μ + t ≤ F x) ≤ exp (-(t ^ 2 / (4 * μ + 2 * t))) := by
  obtain ⟨θ, h0, h1, hθ⟩ := exists_theta hμ ht
  calc Pr q (fun x => μ + t ≤ F x)
      ≤ Pr q (fun x => exp (θ * (μ + t)) ≤ exp (θ * F x)) :=
        Pr_mono hq fun x hx => exp_le_exp.2 (mul_le_mul_of_nonneg_left hx h0)
    _ ≤ E q (fun x => exp (θ * F x)) / exp (θ * (μ + t)) :=
        Pr_le_E_div hq (fun x => (exp_pos _).le) (exp_pos _)
    _ ≤ exp (μ * (exp θ - 1)) / exp (θ * (μ + t)) := by gcongr; exact hm θ h0 h1
    _ = exp (μ * (exp θ - 1) - θ * (μ + t)) := by rw [exp_sub]
    _ ≤ exp (-(t ^ 2 / (4 * μ + 2 * t))) := by
        apply exp_le_exp.2
        have := exp_sub_one_le h0 h1
        nlinarith [mul_le_mul_of_nonneg_left this hμ]

/-- Lower tail from an mgf bound `E[e^{-θF}] ≤ exp (μ (e^{-θ} - 1))` for `θ ∈ [0,1]`. -/
lemma tail_lower_of_mgf (hq : IsProb q) {F : (ι → Bool) → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hm : ∀ θ, 0 ≤ θ → θ ≤ 1 → E q (fun x => exp (-θ * F x)) ≤ exp (μ * (exp (-θ) - 1)))
    {t : ℝ} (ht : 0 ≤ t) :
    Pr q (fun x => F x ≤ μ - t) ≤ exp (-(t ^ 2 / (4 * μ + 2 * t))) := by
  obtain ⟨θ, h0, h1, hθ⟩ := exists_theta hμ ht
  calc Pr q (fun x => F x ≤ μ - t)
      ≤ Pr q (fun x => exp (-θ * (μ - t)) ≤ exp (-θ * F x)) :=
        Pr_mono hq fun x hx => exp_le_exp.2 (by nlinarith)
    _ ≤ E q (fun x => exp (-θ * F x)) / exp (-θ * (μ - t)) :=
        Pr_le_E_div hq (fun x => (exp_pos _).le) (exp_pos _)
    _ ≤ exp (μ * (exp (-θ) - 1)) / exp (-θ * (μ - t)) := by gcongr; exact hm θ h0 h1
    _ = exp (μ * (exp (-θ) - 1) - -θ * (μ - t)) := by rw [exp_sub]
    _ ≤ exp (-(t ^ 2 / (4 * μ + 2 * t))) := by
        apply exp_le_exp.2
        have := exp_neg_sub_one_le h0 h1
        nlinarith [mul_le_mul_of_nonneg_left this hμ]

lemma one_add_pow_le_exp {N : ℕ} {y : ℝ} (hy : -1 ≤ y) : (1 + y) ^ N ≤ exp (N * y) := by
  rw [exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp y]) N

section cnt
variable {T : Finset ι} {p : ℝ}

lemma mgf_cnt (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : ∀ i ∈ T, q i = p) (θ : ℝ) :
    E q (fun x => exp (θ * cnt T x)) ≤ exp (T.card * p * (exp θ - 1)) := by
  rw [E_exp_cnt hT, show 1 - p + p * exp θ = 1 + p * (exp θ - 1) by ring, mul_assoc]
  exact one_add_pow_le_exp (by nlinarith [exp_pos θ])

lemma mgf_cnt_compl (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : ∀ i ∈ T, q i = p) (θ : ℝ) :
    E q (fun x => exp (θ * ((T.card : ℝ) - cnt T x))) ≤
      exp (T.card * (1 - p) * (exp θ - 1)) := by
  have h : ∀ x, exp (θ * ((T.card : ℝ) - cnt T x)) = exp θ ^ T.card * exp (-θ * cnt T x) :=
    fun x => by rw [← exp_nat_mul, ← exp_add]; ring_nf
  rw [E_congr h, E_const_mul, E_exp_cnt hT, ← mul_pow]
  have h2 : exp θ * (1 - p + p * exp (-θ)) = 1 + (1 - p) * (exp θ - 1) := by
    have := exp_add θ (-θ); rw [add_neg_cancel, exp_zero] at this
    linear_combination (-p) * this
  rw [h2, mul_assoc]
  exact one_add_pow_le_exp (by nlinarith [exp_pos θ])

/-- `P[cnt ≥ Np + t] ≤ exp(-t²/(4Np + 2t))`. -/
lemma Pr_cnt_ge (hq : IsProb q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : ∀ i ∈ T, q i = p)
    {t : ℝ} (ht : 0 ≤ t) :
    Pr q (fun x => T.card * p + t ≤ cnt T x) ≤ exp (-(t ^ 2 / (4 * (T.card * p) + 2 * t))) :=
  tail_upper_of_mgf hq (by positivity) (fun θ _ _ => mgf_cnt hp0 hp1 hT θ) ht

/-- `P[cnt ≤ Np - t] ≤ exp(-t²/(4Np + 2t))`. -/
lemma Pr_cnt_le (hq : IsProb q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : ∀ i ∈ T, q i = p)
    {t : ℝ} (ht : 0 ≤ t) :
    Pr q (fun x => (cnt T x : ℝ) ≤ T.card * p - t) ≤ exp (-(t ^ 2 / (4 * (T.card * p) + 2 * t))) :=
  tail_lower_of_mgf hq (by positivity) (fun θ _ _ => mgf_cnt hp0 hp1 hT (-θ)) ht

/-- `P[cnt ≤ Np - t] ≤ exp(-t²/(4N(1-p) + 2t))` (via the complement count). -/
lemma Pr_cnt_le' (hq : IsProb q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : ∀ i ∈ T, q i = p)
    {t : ℝ} (ht : 0 ≤ t) :
    Pr q (fun x => (cnt T x : ℝ) ≤ T.card * p - t) ≤
      exp (-(t ^ 2 / (4 * (T.card * (1 - p)) + 2 * t))) := by
  have := tail_upper_of_mgf hq (F := fun x => (T.card : ℝ) - cnt T x) (μ := T.card * (1 - p))
    (by have := hp1; positivity) (fun θ _ _ => mgf_cnt_compl hp0 hp1 hT θ) ht
  refine le_trans (le_of_eq (Pr_congr fun x => ?_)) this
  constructor <;> intro h <;> linarith

/-- `P[cnt ≥ Np + t] ≤ exp(-t²/(4N(1-p) + 2t))` (via the complement count). -/
lemma Pr_cnt_ge' (hq : IsProb q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : ∀ i ∈ T, q i = p)
    {t : ℝ} (ht : 0 ≤ t) :
    Pr q (fun x => T.card * p + t ≤ cnt T x) ≤
      exp (-(t ^ 2 / (4 * (T.card * (1 - p)) + 2 * t))) := by
  have := tail_lower_of_mgf hq (F := fun x => (T.card : ℝ) - cnt T x) (μ := T.card * (1 - p))
    (by have := hp1; positivity) (fun θ _ _ => mgf_cnt_compl hp0 hp1 hT (-θ)) ht
  refine le_trans (le_of_eq (Pr_congr fun x => ?_)) this
  constructor <;> intro h <;> linarith

/-- Two-sided bound in terms of `ν = N · min(p, 1-p)`. -/
lemma Pr_cnt_abs_ge (hq : IsProb q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : ∀ i ∈ T, q i = p)
    {t : ℝ} (ht : 0 ≤ t) :
    Pr q (fun x => t ≤ |(cnt T x : ℝ) - T.card * p|) ≤
      2 * exp (-(t ^ 2 / (4 * (T.card * min p (1 - p)) + 2 * t))) := by
  have hsplit : Pr q (fun x => t ≤ |(cnt T x : ℝ) - T.card * p|) ≤
      Pr q (fun x => T.card * p + t ≤ cnt T x) + Pr q (fun x => (cnt T x : ℝ) ≤ T.card * p - t) := by
    refine le_trans (Pr_mono hq fun x hx => ?_) (Pr_or_le hq _ _)
    rcases le_abs'.1 hx with h | h
    · right; linarith
    · left; linarith
  by_cases hp : p ≤ 1 - p
  · rw [min_eq_left hp]
    linarith [Pr_cnt_ge hq hp0 hp1 hT ht, Pr_cnt_le hq hp0 hp1 hT ht]
  · rw [min_eq_right (le_of_not_ge hp)]
    linarith [Pr_cnt_ge' hq hp0 hp1 hT ht, Pr_cnt_le' hq hp0 hp1 hT ht]

end cnt

end MD
