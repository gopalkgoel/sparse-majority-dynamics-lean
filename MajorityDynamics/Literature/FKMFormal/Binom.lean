import MajorityDynamics.Literature.FKMFormal.Prob

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! # Binomial point masses: elementary local estimates

`bin N k p ≤ e^6 / σ` everywhere and `bin N k p ≥ c(R)/σ` for `|k - Np| ≤ Rσ`,
where `σ² = Np(1-p)`. Proved from the pmf ratio `bin (k+1) / bin k = (N-k)p / ((k+1)(1-p))`. -/

namespace MD

open Finset Real

/-! ### Basic facts -/

lemma bin_nonneg {N k : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bin N k p := by
  unfold bin
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma bin_pos {N k : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hk : k ≤ N) : 0 < bin N k p := by
  unfold bin
  have : 0 < 1 - p := by linarith
  have := Nat.choose_pos hk
  positivity

lemma bin_eq_zero {N k : ℕ} {p : ℝ} (hk : N < k) : bin N k p = 0 := by
  simp [bin, Nat.choose_eq_zero_of_lt hk]

lemma sum_bin (N : ℕ) (p : ℝ) : ∑ k ∈ range (N + 1), bin N k p = 1 := by
  have h := add_pow p (1 - p) N
  rw [add_sub_cancel, one_pow] at h
  rw [h]
  exact sum_congr rfl fun k _ => by unfold bin; ring

lemma bin_symm {N k : ℕ} {p : ℝ} (hk : k ≤ N) : bin N k p = bin N (N - k) (1 - p) := by
  unfold bin
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk, sub_sub_cancel]
  ring

/-- The pmf ratio identity. -/
lemma bin_ratio {N k : ℕ} {p : ℝ} (hk : k < N) :
    bin N (k + 1) p * ((k + 1) * (1 - p)) = bin N k p * (((N : ℝ) - k) * p) := by
  unfold bin
  have h := Nat.choose_succ_right_eq N k
  have hc : ((N.choose (k + 1) : ℕ) : ℝ) * (k + 1) = N.choose k * ((N : ℝ) - k) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) h
    push_cast [Nat.cast_sub hk.le] at this
    exact this
  have e : N - k = (N - (k + 1)) + 1 := by omega
  rw [e, pow_succ, pow_succ]
  linear_combination (p ^ k * p * (1 - p) ^ (N - (k + 1)) * (1 - p)) * hc

/-! ### Chains of ratio bounds -/

lemma chain_up {f : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {a b : ℕ}
    (h : ∀ k, a ≤ k → k < b → ρ * f k ≤ f (k + 1)) :
    ∀ j, a + j ≤ b → ρ ^ j * f a ≤ f (a + j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    calc ρ ^ (j + 1) * f a = ρ * (ρ ^ j * f a) := by ring
      _ ≤ ρ * f (a + j) := mul_le_mul_of_nonneg_left h1 hρ
      _ ≤ f (a + j + 1) := h (a + j) (by omega) (by omega)

lemma chain_down {f : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {a b : ℕ}
    (h : ∀ k, a ≤ k → k < b → ρ * f (k + 1) ≤ f k) :
    ∀ j, a + j ≤ b → ρ ^ j * f (a + j) ≤ f a := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    calc ρ ^ (j + 1) * f (a + (j + 1)) = ρ ^ j * (ρ * f (a + j + 1)) := by ring_nf
      _ ≤ ρ ^ j * f (a + j) :=
          mul_le_mul_of_nonneg_left (h (a + j) (by omega) (by omega)) (by positivity)
      _ ≤ f a := h1

/-- Two-sided chain: all values on `[a, b]` are within a factor `ρ ^ (b - a)` of each other. -/
lemma chain_two_sided {f : ℕ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {a b : ℕ}
    (hf : ∀ k, 0 ≤ f k)
    (hup : ∀ k, a ≤ k → k < b → ρ * f k ≤ f (k + 1))
    (hdown : ∀ k, a ≤ k → k < b → ρ * f (k + 1) ≤ f k) :
    ∀ i k, a ≤ i → i ≤ b → a ≤ k → k ≤ b → ρ ^ (b - a) * f k ≤ f i := by
  intro i k hai hib hak hkb
  rcases le_total k i with hki | hik
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    have := chain_up hρ0 (a := k) (b := b) (fun m hm hmb => hup m (le_trans hak hm) hmb) j hib
    calc ρ ^ (b - a) * f k ≤ ρ ^ j * f k :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ0 hρ1 (by omega)) (hf k)
      _ ≤ f (k + j) := this
  · obtain ⟨j, rfl⟩ : ∃ j, k = i + j := ⟨k - i, by omega⟩
    have := chain_down hρ0 (a := i) (b := b) (fun m hm hmb => hdown m (le_trans hai hm) hmb) j hkb
    calc ρ ^ (b - a) * f (i + j) ≤ ρ ^ j * f (i + j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ0 hρ1 (by omega)) (hf _)
      _ ≤ f i := this

/-! ### Elementary exponential bounds -/

lemma exp_neg_two_mul_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : exp (-(2 * x)) ≤ 1 - x := by
  have h1 := add_one_le_exp (2 * x)
  rw [exp_neg]
  calc (exp (2 * x))⁻¹ ≤ (1 + 2 * x)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    _ ≤ 1 - x := by
        rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; nlinarith

lemma exp_neg_le_inv_add_one {x : ℝ} (hx0 : 0 ≤ x) : exp (-x) ≤ (1 + x)⁻¹ := by
  rw [exp_neg]
  exact inv_anti₀ (by linarith) (by linarith [add_one_le_exp x])

/-- Integers in an open window of radius `t` number at most `2t + 1`. -/
lemma card_filter_abs_lt (M : ℕ) (μ t : ℝ) (ht : 0 ≤ t) :
    (((range M).filter fun k : ℕ => |(k : ℝ) - μ| < t).card : ℝ) ≤ 2 * t + 1 := by
  by_cases hne : ((range M).filter fun k : ℕ => |(k : ℝ) - μ| < t) = ∅
  · rw [hne]; simp; linarith
  obtain ⟨k₀, hk₀⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hμt : 0 ≤ μ + t := by
    simp only [mem_filter, mem_range] at hk₀
    have := abs_lt.1 hk₀.2
    linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀)]
  have hsub : ((range M).filter fun k : ℕ => |(k : ℝ) - μ| < t) ⊆
      Finset.Ico ⌈μ - t⌉₊ (⌊μ + t⌋₊ + 1) := by
    intro k hk
    simp only [mem_filter, mem_range] at hk
    have := abs_lt.1 hk.2
    simp only [Finset.mem_Ico]
    constructor
    · exact Nat.ceil_le.2 (by linarith)
    · exact Nat.lt_succ_of_le ((Nat.le_floor_iff hμt).2 (by linarith))
  have hcard := card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have h1 : (⌈μ - t⌉₊ : ℝ) ≥ μ - t := Nat.le_ceil _
  have h2 : (⌊μ + t⌋₊ : ℝ) ≤ μ + t := Nat.floor_le hμt
  have h3 : ((⌊μ + t⌋₊ + 1 - ⌈μ - t⌉₊ : ℕ) : ℝ) ≤ 2 * t + 1 := by
    rcases le_or_gt ⌈μ - t⌉₊ (⌊μ + t⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
  exact le_trans (by exact_mod_cast hcard) h3

/-! ### Point-mass upper bound -/

/-- Standard deviation of `Bin(N,p)`. -/
noncomputable def sd (N : ℕ) (p : ℝ) : ℝ := √(N * p * (1 - p))

lemma sd_sq {N : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : sd N p ^ 2 = N * p * (1 - p) := by
  unfold sd
  rw [sq_sqrt]
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma sd_nonneg (N : ℕ) (p : ℝ) : 0 ≤ sd N p := sqrt_nonneg _

lemma sd_symm (N : ℕ) (p : ℝ) : sd N (1 - p) = sd N p := by
  unfold sd; congr 1; ring

/-- Ratio lower bound to the right of the mean: for `Np ≤ i + 1` and `i ≤ Np + σ`,
`bin (i+1) ≥ (1 - 3/σ) bin i`. -/
lemma bin_ratio_right {N i : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hσ : 2 ≤ sd N p)
    (hiN : i < N) (hi1 : (N : ℝ) * p ≤ i + 1) (hi2 : (i : ℝ) ≤ N * p + sd N p) :
    (1 - 3 / sd N p) * bin N i p ≤ bin N (i + 1) p := by
  set σ := sd N p with hσdef
  have hσpos : 0 < σ := by linarith
  have hσ2 : σ ^ 2 = N * p * (1 - p) := sd_sq h0.le h1.le
  have hq : 0 < 1 - p := by linarith
  have hden : 0 < ((i : ℝ) + 1) * (1 - p) := by positivity
  have hr := bin_ratio (p := p) hiN
  have hb := bin_nonneg (N := N) (k := i) h0.le h1.le
  have key : (1 - 3 / σ) * (((i : ℝ) + 1) * (1 - p)) ≤ ((N : ℝ) - i) * p := by
    have e1 : ((i : ℝ) + 1) * (1 - p) - ((N : ℝ) - i) * p = (i : ℝ) + 1 - p - N * p := by ring
    have e2 : σ ^ 2 ≤ ((i : ℝ) + 1) * (1 - p) := by
      rw [hσ2]; nlinarith
    have e3 : (i : ℝ) + 1 - p - N * p ≤ σ + 1 := by linarith
    have e4 : σ + 1 ≤ (3 / σ) * σ ^ 2 := by
      have : (3 / σ) * σ ^ 2 = 3 * σ := by field_simp
      rw [this]; linarith
    have e5 : (3 / σ) * σ ^ 2 ≤ (3 / σ) * (((i : ℝ) + 1) * (1 - p)) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  have := mul_le_mul_of_nonneg_right key hb
  calc (1 - 3 / σ) * bin N i p
      = ((1 - 3 / σ) * (((i : ℝ) + 1) * (1 - p)) * bin N i p) / (((i : ℝ) + 1) * (1 - p)) := by
        field_simp
    _ ≤ (((N : ℝ) - i) * p * bin N i p) / (((i : ℝ) + 1) * (1 - p)) := by
        gcongr
    _ = bin N (i + 1) p := by
        rw [div_eq_iff hden.ne', mul_comm (((N : ℝ) - i) * p), ← hr]

/-- Below the mean the pmf is nondecreasing. -/
lemma bin_mono_left {N i : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hiN : i < N)
    (hi : (i : ℝ) + 1 ≤ N * p) : bin N i p ≤ bin N (i + 1) p := by
  have hr := bin_ratio (p := p) hiN
  have hq : 0 < 1 - p := by linarith
  have hden : 0 < ((i : ℝ) + 1) * (1 - p) := by positivity
  have hb := bin_nonneg (N := N) (k := i) h0.le h1.le
  have key : ((i : ℝ) + 1) * (1 - p) ≤ ((N : ℝ) - i) * p := by nlinarith
  have := mul_le_mul_of_nonneg_left key hb
  calc bin N i p = bin N i p * (((i : ℝ) + 1) * (1 - p)) / (((i : ℝ) + 1) * (1 - p)) := by
        field_simp
    _ ≤ bin N i p * (((N : ℝ) - i) * p) / (((i : ℝ) + 1) * (1 - p)) := by gcongr
    _ = bin N (i + 1) p := by rw [← hr]; field_simp

/-- Point-mass bound at a point `k₀ ∈ [Np - 1, Np + 1]`. -/
lemma bin_le_of_near {N k₀ : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hσ : 6 ≤ sd N p)
    (hk1 : (N : ℝ) * p - 1 ≤ k₀) (hk2 : (k₀ : ℝ) ≤ N * p + 1) :
    bin N k₀ p ≤ exp 6 / sd N p := by
  set σ := sd N p with hσdef
  have hσpos : 0 < σ := by linarith
  have hσ2 : σ ^ 2 = N * p * (1 - p) := sd_sq h0.le h1.le
  have hq : 0 < 1 - p := by linarith
  have hNq : σ ^ 2 ≤ N * (1 - p) := by rw [hσ2]; nlinarith
  have hwin : (k₀ : ℝ) + σ ≤ N := by nlinarith
  set J := ⌊σ⌋₊ with hJ
  have hJσ : (J : ℝ) ≤ σ := Nat.floor_le hσpos.le
  have hJσ' : σ < J + 1 := Nat.lt_floor_add_one σ
  have hJN : k₀ + J ≤ N := by
    have : ((k₀ + J : ℕ) : ℝ) ≤ N := by push_cast; linarith
    exact_mod_cast this
  set ρ := 1 - 3 / σ with hρ
  have h3σ : 3 / σ ≤ 1 / 2 := by rw [div_le_iff₀ hσpos]; linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  have hρexp : exp (-(6 / σ)) ≤ ρ := by
    have := exp_neg_two_mul_le (x := 3 / σ) (by positivity) h3σ
    rwa [show 2 * (3 / σ) = 6 / σ by ring] at this
  have hchain : ∀ j, j ≤ J → exp (-6) * bin N k₀ p ≤ bin N (k₀ + j) p := by
    intro j hj
    have h1' := chain_up hρ0 (f := fun k => bin N k p) (a := k₀) (b := k₀ + J)
      (fun i hi hiJ => by
        apply bin_ratio_right h0 h1 (by linarith) (by omega)
        · have : (k₀ : ℝ) ≤ i := by exact_mod_cast hi
          linarith
        · have : ((i + 1 : ℕ) : ℝ) ≤ k₀ + J := by exact_mod_cast hiJ
          push_cast at this; linarith) j (by omega)
    refine le_trans ?_ h1'
    apply mul_le_mul_of_nonneg_right _ (bin_nonneg h0.le h1.le)
    calc exp (-6) = exp (-(6 / σ)) ^ J * exp (-(6 / σ) * (σ - J)) := by
          rw [← exp_nat_mul, ← exp_add]; congr 1; field_simp; ring
      _ ≤ ρ ^ J * 1 := by
          gcongr
          · exact exp_le_one_iff.2 (by nlinarith [div_pos (by norm_num : (0:ℝ) < 6) hσpos])
      _ ≤ ρ ^ j := by
          rw [mul_one]
          exact pow_le_pow_of_le_one hρ0 (by rw [hρ]; linarith [div_pos (by norm_num : (0:ℝ) < 3) hσpos]) hj
  have hsum : ∑ j ∈ range (J + 1), bin N (k₀ + j) p ≤ 1 := by
    rw [← sum_bin N p]
    have himg : (range (J + 1)).image (fun j => k₀ + j) ⊆ range (N + 1) := by
      intro m hm
      simp only [mem_image, mem_range] at hm ⊢
      obtain ⟨j, hj, rfl⟩ := hm; omega
    rw [← sum_image (f := fun k => bin N k p) (fun a _ b _ h => by simpa using h)]
    exact sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => bin_nonneg h0.le h1.le
  have hlow : ((J : ℝ) + 1) * (exp (-6) * bin N k₀ p) ≤ ∑ j ∈ range (J + 1), bin N (k₀ + j) p := by
    have : ∑ j ∈ range (J + 1), exp (-6) * bin N k₀ p ≤ ∑ j ∈ range (J + 1), bin N (k₀ + j) p :=
      sum_le_sum fun j hj => hchain j (by simpa [Nat.lt_succ_iff] using hj)
    simpa [sum_const, card_range] using this
  have hb := bin_nonneg (N := N) (k := k₀) h0.le h1.le
  have : σ * (exp (-6) * bin N k₀ p) ≤ 1 := by
    calc σ * (exp (-6) * bin N k₀ p) ≤ ((J : ℝ) + 1) * (exp (-6) * bin N k₀ p) := by
          gcongr
      _ ≤ 1 := le_trans hlow hsum
  rw [le_div_iff₀ hσpos]
  have he : exp (-6) * exp 6 = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (-6), exp_pos 6]

/-- Point-mass bound for `k ≤ Np + 1`. -/
lemma bin_le_of_le {N k : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hσ : 6 ≤ sd N p)
    (hk : (k : ℝ) ≤ N * p + 1) : bin N k p ≤ exp 6 / sd N p := by
  rcases le_or_gt ((N : ℝ) * p - 1) k with h | h
  · exact bin_le_of_near h0 h1 hσ h hk
  · set k₁ := ⌈(N : ℝ) * p - 1⌉₊ with hk₁
    have hpos : 0 ≤ (N : ℝ) * p - 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hk₁1 : (N : ℝ) * p - 1 ≤ k₁ := Nat.le_ceil _
    have hk₁2 : (k₁ : ℝ) < N * p - 1 + 1 := Nat.ceil_lt_add_one hpos
    have hkk₁ : k < k₁ := by
      have : (k : ℝ) < k₁ := by linarith
      exact_mod_cast this
    have hk₁N : k₁ ≤ N := by
      have : (k₁ : ℝ) ≤ N := by nlinarith
      exact_mod_cast this
    have hmono := chain_up (ρ := 1) zero_le_one (f := fun k => bin N k p) (a := k) (b := k₁)
      (fun i hi hik₁ => by
        rw [one_mul]
        apply bin_mono_left h0 h1 (by omega)
        have : ((i + 1 : ℕ) : ℝ) ≤ k₁ := by exact_mod_cast hik₁
        push_cast at this; linarith) (k₁ - k) (by omega)
    rw [one_pow, one_mul, Nat.add_sub_cancel' hkk₁.le] at hmono
    exact le_trans hmono (bin_le_of_near h0 h1 hσ hk₁1 (by linarith))

/-- **Point-mass upper bound**: `bin N k p ≤ e^6 / σ` when `σ ≥ 6`. -/
theorem bin_le {N k : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hσ : 6 ≤ sd N p) :
    bin N k p ≤ exp 6 / sd N p := by
  rcases le_or_gt ((k : ℝ)) (N * p + 1) with h | h
  · exact bin_le_of_le h0 h1 hσ h
  rcases le_or_gt k N with hkN | hkN
  · rw [bin_symm hkN, ← sd_symm]
    apply bin_le_of_le (by linarith) (by linarith) (by rwa [sd_symm])
    rw [Nat.cast_sub hkN]; nlinarith
  · rw [bin_eq_zero hkN]
    exact div_nonneg (exp_pos _).le (sd_nonneg _ _)

/-! ### Bulk lower bound -/

/-- Chebyshev for the binomial: mass within `2σ` of the mean is at least `3/4`. -/
lemma sum_bin_window {N : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hσ : 0 < sd N p) :
    3 / 4 ≤ ∑ k ∈ (range (N + 1)).filter (fun k : ℕ => |(k : ℝ) - N * p| < 2 * sd N p), bin N k p := by
  classical
  set q : Fin N → ℝ := fun _ => p with hq
  have hqP : IsProb q := fun _ => ⟨h0, h1⟩
  have hmean : E q (fun x => (cnt univ x : ℝ)) = N * p := by
    rw [E_cnt_mean]; simp [hq]
  have hvar : Var q (fun x => (cnt univ x : ℝ)) = sd N p ^ 2 := by
    rw [Var_cnt, sd_sq h0 h1]; simp [hq]; ring
  have hcheb := Pr_abs_sub_le hqP (fun x => (cnt univ x : ℝ)) (t := 2 * sd N p) (by positivity)
  rw [hmean, hvar] at hcheb
  have hcheb' : Pr q (fun x => 2 * sd N p ≤ |(cnt univ x : ℝ) - N * p|) ≤ 1 / 4 := by
    refine le_trans hcheb (le_of_eq ?_)
    field_simp; ring
  have hnot := Pr_not (q := q) (fun x => 2 * sd N p ≤ |(cnt univ x : ℝ) - N * p|)
  have hPr : Pr q (fun x => ¬ 2 * sd N p ≤ |(cnt univ x : ℝ) - N * p|) =
      ∑ k ∈ (range (N + 1)).filter (fun k : ℕ => |(k : ℝ) - N * p| < 2 * sd N p), bin N k p := by
    rw [Pr_eq_E, E_cnt_fun (T := univ) (p := p) (fun _ _ => rfl)
      (fun k => if ¬ 2 * sd N p ≤ |(k : ℝ) - N * p| then 1 else 0)]
    rw [sum_filter, card_univ, Fintype.card_fin]
    refine sum_congr rfl fun k _ => ?_
    simp only [not_le]
    split_ifs <;> simp
  linarith

/-- Ratio bounds inside the window `|k - Np| ≤ Rσ`. -/
lemma bin_ratio_window {N k : ℕ} {p R : ℝ} (h0 : 0 < p) (h1 : p < 1) (hR : 2 ≤ R)
    (hσ : 4 * (R + 1) ≤ sd N p) (hkN : k < N) (hk : |(k : ℝ) - N * p| ≤ R * sd N p) :
    exp (-(4 * (R + 1) / sd N p)) * bin N k p ≤ bin N (k + 1) p ∧
    exp (-(4 * (R + 1) / sd N p)) * bin N (k + 1) p ≤ bin N k p := by
  set σ := sd N p with hσdef
  have hσpos : 0 < σ := by linarith
  have hσ2 : σ ^ 2 = N * p * (1 - p) := sd_sq h0.le h1.le
  have hq : 0 < 1 - p := by linarith
  have hr := bin_ratio (p := p) hkN
  have hden : 0 < ((k : ℝ) + 1) * (1 - p) := by positivity
  have hb := bin_nonneg (N := N) (k := k) h0.le h1.le
  have hk' := abs_le.1 hk
  set x := 2 * (R + 1) / σ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx12 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ hσpos]; linarith
  have hRσ : R * σ ≤ N * p / 2 := by
    have : 2 * R * σ ≤ σ ^ 2 := by nlinarith
    nlinarith
  have hden2 : σ ^ 2 / 2 ≤ ((k : ℝ) + 1) * (1 - p) := by
    have : (N : ℝ) * p / 2 ≤ k + 1 := by linarith
    rw [hσ2]; nlinarith
  have hnum : |((N : ℝ) - k) * p - ((k : ℝ) + 1) * (1 - p)| ≤ R * σ + 1 := by
    have e : ((N : ℝ) - k) * p - ((k : ℝ) + 1) * (1 - p) = (N * p - k) - (1 - p) := by ring
    rw [e, abs_le]; constructor <;> nlinarith
  have hratio : |((N : ℝ) - k) * p / (((k : ℝ) + 1) * (1 - p)) - 1| ≤ x := by
    rw [div_sub_one hden.ne', abs_div, abs_of_pos hden, div_le_iff₀ hden]
    calc |((N : ℝ) - k) * p - ((k : ℝ) + 1) * (1 - p)| ≤ R * σ + 1 := hnum
      _ ≤ (R + 1) * σ := by nlinarith
      _ = x * (σ ^ 2 / 2) := by rw [hx]; field_simp
      _ ≤ x * (((k : ℝ) + 1) * (1 - p)) := mul_le_mul_of_nonneg_left hden2 hx0
  have hr' : bin N (k + 1) p = bin N k p * (((N : ℝ) - k) * p / (((k : ℝ) + 1) * (1 - p))) := by
    rw [← mul_div_assoc, ← hr]; field_simp
  have hρ : exp (-(4 * (R + 1) / σ)) = exp (-(2 * x)) := by
    congr 1; rw [hx]; field_simp; ring
  have hexp1 : exp (-(2 * x)) ≤ 1 - x := exp_neg_two_mul_le hx0 hx12
  have hexp2 : exp (-(2 * x)) ≤ (1 + x)⁻¹ := by
    calc exp (-(2 * x)) ≤ exp (-x) := exp_le_exp.2 (by linarith)
      _ ≤ (1 + x)⁻¹ := exp_neg_le_inv_add_one hx0
  have hlo : 1 - x ≤ ((N : ℝ) - k) * p / (((k : ℝ) + 1) * (1 - p)) := by
    linarith [(abs_le.1 hratio).1]
  have hhi : ((N : ℝ) - k) * p / (((k : ℝ) + 1) * (1 - p)) ≤ 1 + x := by
    linarith [(abs_le.1 hratio).2]
  rw [hρ]
  constructor
  · rw [hr']
    calc exp (-(2 * x)) * bin N k p ≤ (1 - x) * bin N k p := by gcongr
      _ = bin N k p * (1 - x) := by ring
      _ ≤ bin N k p * (((N : ℝ) - k) * p / (((k : ℝ) + 1) * (1 - p))) := by gcongr
  · rw [hr']
    calc exp (-(2 * x)) * (bin N k p * (((N : ℝ) - k) * p / (((k : ℝ) + 1) * (1 - p))))
        ≤ (1 + x)⁻¹ * (bin N k p * (1 + x)) := by
          have : 0 ≤ bin N k p * (((N : ℝ) - k) * p / (((k : ℝ) + 1) * (1 - p))) := by
            rw [← hr']; exact bin_nonneg h0.le h1.le
          gcongr
      _ = bin N k p := by field_simp

/-- **Bulk lower bound**: `bin N i p ≥ 3 e^{-8R(R+1)} / (20σ)` for `|i - Np| ≤ Rσ`. -/
theorem bin_ge {N i : ℕ} {p R : ℝ} (h0 : 0 < p) (h1 : p < 1) (hR : 2 ≤ R)
    (hσ : 4 * (R + 1) ≤ sd N p) (hi : |(i : ℝ) - N * p| ≤ R * sd N p) :
    3 * exp (-(8 * R * (R + 1))) / (20 * sd N p) ≤ bin N i p := by
  classical
  set σ := sd N p with hσdef
  have hσpos : 0 < σ := by linarith
  have hσ2 : σ ^ 2 = N * p * (1 - p) := sd_sq h0.le h1.le
  have hq : 0 < 1 - p := by linarith
  have hNq : σ ^ 2 ≤ N * (1 - p) := by rw [hσ2]; nlinarith
  have hNp : σ ^ 2 ≤ N * p := by rw [hσ2]; nlinarith
  set lo := ⌈(N : ℝ) * p - R * σ⌉₊ with hlo
  set hi' := ⌊(N : ℝ) * p + R * σ⌋₊ with hhi
  have hlo1 : (N : ℝ) * p - R * σ ≤ lo := Nat.le_ceil _
  have hlo2 : (lo : ℝ) < N * p - R * σ + 1 := Nat.ceil_lt_add_one (by nlinarith)
  have hhi1 : (hi' : ℝ) ≤ N * p + R * σ := Nat.floor_le (by positivity)
  have hhi2 : (N : ℝ) * p + R * σ < hi' + 1 := Nat.lt_floor_add_one _
  have hhiN : hi' < N := by
    have : (hi' : ℝ) < N := by nlinarith
    exact_mod_cast this
  set ρ := exp (-(4 * (R + 1) / σ)) with hρ
  have hρ0 : 0 ≤ ρ := (exp_pos _).le
  have hρ1 : ρ ≤ 1 := exp_le_one_iff.2 (by
    have : 0 ≤ 4 * (R + 1) / σ := by positivity
    linarith)
  have hwin : ∀ k, lo ≤ k → k ≤ hi' → |(k : ℝ) - N * p| ≤ R * σ := by
    intro k hk1 hk2
    have h1' : (lo : ℝ) ≤ k := by exact_mod_cast hk1
    have h2' : (k : ℝ) ≤ hi' := by exact_mod_cast hk2
    rw [abs_le]; constructor <;> linarith
  have hchain := chain_two_sided hρ0 hρ1 (f := fun k => bin N k p) (a := lo) (b := hi')
    (fun _ => bin_nonneg h0.le h1.le)
    (fun k hk1 hk2 => (bin_ratio_window h0 h1 hR hσ (by omega) (hwin k hk1 hk2.le)).1)
    (fun k hk1 hk2 => (bin_ratio_window h0 h1 hR hσ (by omega) (hwin k hk1 hk2.le)).2)
  have hρpow : exp (-(8 * R * (R + 1))) ≤ ρ ^ (hi' - lo) := by
    rw [hρ, ← exp_nat_mul]
    apply exp_le_exp.2
    have hd : ((hi' - lo : ℕ) : ℝ) ≤ 2 * R * σ := by
      rcases le_or_gt lo hi' with h | h
      · rw [Nat.cast_sub h]; linarith
      · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; positivity
    have : ((hi' - lo : ℕ) : ℝ) * (4 * (R + 1) / σ) ≤ 2 * R * σ * (4 * (R + 1) / σ) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    have e : 2 * R * σ * (4 * (R + 1) / σ) = 8 * R * (R + 1) := by field_simp; ring
    rw [e] at this; linarith
  have hi_mem : lo ≤ i ∧ i ≤ hi' := by
    have := abs_le.1 hi
    constructor
    · exact Nat.ceil_le.2 (by linarith)
    · exact (Nat.le_floor_iff (by positivity)).2 (by linarith)
  set W := (range (N + 1)).filter (fun k : ℕ => |(k : ℝ) - N * p| < 2 * σ) with hW
  have hWmem : ∀ k ∈ W, lo ≤ k ∧ k ≤ hi' := by
    intro k hk
    rw [hW, mem_filter] at hk
    have := abs_lt.1 hk.2
    constructor
    · exact Nat.ceil_le.2 (by nlinarith)
    · exact (Nat.le_floor_iff (by positivity)).2 (by nlinarith)
  have hcard : (W.card : ℝ) ≤ 5 * σ := by
    have := card_filter_abs_lt (N + 1) ((N : ℝ) * p) (2 * σ) (by positivity)
    rw [hW]; linarith
  have hlow : 3 / 4 ≤ ∑ k ∈ W, bin N k p := sum_bin_window h0.le h1.le hσpos
  have hup : ∑ k ∈ W, bin N k p ≤ W.card * (exp (8 * R * (R + 1)) * bin N i p) := by
    have : ∀ k ∈ W, bin N k p ≤ exp (8 * R * (R + 1)) * bin N i p := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := hWmem k hk
      have h := hchain i k hi_mem.1 hi_mem.2 hk1 hk2
      have h' := mul_le_mul_of_nonneg_right hρpow (bin_nonneg (N := N) (k := k) h0.le h1.le)
      have hee : exp (8 * R * (R + 1)) * exp (-(8 * R * (R + 1))) = 1 := by
        rw [← exp_add]; simp
      calc bin N k p = exp (8 * R * (R + 1)) * (exp (-(8 * R * (R + 1))) * bin N k p) := by
            rw [← mul_assoc, hee, one_mul]
        _ ≤ exp (8 * R * (R + 1)) * bin N i p := by
            gcongr; exact le_trans h' h
    calc ∑ k ∈ W, bin N k p ≤ ∑ _k ∈ W, exp (8 * R * (R + 1)) * bin N i p := sum_le_sum this
      _ = W.card * (exp (8 * R * (R + 1)) * bin N i p) := by rw [sum_const, nsmul_eq_mul]
  have hb := bin_nonneg (N := N) (k := i) h0.le h1.le
  have hE := exp_pos (8 * R * (R + 1))
  have hee : exp (-(8 * R * (R + 1))) * exp (8 * R * (R + 1)) = 1 := by rw [← exp_add]; simp
  have key : 3 / 4 ≤ 5 * σ * (exp (8 * R * (R + 1)) * bin N i p) := by
    calc (3 : ℝ) / 4 ≤ ∑ k ∈ W, bin N k p := hlow
      _ ≤ W.card * (exp (8 * R * (R + 1)) * bin N i p) := hup
      _ ≤ 5 * σ * (exp (8 * R * (R + 1)) * bin N i p) := by gcongr
  rw [div_le_iff₀ (by positivity)]
  nlinarith [exp_pos (-(8 * R * (R + 1)))]

end MD
