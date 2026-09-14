import MajorityDynamics.Literature.FKMFormal.Chernoff
import MajorityDynamics.Literature.FKMFormal.Graph

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! # Lemma 4.1: the two graph properties used in the last two rounds, and Lemma 3.1. -/

namespace MD

open Finset Real

variable {n : ℕ} {p : ℝ}

/-- Property (i): for every set `N` with `|N| ≤ n/10`, fewer than `w` vertices see at least as
many neighbours inside `N` as outside. -/
def P1 (n w : ℕ) (x : Ω n) : Prop := ∀ N : Finset (Fin n), 10 * N.card ≤ n →
  (univ.filter fun v => cnt (star v (univ \ N)) x ≤ cnt (star v N) x).card < w

/-- Property (ii): minimum degree at least `2w`. -/
def P2 (n w : ℕ) (x : Ω n) : Prop := ∀ v : Fin n, 2 * w ≤ cnt (star v univ) x

section cnt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [DecidableEq κ]

lemma cnt_biUnion (s : Finset κ) (f : κ → Finset ι) (h : (s : Set κ).PairwiseDisjoint f)
    (x : ι → Bool) : cnt (s.biUnion f) x = ∑ v ∈ s, cnt (f v) x := by
  unfold cnt
  rw [filter_biUnion, card_biUnion]
  intro a ha b hb hab
  exact disjoint_filter_filter (h ha hb hab)

end cnt

lemma stars_pairwiseDisjoint (W B : Finset (Fin n)) (h : Disjoint W B) :
    (W : Set (Fin n)).PairwiseDisjoint fun v => star v B :=
  fun _v hv _ _ hne => star_disjoint_of_ne hne (disjoint_left.1 h hv)

lemma card_biUnion_star (W B : Finset (Fin n)) (h : Disjoint W B) :
    (W.biUnion fun v => star v B).card = W.card * B.card := by
  rw [card_biUnion fun a ha b hb hab => stars_pairwiseDisjoint W B h ha hb hab]
  rw [sum_congr rfl fun v hv => by
    rw [card_star, erase_eq_of_notMem (disjoint_left.1 h hv)]]
  rw [sum_const, smul_eq_mul]

/-- If every `v ∈ W` sees at least as many neighbours in `N` as outside, then the edges from `W`
to `Nᶜ \ W` are outnumbered by the edges from `W` to `N \ W` plus `|W|²`. -/
lemma cnt_le_of_bad (x : Ω n) (W N : Finset (Fin n))
    (h : ∀ v ∈ W, cnt (star v (univ \ N)) x ≤ cnt (star v N) x) :
    cnt (W.biUnion fun v => star v ((univ \ N) \ W)) x ≤
      cnt (W.biUnion fun v => star v (N \ W)) x + W.card * W.card := by
  rw [cnt_biUnion _ _ (stars_pairwiseDisjoint W _ disjoint_sdiff),
    cnt_biUnion _ _ (stars_pairwiseDisjoint W _ disjoint_sdiff)]
  calc ∑ v ∈ W, cnt (star v ((univ \ N) \ W)) x ≤ ∑ v ∈ W, cnt (star v N) x :=
        sum_le_sum fun v hv => (cnt_mono (star_subset sdiff_subset) x).trans (h v hv)
    _ ≤ ∑ v ∈ W, (cnt (star v (N \ W)) x + W.card) := sum_le_sum fun v _ => by
        have hsub : star v N ⊆ star v (N \ W) ∪ star v (N ∩ W) := by
          rw [← star_union, sdiff_union_inter]
        refine (cnt_mono hsub x).trans ((cnt_union_le _ _ _).trans (add_le_add le_rfl ?_))
        exact (cnt_le _ _).trans ((card_star_le _ _).trans (card_le_card inter_subset_right))
    _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]

lemma q_biUnion_star (p : ℝ) (W B : Finset (Fin n)) :
    ∀ i ∈ W.biUnion fun v => star v B, q n p i = p := by
  intro i hi
  obtain ⟨v, -, hv⟩ := mem_biUnion.1 hi
  exact q_star p v B i hv

lemma exp_bound_aux {m a t : ℝ} (hm : 0 ≤ m) (ha0 : 0 ≤ a) (ha : a ≤ m) (ht : 2 / 5 * m ≤ t) :
    m / 30 ≤ t ^ 2 / (4 * a + 2 * t) := by
  rcases hm.lt_or_eq with hm | hm
  · rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ t - 2 / 5 * m) (by linarith : 0 ≤ 30 * t + 10 * m)]
  · rw [← hm, zero_div]; exact div_nonneg (sq_nonneg _) (by linarith)

lemma exp_bound_aux' {m a t : ℝ} (hm : 0 ≤ m) (ha0 : 0 ≤ a) (ha : a ≤ m / 10)
    (ht : 3 / 10 * m ≤ t) : m / 30 ≤ t ^ 2 / (4 * a + 2 * t) := by
  rcases hm.lt_or_eq with hm | hm
  · rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ t - 3 / 10 * m) (by linarith : 0 ≤ 30 * t + 10 * m)]
  · rw [← hm, zero_div]; exact div_nonneg (sq_nonneg _) (by linarith)

/-- For fixed `W` (of size `w`) and small `N`, the bad event has probability `≤ 2 exp(-wnp/30)`. -/
lemma Pr_bad_WN_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {w : ℕ} (W N : Finset (Fin n))
    (hW : W.card = w) (hN : 10 * N.card ≤ n) (hwn : 20 * w ≤ n)
    (hwp : 20 * (w : ℝ) ≤ n * p) :
    Pr (q n p) (fun x => ∀ v ∈ W, cnt (star v (univ \ N)) x ≤ cnt (star v N) x) ≤
      2 * exp (-(w * n * p / 30)) := by
  have hq := isProb_q (n := n) hp0 hp1
  set U₁ := W.biUnion fun v => star v ((univ \ N) \ W)
  set U₂ := W.biUnion fun v => star v (N \ W)
  set m : ℝ := w * n
  have hm : 0 ≤ m := by positivity
  have hU₁ : U₁.card = w * ((univ \ N) \ W).card := by
    rw [card_biUnion_star W _ disjoint_sdiff, hW]
  have hU₂ : U₂.card = w * (N \ W).card := by
    rw [card_biUnion_star W _ disjoint_sdiff, hW]
  have hc₁ : ((univ \ N) \ W).card + N.card + W.card ≥ n := by
    have h1 := card_le_card_sdiff_add_card (s := univ \ N) (t := W)
    have h2 : (univ \ N).card + N.card = n := by
      rw [card_sdiff_add_card_eq_card (subset_univ N), card_univ, Fintype.card_fin]
    omega
  have hU₁lo : 17 / 20 * m * p ≤ U₁.card * p := by
    apply mul_le_mul_of_nonneg_right _ hp0
    rw [hU₁]; push_cast
    have : (17 : ℝ) / 20 * n ≤ ((univ \ N) \ W).card := by
      have h1 : ((N.card : ℝ) * 10 ≤ n) := by exact_mod_cast (by omega : N.card * 10 ≤ n)
      have h2 : ((W.card : ℝ) * 20 ≤ n) := by rw [hW]; exact_mod_cast (by omega : w * 20 ≤ n)
      have h3 : (n : ℝ) ≤ ((univ \ N) \ W).card + N.card + W.card := by exact_mod_cast hc₁
      linarith
    simp only [m]; nlinarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  have hU₁hi : (U₁.card : ℝ) * p ≤ m * p := by
    apply mul_le_mul_of_nonneg_right _ hp0
    rw [hU₁]; push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (card_le_univ _).trans (Fintype.card_fin n).le)
      (Nat.cast_nonneg _)
  have hU₂hi : (U₂.card : ℝ) * p ≤ m / 10 * p := by
    apply mul_le_mul_of_nonneg_right _ hp0
    rw [hU₂]; push_cast
    have : ((N \ W).card : ℝ) ≤ n / 10 := by
      have h1 : (((N \ W).card : ℝ) ≤ N.card) := by exact_mod_cast card_le_card sdiff_subset
      have h2 : ((N.card : ℝ) * 10 ≤ n) := by exact_mod_cast (by omega : N.card * 10 ≤ n)
      linarith
    simp only [m]; nlinarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  have hww : (w : ℝ) * w ≤ m / 20 * p := by
    simp only [m]; nlinarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
  -- the bad event forces one of two large deviations
  have himp : ∀ x, (∀ v ∈ W, cnt (star v (univ \ N)) x ≤ cnt (star v N) x) →
      ((cnt U₁ x : ℝ) ≤ U₁.card * p - (U₁.card * p - 9 / 20 * m * p)) ∨
      (U₂.card * p + (2 / 5 * m * p - U₂.card * p) ≤ cnt U₂ x) := by
    intro x hx
    have := cnt_le_of_bad x W N hx
    rw [hW] at this
    have h' : (cnt U₁ x : ℝ) ≤ cnt U₂ x + w * w := by exact_mod_cast this
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    linarith [hcon.1, hcon.2]
  refine (Pr_mono hq himp).trans ((Pr_or_le hq _ _).trans ?_)
  have h₁ := Pr_cnt_le hq hp0 hp1 (q_biUnion_star p W ((univ \ N) \ W))
    (t := U₁.card * p - 9 / 20 * m * p) (by linarith)
  have h₂ := Pr_cnt_ge hq hp0 hp1 (q_biUnion_star p W (N \ W))
    (t := 2 / 5 * m * p - U₂.card * p) (by linarith)
  have hmp : 0 ≤ m * p := by positivity
  have e₁ : exp (-((U₁.card * p - 9 / 20 * m * p) ^ 2 /
      (4 * (U₁.card * p) + 2 * (U₁.card * p - 9 / 20 * m * p)))) ≤ exp (-(w * n * p / 30)) := by
    apply exp_le_exp.2; apply neg_le_neg
    have := exp_bound_aux (m := m * p) (a := U₁.card * p) (t := U₁.card * p - 9 / 20 * m * p)
      hmp (by positivity) hU₁hi (by linarith)
    simpa [m] using this
  have e₂ : exp (-((2 / 5 * m * p - U₂.card * p) ^ 2 /
      (4 * (U₂.card * p) + 2 * (2 / 5 * m * p - U₂.card * p)))) ≤ exp (-(w * n * p / 30)) := by
    apply exp_le_exp.2; apply neg_le_neg
    have := exp_bound_aux' (m := m * p) (a := U₂.card * p) (t := 2 / 5 * m * p - U₂.card * p)
      hmp (by positivity) (by linarith) (by linarith)
    simpa [m] using this
  linarith

lemma not_P1_imp {w : ℕ} (x : Ω n) (h : ¬ P1 n w x) :
    ∃ N ∈ (univ : Finset (Fin n)).powerset, ∃ W ∈ (univ : Finset (Fin n)).powerset,
      10 * N.card ≤ n ∧ W.card = w ∧ ∀ v ∈ W, cnt (star v (univ \ N)) x ≤ cnt (star v N) x := by
  unfold P1 at h
  push Not at h
  obtain ⟨N, hN, hcard⟩ := h
  obtain ⟨W, hW, hWc⟩ := exists_subset_card_eq hcard
  exact ⟨N, mem_powerset.2 (subset_univ _), W, mem_powerset.2 (subset_univ _), hN, hWc,
    fun v hv => (mem_filter.1 (hW hv)).2⟩

/-- Lemma 4.1 (i): `P[¬ P1] ≤ 4^n · 2 exp(-wnp/30)`. -/
theorem Pr_not_P1_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {w : ℕ} (hwn : 20 * w ≤ n)
    (hwp : 20 * (w : ℝ) ≤ n * p) :
    Pr (q n p) (fun x => ¬ P1 n w x) ≤ 4 ^ n * (2 * exp (-(w * n * p / 30))) := by
  have hq := isProb_q (n := n) hp0 hp1
  refine (Pr_mono hq fun x => not_P1_imp x).trans ((Pr_exists_le hq _ _).trans ?_)
  have hB : ∀ N ∈ (univ : Finset (Fin n)).powerset,
      Pr (q n p) (fun x => ∃ W ∈ (univ : Finset (Fin n)).powerset,
        10 * N.card ≤ n ∧ W.card = w ∧ ∀ v ∈ W, cnt (star v (univ \ N)) x ≤ cnt (star v N) x) ≤
      2 ^ n * (2 * exp (-(w * n * p / 30))) := by
    intro N _
    refine (Pr_exists_le hq _ _).trans ?_
    have : ∀ W ∈ (univ : Finset (Fin n)).powerset,
        Pr (q n p) (fun x => 10 * N.card ≤ n ∧ W.card = w ∧
          ∀ v ∈ W, cnt (star v (univ \ N)) x ≤ cnt (star v N) x) ≤
        2 * exp (-(w * n * p / 30)) := by
      intro W _
      by_cases hc : 10 * N.card ≤ n ∧ W.card = w
      · refine le_trans (le_of_eq (Pr_congr fun x => ?_)) (Pr_bad_WN_le hp0 hp1 W N hc.2 hc.1 hwn hwp)
        exact ⟨fun h => h.2.2, fun h => ⟨hc.1, hc.2, h⟩⟩
      · refine le_trans (le_of_eq (Pr_congr (B := fun _ => False) fun x => ?_)) ?_
        · exact ⟨fun h => hc ⟨h.1, h.2.1⟩, fun h => h.elim⟩
        · rw [Pr_eq_E]; simp only [if_false, E_const]; positivity
    refine (sum_le_sum this).trans ?_
    rw [sum_const, card_powerset, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; rfl
  refine (sum_le_sum hB).trans ?_
  rw [sum_const, card_powerset, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
  rw [← mul_assoc, ← mul_pow]; norm_num

/-- Lemma 4.1 (ii): `P[¬ P2] ≤ n · exp(-(n-1)p/20)`. -/
theorem Pr_not_P2_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {w : ℕ} (hn : 1 ≤ n)
    (hw : 4 * (w : ℝ) ≤ (n - 1) * p) :
    Pr (q n p) (fun x => ¬ P2 n w x) ≤ n * exp (-((n - 1) * p / 20)) := by
  have hq := isProb_q (n := n) hp0 hp1
  have himp : ∀ x, ¬ P2 n w x → ∃ v ∈ (univ : Finset (Fin n)),
      (cnt (star v univ) x : ℝ) ≤ (star v univ).card * p - ((n - 1) * p - 2 * w) := by
    intro x hx
    unfold P2 at hx; push Not at hx
    obtain ⟨v, hv⟩ := hx
    refine ⟨v, mem_univ _, ?_⟩
    rw [card_star, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have : (cnt (star v univ) x : ℝ) + 1 ≤ 2 * w := by exact_mod_cast hv
    rw [Nat.cast_sub hn]; push_cast; linarith
  refine (Pr_mono hq himp).trans ((Pr_exists_le hq _ _).trans ?_)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 ≤ ((n : ℝ) - 1) * p := by have := hp0; nlinarith
  have : ∀ v ∈ (univ : Finset (Fin n)),
      Pr (q n p) (fun x => (cnt (star v univ) x : ℝ) ≤ (star v univ).card * p - ((n - 1) * p - 2 * w))
        ≤ exp (-((n - 1) * p / 20)) := by
    intro v _
    refine (Pr_cnt_le hq hp0 hp1 (q_star p v univ) (t := (n - 1) * p - 2 * w) (by linarith)).trans ?_
    apply exp_le_exp.2; apply neg_le_neg
    rw [card_star, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.cast_sub hn]
    push_cast
    set D := ((n : ℝ) - 1) * p
    set t := D - 2 * w
    have ht : D / 2 ≤ t := by simp only [t]; linarith
    rcases hD.lt_or_eq with hD' | hD'
    · rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (by linarith : 0 ≤ t - D / 2) (by linarith : 0 ≤ 20 * t + 10 * D)]
    · rw [← hD', zero_div]; exact div_nonneg (sq_nonneg _) (by linarith)
  refine (sum_le_sum this).trans ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Lemma 3.1: the initial majority is rarely tiny -/

/-- Coordinates of the initial states. -/
def Vc (n : ℕ) : Finset (Fin n ⊕ Edge n) := univ.image Sum.inl

lemma card_Vc : (Vc n).card = n := by
  rw [Vc, card_image_of_injective _ Sum.inl_injective, card_univ, Fintype.card_fin]

lemma q_Vc (p : ℝ) : ∀ i ∈ Vc n, q n p i = 1 / 2 := by
  intro i hi
  obtain ⟨v, -, rfl⟩ := mem_image.1 hi
  rfl

lemma inr_not_mem_Vc (e : Edge n) : Sum.inr e ∉ Vc n := by
  simp [Vc]

lemma inl_mem_Vc (v : Fin n) : Sum.inl v ∈ Vc n := mem_image_of_mem _ (mem_univ v)

lemma cnt_Vc (x : Ω n) : cnt (Vc n) x = (sset (init x) true).card := by
  unfold cnt Vc sset
  rw [filter_image]
  exact card_image_of_injective _ Sum.inl_injective

lemma sum_val (s : Fin n → Bool) :
    (∑ v, val (s v)) = ((sset s true).card : ℤ) - (sset s false).card := by
  rw [← sum_filter_add_sum_filter_not univ (fun v => s v = true)]
  have h1 : ∀ v ∈ univ.filter (fun v => s v = true), val (s v) = 1 := fun v hv => by
    simp [val, (mem_filter.1 hv).2]
  have h2 : ∀ v ∈ univ.filter (fun v => ¬ s v = true), val (s v) = -1 := fun v hv => by
    have := (mem_filter.1 hv).2; simp only [Bool.not_eq_true] at this; simp [val, this]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_const, sum_const]
  simp [sset, sub_eq_add_neg]

lemma tot_eq (x : Ω n) :
    tot x = ((sset (init x) true).card : ℤ) - (sset (init x) false).card := sum_val _

lemma tot_eq_cnt (x : Ω n) : tot x = 2 * (cnt (Vc n) x : ℤ) - n := by
  rw [tot_eq, cnt_Vc]
  have := card_sset_add (init x)
  omega

lemma sd_half (n : ℕ) : sd n (1 / 2) = √n / 2 := by
  unfold sd
  rw [show (n : ℝ) * (1 / 2) * (1 - 1 / 2) = (√n / 2) ^ 2 by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring, Real.sqrt_sq (by positivity)]

/-- Lemma 3.1: `P[|∑ S₀| < 2c√n] ≤ (2c√n + 1) · 2e⁶/√n`. -/
theorem Pr_tot_small_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 144 ≤ n) {c : ℝ} (hc : 0 ≤ c) :
    Pr (q n p) (fun x => |(tot x : ℝ)| < 2 * c * √n) ≤ (2 * (c * √n) + 1) * (exp 6 / (√n / 2)) := by
  classical
  have hq := isProb_q (n := n) hp0 hp1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hσ : 6 ≤ sd n (1 / 2) := by
    rw [sd_half]
    have : (12 : ℝ) ≤ √n := by
      rw [show (12 : ℝ) = √144 by rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    linarith
  set Wd := (range (n + 1)).filter fun k : ℕ => |(k : ℝ) - n * (1 / 2)| < c * √n with hWd
  have himp : ∀ x, |(tot x : ℝ)| < 2 * c * √n → ∃ k ∈ Wd, cnt (Vc n) x = k := by
    intro x hx
    refine ⟨cnt (Vc n) x, ?_, rfl⟩
    rw [hWd, mem_filter, mem_range]
    refine ⟨Nat.lt_succ_of_le ((cnt_le _ _).trans card_Vc.le), ?_⟩
    have h : (tot x : ℝ) = 2 * (cnt (Vc n) x : ℝ) - n := by
      have := tot_eq_cnt x; exact_mod_cast this
    rw [h] at hx
    rw [abs_lt] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  refine (Pr_mono hq himp).trans ((Pr_exists_le hq _ _).trans ?_)
  have hb : ∀ k ∈ Wd, Pr (q n p) (fun x => cnt (Vc n) x = k) ≤ exp 6 / (√n / 2) := by
    intro k _
    rw [Pr_cnt_eq (q_Vc p) k, card_Vc, ← sd_half]
    exact bin_le (by norm_num) (by norm_num) hσ
  refine (sum_le_sum hb).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_filter_abs_lt (n + 1) _ _ (by positivity)) (by positivity)

end MD
