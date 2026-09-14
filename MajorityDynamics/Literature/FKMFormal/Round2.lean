import MajorityDynamics.Literature.FKMFormal.Graph

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! # The second round from a fixed initial state: second-moment analysis. -/

namespace MD

open Finset Real

variable {n : ℕ} {p : ℝ}

/-- Neighbour difference `#(nbrs in +1) - #(nbrs in -1)` of `u` in state `s₀`, ignoring `X`. -/
def Z (s₀ : Fin n → Bool) (u : Fin n) (X : Finset (Fin n)) (x : Ω n) : ℤ :=
  (cnt (star u (sset s₀ true \ X)) x : ℤ) - cnt (star u (sset s₀ false \ X)) x

lemma nsum_eq_Z (x : Ω n) (s₀ : Fin n → Bool) (u : Fin n) : nsum x s₀ u = Z s₀ u ∅ x := by
  simp [Z, nsum_eq_cnt]

lemma sdiff_erase_eq (A X : Finset (Fin n)) (v : Fin n) : (A \ X).erase v = A \ insert v X := by
  ext w; simp only [mem_erase, mem_sdiff, mem_insert, not_or]; tauto

lemma Z_update {u v : Fin n} (hv : v ≠ u) (s₀ : Fin n → Bool) (X : Finset (Fin n)) (x : Ω n)
    (b : Bool) :
    Z s₀ u X (Function.update x (edge u v) b) =
      Z s₀ u (insert v X) x + if v ∉ X ∧ b = true then val (s₀ v) else 0 := by
  unfold Z
  rw [cnt_star_update hv, cnt_star_update hv, sdiff_erase_eq, sdiff_erase_eq]
  simp only [mem_sdiff, sset, mem_filter, mem_univ, true_and]
  by_cases hX : v ∈ X <;> cases b <;> cases hs : s₀ v <;> simp [hX, val] <;> ring

lemma Z_erase {u v : Fin n} (hv : v ≠ u) (s₀ : Fin n → Bool) (X : Finset (Fin n)) (x : Ω n) :
    Z s₀ u X x = Z s₀ u (insert v X) x +
      if v ∉ X ∧ x (edge u v) = true then val (s₀ v) else 0 := by
  have := Z_update hv s₀ X x (x (edge u v))
  rwa [Function.update_eq_self] at this

lemma star_sdiff_subset (u : Fin n) (A X : Finset (Fin n)) :
    star u (A \ X) ⊆ star u (univ \ X) :=
  star_subset (sdiff_subset_sdiff (subset_univ _) (Subset.refl _))

lemma depOn_Z (s₀ : Fin n → Bool) (u : Fin n) (X : Finset (Fin n)) (φ : ℤ → ℝ) :
    DepOn (fun x => φ (Z s₀ u X x)) (star u (univ \ X)) := by
  intro x y h
  simp only [Z, cnt_congr fun i hi => h i (star_sdiff_subset u _ X hi)]

lemma evDepOn_Z (s₀ : Fin n → Bool) (u : Fin n) (X : Finset (Fin n)) (P : ℤ → Prop) :
    EvDepOn (fun x => P (Z s₀ u X x)) (star u (univ \ X)) := by
  intro x y h
  simp only [Z, cnt_congr fun i hi => h i (star_sdiff_subset u _ X hi)]

lemma Z_sets_disjoint (s₀ : Fin n → Bool) (u : Fin n) (X : Finset (Fin n)) :
    Disjoint (star u (sset s₀ true \ X)) (star u (sset s₀ false \ X)) :=
  star_disjoint ((sset_disjoint s₀).mono sdiff_subset sdiff_subset)

/-- Three-point window bound for `Z`. -/
lemma Pr_Z_window_le (hp0 : 0 < p) (hp1 : p < 1) (s₀ : Fin n → Bool) (u : Fin n)
    (X : Finset (Fin n)) (hσ : 6 ≤ sd (star u (sset s₀ true \ X)).card p) (a : ℤ) :
    Pr (q n p) (fun x => |Z s₀ u X x + a| ≤ 1) ≤
      3 * (exp 6 / sd (star u (sset s₀ true \ X)).card p) := by
  have hq := isProb_q (n := n) hp0.le hp1.le
  unfold Z
  have h1 := Pr_cnt_sub_eq_le' hp0 hp1 (q_star p u _) (q_star p u _) (Z_sets_disjoint s₀ u X) hσ
  have hsplit : ∀ x : Ω n,
      |(cnt (star u (sset s₀ true \ X)) x : ℤ) - cnt (star u (sset s₀ false \ X)) x + a| ≤ 1 →
      ((cnt (star u (sset s₀ true \ X)) x : ℤ) - cnt (star u (sset s₀ false \ X)) x = -a - 1) ∨
      ((cnt (star u (sset s₀ true \ X)) x : ℤ) - cnt (star u (sset s₀ false \ X)) x = -a) ∨
      ((cnt (star u (sset s₀ true \ X)) x : ℤ) - cnt (star u (sset s₀ false \ X)) x = -a + 1) := by
    intro x h; rw [abs_le] at h; omega
  refine (Pr_mono hq hsplit).trans ?_
  refine (Pr_or_le hq _ _).trans ?_
  refine (add_le_add le_rfl (Pr_or_le hq _ _)).trans ?_
  linarith [h1 (-a - 1), h1 (-a), h1 (-a + 1)]

/-! ### Signed contributions to the round-2 neighbour sum -/

/-- Signed contribution of `u` to the round-2 neighbour sum of `v`. -/
def I (s₀ : Fin n → Bool) (v u : Fin n) (x : Ω n) : ℝ :=
  if adj x v u then (val (step x s₀ u) : ℝ) else 0

lemma I_eq (s₀ : Fin n → Bool) (v u : Fin n) (x : Ω n) :
    I s₀ v u x = if v ≠ u ∧ x (edge u v) = true then (val (step x s₀ u) : ℝ) else 0 := by
  simp only [I, adj, edge_comm v u]

lemma nsum_step (x : Ω n) (s₀ : Fin n → Bool) (v : Fin n) :
    (nsum x (step x s₀) v : ℝ) = ∑ u ∈ univ.erase v, I s₀ v u x := by
  unfold nsum I
  rw [Int.cast_sum, ← sum_erase (a := v) univ
    (f := fun w => ((if adj x v w then val (step x s₀ w) else 0 : ℤ) : ℝ)) (by simp [adj])]
  exact sum_congr rfl fun u _ => by split_ifs <;> simp

lemma depOn_I (s₀ : Fin n → Bool) {v u : Fin n} (hu : u ≠ v) : DepOn (I s₀ v u) (star u univ) := by
  intro x y h
  have he : x (edge u v) = y (edge u v) := h _ ((mem_star (Ne.symm hu)).2 (mem_univ v))
  rw [I_eq, I_eq, he, step_congr s₀ u h]

lemma depOn_I_insert (s₀ : Fin n → Bool) {v u u' : Fin n} (hu : u ≠ v) (huu' : u ≠ u') :
    DepOn (I s₀ v u) (insert (edge u u') (star u (univ.erase u'))) := by
  refine (depOn_I s₀ hu).mono ?_
  rw [star_erase (Ne.symm huu') (mem_univ u')]

lemma I_update_false (s₀ : Fin n → Bool) (v u : Fin n) (x : Ω n) :
    I s₀ v u (Function.update x (edge u v) false) = 0 := by
  rw [I_eq]; simp

lemma I_update_true (s₀ : Fin n → Bool) {v u : Fin n} (hu : u ≠ v) (x : Ω n) :
    I s₀ v u (Function.update x (edge u v) true) =
      val (step (Function.update x (edge u v) true) s₀ u) := by
  rw [I_eq]; simp [Ne.symm hu]

lemma E_I (s₀ : Fin n → Bool) {v u : Fin n} (hu : u ≠ v) :
    E (q n p) (I s₀ v u) =
      p * E (q n p) (fun x => (val (step (Function.update x (edge u v) true) s₀ u) : ℝ)) := by
  rw [E_update (edge u v)]
  simp only [I_update_false, I_update_true s₀ hu, q_edge p (Ne.symm hu), E_const, mul_zero,
    add_zero]

lemma val_step_update_ge (s₀ : Fin n → Bool) {v u : Fin n} (hv : v ≠ u) (x : Ω n) :
    (2 : ℝ) * (if 2 ≤ Z s₀ u {v} x then 1 else 0) - 1 ≤
      (val (step (Function.update x (edge u v) true) s₀ u) : ℝ) := by
  split_ifs with h
  · have : 0 < nsum (Function.update x (edge u v) true) s₀ u := by
      rw [nsum_eq_Z, Z_update hv, insert_empty]
      simp only [notMem_empty, not_false_eq_true, true_and, if_true]
      unfold val; split_ifs <;> omega
    rw [step_pos this]; norm_num [val]
  · unfold val; split_ifs <;> norm_num

lemma card_sdiff_erase_ge (A : Finset (Fin n)) (u v : Fin n) :
    (A.card : ℝ) - 2 ≤ ((A \ {v}).erase u).card := by
  have h1 : A.card ≤ (A \ {v}).card + 1 := by
    have := card_le_card_sdiff_add_card (s := A) (t := {v}); rwa [card_singleton] at this
  have h2 : (A \ {v}).card ≤ ((A \ {v}).erase u).card + 1 := by
    have := card_le_card_sdiff_add_card (s := A \ {v}) (t := {u})
    rwa [card_singleton, sdiff_singleton_eq_erase u] at this
  have : A.card ≤ ((A \ {v}).erase u).card + 2 := by omega
  have := (Nat.cast_le (α := ℝ)).2 this
  push_cast at this; linarith

/-- Lower bound on the mean contribution `E[I_u]` (Lemma 3.5 of the paper, elementary form). -/
lemma E_I_ge (hp0 : 0 < p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool) {v u : Fin n} (hu : u ≠ v)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hK : 10000 ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p)
    (hγ : γ * √(n * p) ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p) :
    2 * p * (ξ₀ * γ) ≤ E (q n p) (I s₀ v u) := by
  have hq := isProb_q (n := n) hp0.le hp1
  rw [E_I s₀ hu]
  set a := (sset s₀ true).card
  set b := (sset s₀ false).card
  set T₃ := star u (sset s₀ false \ {v}) with hT₃
  set TP := star u (sset s₀ true \ {v}) with hTP
  have hab : (b : ℝ) < a - 2 := by nlinarith
  have hbn : (b : ℝ) ≤ n := by
    have := card_sset_add s₀; exact_mod_cast (by omega : b ≤ n)
  have hcard3 : (T₃.card : ℝ) ≤ b := by
    exact_mod_cast (card_star_le _ _).trans (card_le_card sdiff_subset)
  have hcardP : (a : ℝ) - 2 ≤ TP.card := by rw [hTP, card_star]; exact card_sdiff_erase_ge _ u v
  obtain ⟨T₂, hT₂, hcard2⟩ := exists_subset_card_eq (s := TP) (n := T₃.card)
    (by exact_mod_cast hcard3.trans (hab.le.trans hcardP))
  set T₁ := TP \ T₂
  have hcard1 : (T₁.card : ℝ) = TP.card - T₂.card := by
    rw [card_sdiff_of_subset hT₂]; rw [Nat.cast_sub (card_le_card hT₂)]
  have hd13 : Disjoint TP T₃ := Z_sets_disjoint s₀ u {v}
  have hPr : 1 / 2 + ξ₀ * γ ≤ Pr (q n p) (fun x => 2 ≤ Z s₀ u {v} x) := by
    have hsplit : ∀ x : Ω n, cnt TP x = cnt T₁ x + cnt T₂ x := fun x => by
      rw [← cnt_union sdiff_disjoint, sdiff_union_of_subset hT₂]
    rw [Pr_congr (B := fun x => cnt T₃ x + 2 ≤ cnt T₁ x + cnt T₂ x)
      (fun x => by unfold Z; rw [← hTP, ← hT₃, ← hsplit]; omega)]
    refine Pr_maj_ge hq hp0 hp1 (fun i hi => q_star p u _ i (sdiff_subset hi))
      (fun i hi => q_star p u _ i (hT₂ hi)) (q_star p u _) sdiff_disjoint
      (hd13.mono_left sdiff_subset) (hd13.mono_left hT₂) hcard2 ?_ hγ0 hγ1 ?_
    · refine hK.trans (mul_le_mul_of_nonneg_right ?_ hp0.le)
      rw [hcard1, hcard2]; linarith
    · refine hγ.trans' ?_ |>.trans (mul_le_mul_of_nonneg_right ?_ hp0.le)
      · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hγ0
        rw [hcard2]; exact mul_le_mul_of_nonneg_right (hcard3.trans hbn) hp0.le
      · rw [hcard1, hcard2]; linarith
  have hE : 2 * (ξ₀ * γ) ≤
      E (q n p) (fun x => (val (step (Function.update x (edge u v) true) s₀ u) : ℝ)) := by
    have h1 := E_mono hq (F := fun x => 2 * (if 2 ≤ Z s₀ u {v} x then (1 : ℝ) else 0) - 1)
      (fun x => val_step_update_ge s₀ (Ne.symm hu) x)
    rw [E_sub, E_const_mul, E_const, ← Pr_eq_E] at h1
    linarith
  calc 2 * p * (ξ₀ * γ) = p * (2 * (ξ₀ * γ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hE hp0.le

/-! ### Covariances -/

lemma abs_val_sub_le (a b : Bool) : |(val a : ℝ) - val b| ≤ 2 := by
  cases a <;> cases b <;> simp [val] <;> norm_num

lemma abs_val_le (a : Bool) : |val a| ≤ 1 := by cases a <;> simp [val]

lemma abs_I_update_sub_le (s₀ : Fin n → Bool) {v u u' : Fin n} (hu : u ≠ v) (huu' : u ≠ u')
    (hu'v : u' ≠ v) (x : Ω n) :
    |I s₀ v u (Function.update x (edge u u') true) -
        I s₀ v u (Function.update x (edge u u') false)| ≤
      2 * ((if x (edge u v) = true then 1 else 0) *
        if |Z s₀ u {v, u'} x + val (s₀ v)| ≤ 1 then 1 else 0) := by
  have hne : edge u v ≠ edge u u' := fun h =>
    hu'v (edge_inj (Ne.symm hu) (Ne.symm huu') h).symm
  rw [I_eq, I_eq, Function.update_of_ne hne, Function.update_of_ne hne]
  by_cases hx : x (edge u v) = true
  · rw [if_pos hx, if_pos ⟨Ne.symm hu, hx⟩, if_pos ⟨Ne.symm hu, hx⟩]
    have hZ : Z s₀ u {u'} x = Z s₀ u {v, u'} x + val (s₀ v) := by
      rw [Z_erase (Ne.symm hu) s₀ {u'} x, if_pos ⟨by simpa using hu'v.symm, hx⟩]
    have hpl : nsum (Function.update x (edge u u') true) s₀ u =
        Z s₀ u {v, u'} x + val (s₀ v) + val (s₀ u') := by
      rw [nsum_eq_Z, Z_update (Ne.symm huu'), insert_empty, ← hZ]; simp
    have hmi : nsum (Function.update x (edge u u') false) s₀ u = Z s₀ u {v, u'} x + val (s₀ v) := by
      rw [nsum_eq_Z, Z_update (Ne.symm huu'), insert_empty, ← hZ]; simp
    by_cases hw : |Z s₀ u {v, u'} x + val (s₀ v)| ≤ 1
    · rw [if_pos hw]; simpa using abs_val_sub_le _ _
    · rw [if_neg hw]
      have hstep : step (Function.update x (edge u u') true) s₀ u =
          step (Function.update x (edge u u') false) s₀ u := by
        have := abs_val_le (s₀ u')
        rw [abs_le] at this
        simp only [step, hpl, hmi]
        rcases lt_abs.1 (not_le.1 hw) with h | h <;> split_ifs <;> first | rfl | omega
      rw [hstep]; simp
  · rw [if_neg hx]
    simp [hx]

/-- The two conditional means differ by at most `2p · P[window]`. -/
lemma abs_Delta_le (hp0 : 0 < p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool) {v u u' : Fin n} (hu : u ≠ v)
    (huu' : u ≠ u') (hu'v : u' ≠ v) :
    |E (q n p) (fun x => I s₀ v u (Function.update x (edge u u') true)) -
        E (q n p) (fun x => I s₀ v u (Function.update x (edge u u') false))| ≤
      2 * p * Pr (q n p) (fun x => |Z s₀ u {v, u'} x + val (s₀ v)| ≤ 1) := by
  classical
  have hq := isProb_q (n := n) hp0.le hp1
  rw [← E_sub]
  refine (abs_E_le hq _).trans ?_
  refine (E_mono hq fun x => abs_I_update_sub_le s₀ hu huu' hu'v x).trans ?_
  have hF : DepOn (fun x : Ω n => if x (edge u v) = true then (1 : ℝ) else 0) {edge u v} :=
    fun x y h => by simp only [h _ (mem_singleton_self _)]
  have hG : DepOn (fun x : Ω n => if |Z s₀ u {v, u'} x + val (s₀ v)| ≤ 1 then (1 : ℝ) else 0)
      (star u (univ \ {v, u'})) :=
    depOn_Z s₀ u {v, u'} fun z => if |z + val (s₀ v)| ≤ 1 then (1 : ℝ) else 0
  have hd : Disjoint ({edge u v} : Finset (Fin n ⊕ Edge n)) (star u (univ \ {v, u'})) :=
    disjoint_singleton_left.2 (by rw [mem_star (Ne.symm hu)]; simp)
  rw [E_const_mul, E_mul_of_depOn hF hG hd, E_ind_coord_bool, q_edge p (Ne.symm hu), Pr_eq_E]
  exact le_of_eq (by ring)

lemma Var_I_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool) {v u : Fin n} (hu : u ≠ v) :
    Var (q n p) (I s₀ v u) ≤ p := by
  have hq := isProb_q (n := n) hp0 hp1
  rw [Var_eq]
  have : E (q n p) (fun x => I s₀ v u x ^ 2) ≤
      E (q n p) (fun x => if x (edge u v) = true then 1 else 0) := by
    refine E_mono hq fun x => ?_
    rw [I_eq]
    split_ifs with h1 h2 h2
    · cases step x s₀ u <;> simp [val]
    · exact absurd h1.2 h2
    · norm_num
    · norm_num
  rw [E_ind_coord_bool, q_edge p (Ne.symm hu)] at this
  nlinarith [sq_nonneg (E (q n p) (I s₀ v u))]

lemma card_star_sdiff (s₀ : Fin n → Bool) (u u' v : Fin n) :
    (star u (sset s₀ true \ {v, u'})).card = (sset s₀ true \ {u, u', v}).card := by
  rw [card_star]; congr 1; ext w; simp only [mem_erase, mem_sdiff, mem_insert, mem_singleton]; tauto

lemma exp_six_sq : exp 6 * exp 6 = exp 12 := by rw [← exp_add]; norm_num

/-- Covariance bound for two distinct contributions (Lemma 3.6 / Claim 3.9 of the paper). -/
lemma abs_Cov_le (hp0 : 0 < p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool) {v u u' : Fin n} (hu : u ≠ v)
    (hu' : u' ≠ v) (huu' : u ≠ u') (hM : 0 < (sset s₀ true \ {u, u', v}).card) :
    |Cov (q n p) (I s₀ v u) (I s₀ v u')| ≤
      36 * exp 12 * p ^ 2 / (sset s₀ true \ {u, u', v}).card := by
  have hq := isProb_q (n := n) hp0.le hp1
  set M := (sset s₀ true \ {u, u', v}).card with hMdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hG : DepOn (I s₀ v u') (insert (edge u u') (star u' (univ.erase u))) := by
    rw [edge_comm]; exact depOn_I_insert s₀ hu' huu'.symm
  rw [Cov_update (depOn_I_insert s₀ hu huu') hG (star_disjoint_of_ne huu' (by simp)),
    q_edge p (Ne.symm huu'), abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hp0.le (by linarith))]
  have h0 : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
  have hΔ₁ := abs_Delta_le hp0 hp1 s₀ hu huu' hu'
  have hΔ₂ := abs_Delta_le hp0 hp1 s₀ hu' huu'.symm hu
  rw [edge_comm u' u] at hΔ₂
  have hΔ₁' := hΔ₁.trans (mul_le_of_le_one_right (by positivity) (Pr_le_one hq _))
  have hΔ₂' := hΔ₂.trans (mul_le_of_le_one_right (by positivity) (Pr_le_one hq _))
  have hset : (sset s₀ true \ {u', u, v}).card = M := by
    rw [hMdef]; congr 1; ext w; simp only [mem_sdiff, mem_insert, mem_singleton]; tauto
  by_cases hσ : 36 ≤ (M : ℝ) * p * (1 - p)
  · have hp1' : p < 1 := by
      rcases hp1.lt_or_eq with h | h
      · exact h
      · subst h; norm_num at hσ
    have hsd2 : sd M p ^ 2 = M * p * (1 - p) := sd_sq hp0.le hp1
    have hsd6 : 6 ≤ sd M p := by nlinarith [sd_nonneg M p]
    have hσpos : 0 < sd M p := by linarith
    have hW₁ := Pr_Z_window_le hp0 hp1' s₀ u {v, u'}
      (by rw [card_star_sdiff]; exact hsd6) (val (s₀ v))
    have hW₂ := Pr_Z_window_le hp0 hp1' s₀ u' {v, u}
      (by rw [card_star_sdiff, hset]; exact hsd6) (val (s₀ v))
    rw [card_star_sdiff] at hW₁
    rw [card_star_sdiff, hset] at hW₂
    have hB₁ := hΔ₁.trans (mul_le_mul_of_nonneg_left hW₁ (by positivity))
    have hB₂ := hΔ₂.trans (mul_le_mul_of_nonneg_left hW₂ (by positivity))
    have hp' : (1 : ℝ) - p ≠ 0 := sub_ne_zero.2 hp1'.ne'
    calc p * (1 - p) * |_| * |_| ≤ p * (1 - p) * (2 * p * (3 * (exp 6 / sd M p))) *
          (2 * p * (3 * (exp 6 / sd M p))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hB₁ h0) hB₂ (abs_nonneg _)
            (mul_nonneg h0 (by positivity))
      _ = 36 * (exp 6 * exp 6) * p ^ 2 * (p * (1 - p)) / sd M p ^ 2 := by
          field_simp; ring
      _ = 36 * exp 12 * p ^ 2 / M := by
          rw [exp_six_sq, hsd2]; field_simp; try ring
  · rw [not_le] at hσ
    calc p * (1 - p) * |_| * |_| ≤ p * (1 - p) * (2 * p) * (2 * p) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔ₁' h0) hΔ₂' (abs_nonneg _) (by positivity)
      _ = 4 * p ^ 2 * (M * p * (1 - p)) / M := by field_simp; ring
      _ ≤ 4 * p ^ 2 * 36 / M := by gcongr
      _ ≤ 36 * exp 12 * p ^ 2 / M := by
          rw [div_le_div_iff_of_pos_right hMpos]
          nlinarith [add_one_le_exp (12 : ℝ), sq_nonneg p]

/-! ### The round-2 neighbour sum: variance, mean, Chebyshev, Markov -/

lemma card_erase_univ (v : Fin n) : (((univ : Finset (Fin n)).erase v).card : ℝ) = n - 1 := by
  rw [card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin, Nat.cast_sub v.pos]; simp

/-- The round-2 neighbour sum of `v`. -/
def X2 (s₀ : Fin n → Bool) (v : Fin n) (x : Ω n) : ℝ := ∑ u ∈ univ.erase v, I s₀ v u x

lemma card_sdiff_three_ge (A : Finset (Fin n)) (u u' v : Fin n) :
    (A.card : ℝ) - 3 ≤ (A \ {u, u', v}).card := by
  have h1 := card_le_card_sdiff_add_card (s := A) (t := {u, u', v})
  have h2 : ({u, u', v} : Finset (Fin n)).card ≤ 3 := card_le_three
  have : A.card ≤ (A \ {u, u', v}).card + 3 := by omega
  have := (Nat.cast_le (α := ℝ)).2 this
  push_cast at this; linarith

lemma Var_X2_le (hp0 : 0 < p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool) (v : Fin n)
    (ha : 3 < (sset s₀ true).card) :
    Var (q n p) (X2 s₀ v) ≤
      (n - 1) * p + (n - 1) ^ 2 * (36 * exp 12 * p ^ 2 / ((sset s₀ true).card - 3)) := by
  set a := (sset s₀ true).card
  have ha' : (0 : ℝ) < a - 3 := by
    have : (3 : ℝ) < a := by exact_mod_cast ha
    linarith
  set C := 36 * exp 12 * p ^ 2 / ((a : ℝ) - 3)
  have hC : 0 ≤ C := by positivity
  unfold X2; rw [Var_sum]
  have hterm : ∀ u ∈ univ.erase v, ∀ u' ∈ univ.erase v,
      Cov (q n p) (I s₀ v u) (I s₀ v u') ≤ (if u = u' then p else 0) + C := by
    intro u hu u' hu'
    have hu := ne_of_mem_erase hu
    have hu' := ne_of_mem_erase hu'
    by_cases h : u = u'
    · subst h; rw [if_pos rfl, ← Var_eq_Cov]; linarith [Var_I_le hp0.le hp1 s₀ hu]
    · rw [if_neg h, zero_add]
      have hM := card_sdiff_three_ge (sset s₀ true) u u' v
      have hMpos : 0 < (sset s₀ true \ {u, u', v}).card := by
        exact_mod_cast (ha'.trans_le hM)
      refine (le_abs_self _).trans ((abs_Cov_le hp0 hp1 s₀ hu hu' h hMpos).trans ?_)
      exact div_le_div_of_nonneg_left (by positivity) ha' hM
  calc ∑ u ∈ univ.erase v, ∑ u' ∈ univ.erase v, Cov (q n p) (I s₀ v u) (I s₀ v u')
      ≤ ∑ u ∈ univ.erase v, ∑ u' ∈ univ.erase v, ((if u = u' then p else 0) + C) :=
        sum_le_sum fun u hu => sum_le_sum fun u' hu' => hterm u hu u' hu'
    _ = ∑ u ∈ univ.erase v, (p + ((univ.erase v).card : ℝ) * C) := by
        refine sum_congr rfl fun u hu => ?_
        rw [sum_add_distrib, sum_ite_eq, if_pos hu, sum_const, nsmul_eq_mul]
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_erase_univ]; ring

lemma E_X2_ge (hp0 : 0 < p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool) (v : Fin n)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hK : 10000 ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p)
    (hγ : γ * √(n * p) ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p) :
    ((n : ℝ) - 1) * (2 * p * (ξ₀ * γ)) ≤ E (q n p) (X2 s₀ v) := by
  unfold X2; rw [E_sum]
  have := sum_le_sum (s := univ.erase v) (f := fun _ => 2 * p * (ξ₀ * γ))
    (g := fun u => E (q n p) (I s₀ v u)) fun u hu =>
    E_I_ge hp0 hp1 s₀ (ne_of_mem_erase hu) hγ0 hγ1 hK hγ
  rwa [sum_const, nsmul_eq_mul, card_erase_univ] at this

/-- Chebyshev: a fixed vertex is in the minority after two rounds with small probability. -/
theorem Pr_round2_false_le (hp0 : 0 < p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool) (v : Fin n)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hn : 12 ≤ n)
    (hab : (sset s₀ false).card ≤ (sset s₀ true).card)
    (hK : 10000 ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p)
    (hγ : γ * √(n * p) ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p) :
    Pr (q n p) (fun x => Sfix x s₀ 2 v = false) ≤
      (1 / (2 * n * p) + 36 * exp 12 / n) / (ξ₀ ^ 2 * γ ^ 2) := by
  have hq := isProb_q (n := n) hp0.le hp1
  set a := (sset s₀ true).card
  set b := (sset s₀ false).card
  have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have habn : a + b = n := card_sset_add s₀
  have ha : (n : ℝ) / 2 ≤ a := by
    have : n ≤ 2 * a := by omega
    have := (Nat.cast_le (α := ℝ)).2 this
    push_cast at this; linarith
  have ha3 : 3 < a := by omega
  have ha3' : (0 : ℝ) < a - 3 := by
    have : (3 : ℝ) < a := by exact_mod_cast ha3
    linarith
  have hξ := ξ₀_pos
  set μ := E (q n p) (X2 s₀ v)
  set t := ((n : ℝ) - 1) * (2 * p * (ξ₀ * γ)) with ht
  have hμ : t ≤ μ := E_X2_ge hp0 hp1 s₀ v hγ0.le hγ1 hK hγ
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have htpos : 0 < t := by positivity
  have hV := Var_X2_le hp0 hp1 s₀ v ha3
  have himp : ∀ x, Sfix x s₀ 2 v = false → t ≤ |X2 s₀ v x - μ| := by
    intro x hx
    have h1 : nsum x (step x s₀) v ≤ 0 := nsum_nonpos_of_step_false hx
    have h2 : X2 s₀ v x ≤ 0 := by
      unfold X2; rw [← nsum_step]; exact_mod_cast h1
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  refine (Pr_mono hq himp).trans ((Pr_abs_sub_le hq _ htpos).trans ?_)
  have hp' : p ≠ 0 := hp0.ne'
  have hn1' : (n : ℝ) - 1 ≠ 0 := hn1.ne'
  have hξ' : ξ₀ ≠ 0 := hξ.ne'
  have hγ' : γ ≠ 0 := hγ0.ne'
  have ha3'' : (a : ℝ) - 3 ≠ 0 := ha3'.ne'
  calc Var (q n p) (X2 s₀ v) / t ^ 2
      ≤ ((n - 1) * p + (n - 1) ^ 2 * (36 * exp 12 * p ^ 2 / (a - 3))) / t ^ 2 :=
        div_le_div_of_nonneg_right hV (by positivity)
    _ = (1 / (4 * (n - 1) * p) + 36 * exp 12 / (4 * (a - 3))) / (ξ₀ ^ 2 * γ ^ 2) := by
        rw [ht]; field_simp; ring
    _ ≤ (1 / (2 * n * p) + 36 * exp 12 / n) / (ξ₀ ^ 2 * γ ^ 2) := by
        have h1 : 1 / (4 * ((n : ℝ) - 1) * p) ≤ 1 / (2 * n * p) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
        have h2 : 36 * exp 12 / (4 * ((a : ℝ) - 3)) ≤ 36 * exp 12 / n :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        exact div_le_div_of_nonneg_right (add_le_add h1 h2) (by positivity)

/-- Markov: with probability `1 - O(η/γ²)`, at most `n/10` vertices are `-1` after two rounds. -/
theorem Pr_many_false_le (hp0 : 0 < p) (hp1 : p ≤ 1) (s₀ : Fin n → Bool)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hn : 12 ≤ n)
    (hab : (sset s₀ false).card ≤ (sset s₀ true).card)
    (hK : 10000 ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p)
    (hγ : γ * √(n * p) ≤ (((sset s₀ true).card : ℝ) - 2 - (sset s₀ false).card) * p) :
    Pr (q n p) (fun x => ¬ 10 * (sset (Sfix x s₀ 2) false).card ≤ n) ≤
      10 * ((1 / (2 * n * p) + 36 * exp 12 / n) / (ξ₀ ^ 2 * γ ^ 2)) := by
  have hq := isProb_q (n := n) hp0.le hp1
  set η := (1 / (2 * n * p) + 36 * exp 12 / n) / (ξ₀ ^ 2 * γ ^ 2)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set N : Ω n → ℝ := fun x => ∑ v, if Sfix x s₀ 2 v = false then (1 : ℝ) else 0 with hNdef
  have hN : ∀ x, ((sset (Sfix x s₀ 2) false).card : ℝ) = N x := fun x => by
    simp only [sset, hNdef, card_filter]; push_cast; rfl
  have himp : ∀ x, ¬ 10 * (sset (Sfix x s₀ 2) false).card ≤ n → (n : ℝ) / 10 ≤ N x := by
    intro x hx
    rw [← hN]
    have := (Nat.cast_lt (α := ℝ)).2 (not_le.1 hx)
    push_cast at this; linarith
  refine (Pr_mono hq himp).trans ((Pr_le_E_div hq
    (fun x => sum_nonneg fun v _ => by split_ifs <;> norm_num) (by positivity)).trans ?_)
  have hE : E (q n p) N ≤ n * η := by
    rw [hNdef, E_sum]
    calc ∑ v, E (q n p) (fun x => if Sfix x s₀ 2 v = false then (1 : ℝ) else 0)
        ≤ ∑ _v : Fin n, η := sum_le_sum fun v _ => by
          rw [← Pr_eq_E]; exact Pr_round2_false_le hp0 hp1 s₀ v hγ0 hγ1 hn hab hK hγ
      _ = n * η := by simp
  rw [div_le_iff₀ (by positivity)]
  linarith

end MD
