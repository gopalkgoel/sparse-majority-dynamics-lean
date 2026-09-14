import MajorityDynamics.Literature.FKMFormal.Defs

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! # Finite Bernoulli product spaces: expectation, independence, conditioning. -/

namespace MD

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}

/-- All coordinate probabilities lie in `[0,1]`. -/
def IsProb (q : ι → ℝ) : Prop := ∀ i, 0 ≤ q i ∧ q i ≤ 1

lemma wt_nonneg (hq : IsProb q) (x : ι → Bool) : 0 ≤ wt q x := by
  unfold wt; exact Finset.prod_nonneg fun i _ => by split_ifs <;> linarith [hq i]

lemma sum_wt (q : ι → ℝ) : ∑ x, wt q x = 1 := by
  have h : ∏ i : ι, (∑ b ∈ (univ : Finset Bool), if b then q i else 1 - q i) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [Fintype.sum_bool]; simp
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ] at h
  exact h

/-! ### Expectation -/

lemma E_add (F G : (ι → Bool) → ℝ) : E q (fun x => F x + G x) = E q F + E q G := by
  simp [E, mul_add, sum_add_distrib]

lemma E_sub (F G : (ι → Bool) → ℝ) : E q (fun x => F x - G x) = E q F - E q G := by
  simp [E, mul_sub, sum_sub_distrib]

lemma E_const_mul (c : ℝ) (F : (ι → Bool) → ℝ) : E q (fun x => c * F x) = c * E q F := by
  simp [E, mul_left_comm, mul_sum]

lemma E_mul_const (c : ℝ) (F : (ι → Bool) → ℝ) : E q (fun x => F x * c) = E q F * c := by
  simp [E, ← mul_assoc, sum_mul]

lemma E_const (c : ℝ) : E q (fun _ => c) = c := by
  simp [E, ← sum_mul, sum_wt]

lemma E_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → Bool) → ℝ) :
    E q (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, E q (F j) := by
  unfold E; simp_rw [mul_sum]; rw [sum_comm]

lemma E_congr {F G : (ι → Bool) → ℝ} (h : ∀ x, F x = G x) : E q F = E q G := by
  simp [E, h]

lemma E_mono (hq : IsProb q) {F G : (ι → Bool) → ℝ} (h : ∀ x, F x ≤ G x) : E q F ≤ E q G :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (wt_nonneg hq x)

lemma E_nonneg (hq : IsProb q) {F : (ι → Bool) → ℝ} (h : ∀ x, 0 ≤ F x) : 0 ≤ E q F := by
  have := E_mono hq (F := fun _ => 0) h
  rwa [E_const] at this

/-! ### Integrating out one coordinate -/

/-- Average of `F` over the coordinate `i`. -/
def Ei (q : ι → ℝ) (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  q i * F (Function.update x i true) + (1 - q i) * F (Function.update x i false)

lemma wt_update (x : ι → Bool) (i : ι) (b : Bool) :
    wt q (Function.update x i b) * (if x i then q i else 1 - q i) =
      wt q x * (if b then q i else 1 - q i) := by
  unfold wt
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ _ (mem_univ i)]
  have : ∏ j ∈ univ.erase i, (if Function.update x i b j then q j else 1 - q j) =
      ∏ j ∈ univ.erase i, (if x j then q j else 1 - q j) :=
    prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  ring

lemma sum_filter_update (i : ι) (b c : Bool) (G : (ι → Bool) → ℝ) :
    ∑ x ∈ univ.filter (fun x => x i = b), G (Function.update x i c) =
      ∑ y ∈ univ.filter (fun y => y i = c), G y := by
  refine sum_nbij' (fun x => Function.update x i c) (fun y => Function.update y i b)
    (fun x _ => by simp) (fun y _ => by simp) (fun x hx => ?_) (fun y hy => ?_) (fun _ _ => rfl)
  · simp only [mem_filter, mem_univ, true_and] at hx
    simp [Function.update_idem, ← hx]
  · simp only [mem_filter, mem_univ, true_and] at hy
    simp [Function.update_idem, ← hy]

lemma sum_c_update (i : ι) (c : Bool) (H : (ι → Bool) → ℝ) :
    ∑ x, (if x i then q i else 1 - q i) * H (Function.update x i c) =
      ∑ y ∈ univ.filter (fun y => y i = c), H y := by
  rw [← sum_filter_add_sum_filter_not univ (fun x => x i = true)]
  have h1 : ∀ x ∈ univ.filter (fun x => x i = true),
      (if x i then q i else 1 - q i) * H (Function.update x i c) =
        q i * H (Function.update x i c) := fun x hx => by
    simp only [mem_filter, mem_univ, true_and] at hx; simp [hx]
  have h2 : ∀ x ∈ univ.filter (fun x => ¬ x i = true),
      (if x i then q i else 1 - q i) * H (Function.update x i c) =
        (1 - q i) * H (Function.update x i c) := fun x hx => by
    simp only [mem_filter, mem_univ, true_and] at hx; simp [hx]
  rw [sum_congr rfl h1, sum_congr rfl h2, ← mul_sum, ← mul_sum]
  have h3 : univ.filter (fun x : ι → Bool => ¬ x i = true) = univ.filter (fun x => x i = false) := by
    ext x; simp
  rw [h3, sum_filter_update i true c, sum_filter_update i false c]
  ring

lemma E_Ei (i : ι) (F : (ι → Bool) → ℝ) : E q (Ei q i F) = E q F := by
  unfold E Ei
  have h : ∀ x, wt q x * (q i * F (Function.update x i true) +
      (1 - q i) * F (Function.update x i false)) =
      (if x i then q i else 1 - q i) * (wt q (Function.update x i true) * F (Function.update x i true))
      + (if x i then q i else 1 - q i) * (wt q (Function.update x i false) * F (Function.update x i false)) := by
    intro x
    have h1 := wt_update (q := q) x i true
    have h2 := wt_update (q := q) x i false
    simp only [if_true, Bool.false_eq_true, if_false] at h1 h2
    linear_combination (-F (Function.update x i true)) * h1 + (-F (Function.update x i false)) * h2
  simp_rw [h, sum_add_distrib]
  rw [sum_c_update i true (fun y => wt q y * F y), sum_c_update i false (fun y => wt q y * F y),
    ← sum_filter_add_sum_filter_not univ (fun x : ι → Bool => x i = true)]
  congr 1
  apply sum_congr _ fun _ _ => rfl
  ext x; simp

/-! ### Dependence on a set of coordinates -/

/-- `F` depends only on the coordinates in `A`. -/
def DepOn (F : (ι → Bool) → ℝ) (A : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ A, x i = y i) → F x = F y

/-- The event `P` depends only on the coordinates in `A`. -/
def EvDepOn (P : (ι → Bool) → Prop) (A : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ A, x i = y i) → (P x ↔ P y)

lemma DepOn.mono {F : (ι → Bool) → ℝ} {A B : Finset ι} (h : DepOn F A) (hAB : A ⊆ B) :
    DepOn F B := fun x y hxy => h x y fun i hi => hxy i (hAB hi)

lemma DepOn.const (c : ℝ) (A : Finset ι) : DepOn (fun _ => c) A := fun _ _ _ => rfl

lemma DepOn.add {F G : (ι → Bool) → ℝ} {A : Finset ι} (hF : DepOn F A) (hG : DepOn G A) :
    DepOn (fun x => F x + G x) A := fun x y h => by simp only [hF x y h, hG x y h]

lemma DepOn.sub {F G : (ι → Bool) → ℝ} {A : Finset ι} (hF : DepOn F A) (hG : DepOn G A) :
    DepOn (fun x => F x - G x) A := fun x y h => by simp only [hF x y h, hG x y h]

lemma DepOn.mul {F G : (ι → Bool) → ℝ} {A : Finset ι} (hF : DepOn F A) (hG : DepOn G A) :
    DepOn (fun x => F x * G x) A := fun x y h => by simp only [hF x y h, hG x y h]

lemma DepOn.comp {F : (ι → Bool) → ℝ} {A : Finset ι} (φ : ℝ → ℝ) (hF : DepOn F A) :
    DepOn (fun x => φ (F x)) A := fun x y h => by simp only [hF x y h]

lemma DepOn.sum {κ : Type*} {A : Finset ι} (s : Finset κ) (F : κ → (ι → Bool) → ℝ)
    (h : ∀ j ∈ s, DepOn (F j) A) : DepOn (fun x => ∑ j ∈ s, F j x) A :=
  fun x y hxy => sum_congr rfl fun j hj => h j hj x y hxy

lemma DepOn.prod {κ : Type*} (s : Finset κ) (F : κ → (ι → Bool) → ℝ) (A : κ → Finset ι)
    (h : ∀ j ∈ s, DepOn (F j) (A j)) : DepOn (fun x => ∏ j ∈ s, F j x) (s.biUnion A) :=
  fun x y hxy => prod_congr rfl fun j hj =>
    h j hj x y fun i hi => hxy i (mem_biUnion.2 ⟨j, hj, hi⟩)

lemma EvDepOn.ind {P : (ι → Bool) → Prop} [DecidablePred P] {A : Finset ι} (h : EvDepOn P A) :
    DepOn (fun x => if P x then (1 : ℝ) else 0) A := fun x y hxy => by
  simp only [h x y hxy]

lemma EvDepOn.mono {P : (ι → Bool) → Prop} {A B : Finset ι} (h : EvDepOn P A) (hAB : A ⊆ B) :
    EvDepOn P B := fun x y hxy => h x y fun i hi => hxy i (hAB hi)

lemma DepOn.Ei {F : (ι → Bool) → ℝ} {A : Finset ι} (h : DepOn F A) (i : ι) :
    DepOn (Ei q i F) (A.erase i) := by
  intro x y hxy
  have : ∀ b, F (Function.update x i b) = F (Function.update y i b) := fun b =>
    h _ _ fun j hj => by
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact hxy j (mem_erase.2 ⟨hji, hj⟩)
  simp only [MD.Ei, this]

lemma DepOn.update_eq {F : (ι → Bool) → ℝ} {A : Finset ι} (h : DepOn F A) {i : ι} (hi : i ∉ A)
    (x : ι → Bool) (b : Bool) : F (Function.update x i b) = F x :=
  h _ _ fun j hj => Function.update_of_ne (fun hji => hi (by subst hji; exact hj)) _ _

lemma Ei_of_not_mem {F : (ι → Bool) → ℝ} {A : Finset ι} (h : DepOn F A) {i : ι} (hi : i ∉ A) :
    Ei q i F = F := by
  funext x
  simp only [Ei, h.update_eq hi]
  ring

lemma E_mul_of_depOn {F G : (ι → Bool) → ℝ} {A B : Finset ι} (hF : DepOn F A) (hG : DepOn G B)
    (hAB : Disjoint A B) : E q (fun x => F x * G x) = E q F * E q G := by
  induction A using Finset.induction_on generalizing F with
  | empty =>
    have hc : ∀ x, F x = F (fun _ => false) := fun x => hF x _ (by simp)
    rw [E_congr (G := fun x => F (fun _ => false) * G x) fun x => by rw [← hc x],
      E_congr (G := fun _ => F (fun _ => false)) hc, E_const_mul, E_const]
  | insert i A hi ih =>
    have hiB : i ∉ B := Finset.disjoint_left.1 hAB (mem_insert_self i A)
    have hAB' : Disjoint A B := hAB.mono_left (subset_insert i A)
    have h1 : DepOn (Ei q i F) A := by simpa [Finset.erase_insert hi] using hF.Ei (q := q) i
    calc E q (fun x => F x * G x) = E q (Ei q i (fun x => F x * G x)) := (E_Ei ..).symm
      _ = E q (fun x => Ei q i F x * G x) := by
          apply E_congr; intro x
          simp only [Ei, hG.update_eq hiB]; ring
      _ = E q (Ei q i F) * E q G := ih h1 hAB'
      _ = E q F * E q G := by rw [E_Ei]

lemma E_prod_of_depOn {κ : Type*} [DecidableEq κ] (s : Finset κ) (F : κ → (ι → Bool) → ℝ)
    (A : κ → Finset ι) (hA : (s : Set κ).PairwiseDisjoint A) (h : ∀ j ∈ s, DepOn (F j) (A j)) :
    E q (fun x => ∏ j ∈ s, F j x) = ∏ j ∈ s, E q (F j) := by
  induction s using Finset.induction_on with
  | empty => simp [E_const]
  | insert j s hj ih =>
    have hA' : (s : Set κ).PairwiseDisjoint A := hA.subset (by simp)
    have hd : Disjoint (A j) (s.biUnion A) := by
      rw [Finset.disjoint_biUnion_right]
      intro k hk
      exact hA (mem_insert_self j s) (mem_insert_of_mem hk) (fun hjk => hj (hjk ▸ hk))
    rw [prod_insert hj, ← ih hA' (fun k hk => h k (mem_insert_of_mem hk))]
    rw [E_congr (G := fun x => F j x * ∏ k ∈ s, F k x) fun x => by rw [prod_insert hj]]
    exact E_mul_of_depOn (h j (mem_insert_self j s))
      (DepOn.prod s F A fun k hk => h k (mem_insert_of_mem hk)) hd

/-! ### Probabilities -/

lemma Pr_eq_E (A : (ι → Bool) → Prop) [DecidablePred A] :
    Pr q A = E q fun x => if A x then 1 else 0 := by
  unfold Pr; congr 1; funext x; congr

lemma Pr_nonneg (hq : IsProb q) (A : (ι → Bool) → Prop) : 0 ≤ Pr q A := by
  classical
  rw [Pr_eq_E]
  exact E_nonneg hq fun x => by split_ifs <;> norm_num

lemma Pr_le_one (hq : IsProb q) (A : (ι → Bool) → Prop) : Pr q A ≤ 1 := by
  classical
  rw [Pr_eq_E]
  calc E q (fun x => if A x then (1 : ℝ) else 0) ≤ E q (fun _ => 1) :=
        E_mono hq fun x => by split_ifs <;> norm_num
    _ = 1 := E_const 1

lemma Pr_congr {A B : (ι → Bool) → Prop} (h : ∀ x, A x ↔ B x) : Pr q A = Pr q B := by
  classical
  rw [Pr_eq_E, Pr_eq_E]
  exact E_congr fun x => by simp only [h x]

lemma Pr_mono (hq : IsProb q) {A B : (ι → Bool) → Prop} (h : ∀ x, A x → B x) :
    Pr q A ≤ Pr q B := by
  classical
  rw [Pr_eq_E, Pr_eq_E]
  exact E_mono hq fun x => by
    by_cases hx : A x
    · simp [hx, h x hx]
    · simp [hx]; split_ifs <;> norm_num

lemma Pr_not (A : (ι → Bool) → Prop) : Pr q (fun x => ¬ A x) = 1 - Pr q A := by
  classical
  have := E_add (q := q) (fun x => if ¬ A x then (1 : ℝ) else 0) (fun x => if A x then 1 else 0)
  rw [E_congr (G := fun _ => (1 : ℝ)) (fun x => by split_ifs <;> simp), E_const] at this
  rw [Pr_eq_E, Pr_eq_E]; linarith

lemma Pr_or_le (hq : IsProb q) (A B : (ι → Bool) → Prop) :
    Pr q (fun x => A x ∨ B x) ≤ Pr q A + Pr q B := by
  classical
  rw [Pr_eq_E, Pr_eq_E, Pr_eq_E, ← E_add]
  exact E_mono hq fun x => by split_ifs <;> simp_all

lemma Pr_exists_le {κ : Type*} (hq : IsProb q) (s : Finset κ) (A : κ → (ι → Bool) → Prop) :
    Pr q (fun x => ∃ j ∈ s, A j x) ≤ ∑ j ∈ s, Pr q (A j) := by
  classical
  simp_rw [Pr_eq_E]
  rw [← E_sum]
  refine E_mono hq fun x => ?_
  by_cases hx : ∃ j ∈ s, A j x
  · obtain ⟨j, hj, hjx⟩ := hx
    rw [if_pos ⟨j, hj, hjx⟩]
    calc (1 : ℝ) = if A j x then 1 else 0 := by simp [hjx]
      _ ≤ ∑ k ∈ s, if A k x then (1 : ℝ) else 0 :=
        single_le_sum (f := fun k => if A k x then (1 : ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) hj
  · rw [if_neg hx]
    exact sum_nonneg fun k _ => by split_ifs <;> norm_num

lemma Pr_and_of_depOn {A B : (ι → Bool) → Prop} {S T : Finset ι}
    (hA : EvDepOn A S) (hB : EvDepOn B T) (hST : Disjoint S T) :
    Pr q (fun x => A x ∧ B x) = Pr q A * Pr q B := by
  classical
  simp_rw [Pr_eq_E]
  rw [← E_mul_of_depOn hA.ind hB.ind hST]
  exact E_congr fun x => by split_ifs <;> simp_all

lemma Pr_forall_of_depOn {κ : Type*} [DecidableEq κ] (s : Finset κ) (A : κ → (ι → Bool) → Prop)
    (S : κ → Finset ι) (hS : (s : Set κ).PairwiseDisjoint S) (h : ∀ j ∈ s, EvDepOn (A j) (S j)) :
    Pr q (fun x => ∀ j ∈ s, A j x) = ∏ j ∈ s, Pr q (A j) := by
  classical
  simp_rw [Pr_eq_E]
  rw [← E_prod_of_depOn s _ S hS fun j hj => (h j hj).ind]
  refine E_congr fun x => ?_
  by_cases hx : ∀ j ∈ s, A j x
  · rw [if_pos hx]; exact (prod_eq_one fun j hj => by simp [hx j hj]).symm
  · rw [if_neg hx]
    push Not at hx
    obtain ⟨j, hj, hjx⟩ := hx
    exact (prod_eq_zero hj (by simp [hjx])).symm

/-- Markov's inequality. -/
lemma Pr_le_E_div (hq : IsProb q) {F : (ι → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) {t : ℝ} (ht : 0 < t) :
    Pr q (fun x => t ≤ F x) ≤ E q F / t := by
  classical
  rw [Pr_eq_E, div_eq_inv_mul, ← E_const_mul]
  refine E_mono hq fun x => ?_
  split_ifs with h
  · rw [← div_eq_inv_mul, le_div_iff₀ ht, one_mul]; exact h
  · exact mul_nonneg (inv_nonneg.2 ht.le) (hF x)

/-- Variance. -/
noncomputable def Var (q : ι → ℝ) (F : (ι → Bool) → ℝ) : ℝ := E q fun x => (F x - E q F) ^ 2

/-- Covariance. -/
noncomputable def Cov (q : ι → ℝ) (F G : (ι → Bool) → ℝ) : ℝ :=
  E q (fun x => F x * G x) - E q F * E q G

lemma Var_eq (F : (ι → Bool) → ℝ) : Var q F = E q (fun x => F x ^ 2) - (E q F) ^ 2 := by
  unfold Var
  have : ∀ x, (F x - E q F) ^ 2 = F x ^ 2 - (2 * E q F) * F x + (E q F) ^ 2 := fun x => by ring
  rw [E_congr this, E_add, E_sub, E_const_mul, E_const]
  ring

lemma Var_eq_Cov (F : (ι → Bool) → ℝ) : Var q F = Cov q F F := by
  rw [Var_eq, Cov, sq (E q F)]; congr 1; exact E_congr fun x => by ring

lemma Var_nonneg (hq : IsProb q) (F : (ι → Bool) → ℝ) : 0 ≤ Var q F :=
  E_nonneg hq fun _ => sq_nonneg _

/-- Chebyshev's inequality. -/
lemma Pr_abs_sub_le (hq : IsProb q) (F : (ι → Bool) → ℝ) {t : ℝ} (ht : 0 < t) :
    Pr q (fun x => t ≤ |F x - E q F|) ≤ Var q F / t ^ 2 := by
  have := Pr_le_E_div hq (F := fun x => (F x - E q F) ^ 2) (fun x => sq_nonneg _) (pow_pos ht 2)
  refine le_trans (le_of_eq (Pr_congr fun x => ?_)) this
  rw [← sq_abs (F x - E q F)]
  exact (pow_le_pow_iff_left₀ ht.le (abs_nonneg _) two_ne_zero).symm

lemma Var_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → Bool) → ℝ) :
    Var q (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, ∑ k ∈ s, Cov q (F j) (F k) := by
  rw [Var_eq, E_sum]
  have h1 : E q (fun x => (∑ j ∈ s, F j x) ^ 2) =
      ∑ j ∈ s, ∑ k ∈ s, E q (fun x => F j x * F k x) := by
    simp_rw [← E_sum]
    exact E_congr fun x => by rw [sq, sum_mul_sum]
  rw [h1, sq, sum_mul_sum]
  simp_rw [Cov, sum_sub_distrib]

lemma Var_ind_le (A : (ι → Bool) → Prop) [DecidablePred A] :
    Var q (fun x => if A x then (1 : ℝ) else 0) ≤ 1 / 4 := by
  rw [Var_eq]
  have h1 : E q (fun x => (if A x then (1 : ℝ) else 0) ^ 2) = E q (fun x => if A x then 1 else 0) :=
    E_congr fun x => by split_ifs <;> norm_num
  rw [h1]
  nlinarith [sq_nonneg (E q (fun x => if A x then (1 : ℝ) else 0) - 1 / 2)]

/-! ### Conditioning on a set of coordinates -/

/-- Overwrite the coordinates in `A` by `a`. -/
def repl (A : Finset ι) (a x : ι → Bool) : ι → Bool := fun i => if i ∈ A then a i else x i

/-- Canonical assignments on `A` (zero outside `A`). -/
def canon (A : Finset ι) : Finset (ι → Bool) := univ.filter fun a => ∀ i, i ∉ A → a i = false

/-- `x` agrees with `a` on `A`. -/
def agree (A : Finset ι) (a x : ι → Bool) : Prop := ∀ i ∈ A, x i = a i

instance (A : Finset ι) (a x : ι → Bool) : Decidable (agree A a x) := by
  unfold agree; infer_instance

lemma repl_of_mem {A : Finset ι} {a x : ι → Bool} {i : ι} (h : i ∈ A) : repl A a x i = a i := by
  simp [repl, h]

lemma repl_of_not_mem {A : Finset ι} {a x : ι → Bool} {i : ι} (h : i ∉ A) : repl A a x i = x i := by
  simp [repl, h]

lemma depOn_repl (F : (ι → Bool) → ℝ) (A : Finset ι) (a : ι → Bool) :
    DepOn (fun x => F (repl A a x)) (univ \ A) := by
  intro x y h
  have : repl A a x = repl A a y := funext fun i => by
    by_cases hi : i ∈ A
    · simp [repl, hi]
    · simp only [repl, hi, if_false]; exact h i (by simp [hi])
  simp only [this]

lemma evDepOn_repl (P : (ι → Bool) → Prop) (A : Finset ι) (a : ι → Bool) :
    EvDepOn (fun x => P (repl A a x)) (univ \ A) := by
  intro x y h
  have : repl A a x = repl A a y := funext fun i => by
    by_cases hi : i ∈ A
    · simp [repl, hi]
    · simp only [repl, hi, if_false]; exact h i (by simp [hi])
  simp only [this]

lemma evDepOn_agree (A : Finset ι) (a : ι → Bool) : EvDepOn (agree A a) A := by
  intro x y h
  exact ⟨fun hx i hi => (h i hi).symm.trans (hx i hi), fun hy i hi => (h i hi).trans (hy i hi)⟩

lemma sum_canon_ind (A : Finset ι) (x : ι → Bool) (G : (ι → Bool) → ℝ) :
    ∑ a ∈ canon A, (if agree A a x then 1 else 0) * G (repl A a x) = G x := by
  classical
  set a₀ : ι → Bool := fun i => if i ∈ A then x i else false with ha₀
  have hmem : a₀ ∈ canon A := by
    simp only [canon, mem_filter, mem_univ, true_and]; intro i hi; simp [ha₀, hi]
  have hag : agree A a₀ x := fun i hi => by simp [ha₀, hi]
  have hrepl : repl A a₀ x = x := funext fun i => by by_cases hi : i ∈ A <;> simp [repl, ha₀, hi]
  rw [sum_eq_single a₀]
  · simp [hag, hrepl]
  · intro a ha hne
    have : ¬ agree A a x := fun h => hne (funext fun i => by
      by_cases hi : i ∈ A
      · simp [ha₀, hi, ← h i hi]
      · simp only [canon, mem_filter] at ha; simp [ha₀, hi, ha.2 i hi])
    simp [this]
  · intro h; exact absurd hmem h

lemma E_condition (A : Finset ι) (F : (ι → Bool) → ℝ) :
    E q F = ∑ a ∈ canon A, Pr q (agree A a) * E q (fun x => F (repl A a x)) := by
  classical
  calc E q F = E q (fun x => ∑ a ∈ canon A, (if agree A a x then 1 else 0) * F (repl A a x)) :=
        E_congr fun x => (sum_canon_ind A x F).symm
    _ = ∑ a ∈ canon A, E q (fun x => (if agree A a x then 1 else 0) * F (repl A a x)) := E_sum ..
    _ = _ := sum_congr rfl fun a _ => by
        rw [E_mul_of_depOn (evDepOn_agree A a).ind (depOn_repl F A a) disjoint_sdiff, Pr_eq_E]

lemma sum_Pr_agree (A : Finset ι) : ∑ a ∈ canon A, Pr q (agree A a) = 1 := by
  have := E_condition (q := q) A (fun _ => 1)
  simp only [E_const, mul_one] at this
  exact this.symm

lemma Pr_condition (A : Finset ι) (P : (ι → Bool) → Prop) :
    Pr q P = ∑ a ∈ canon A, Pr q (agree A a) * Pr q (fun x => P (repl A a x)) := by
  classical
  rw [Pr_eq_E, E_condition A]
  exact sum_congr rfl fun a _ => by rw [Pr_eq_E, Pr_eq_E]

/-! ### Counting coordinates: binomial law -/

/-- Number of `true` coordinates in `T`. -/
def cnt (T : Finset ι) (x : ι → Bool) : ℕ := (T.filter fun i => x i = true).card

/-- Binomial point mass. -/
noncomputable def bin (N k : ℕ) (p : ℝ) : ℝ := N.choose k * p ^ k * (1 - p) ^ (N - k)

lemma cnt_le (T : Finset ι) (x : ι → Bool) : cnt T x ≤ T.card := card_filter_le _ _

lemma cnt_cast (T : Finset ι) (x : ι → Bool) :
    (cnt T x : ℝ) = ∑ i ∈ T, if x i then (1 : ℝ) else 0 := by
  unfold cnt; rw [card_filter]; push_cast; rfl

lemma cnt_congr {T : Finset ι} {x y : ι → Bool} (h : ∀ i ∈ T, x i = y i) : cnt T x = cnt T y := by
  unfold cnt; congr 1; exact filter_congr fun i hi => by rw [h i hi]

lemma depOn_cnt (T : Finset ι) (φ : ℕ → ℝ) : DepOn (fun x => φ (cnt T x)) T :=
  fun _ _ h => by simp only [cnt_congr h]

lemma depOn_cnt2 (T₂ T₃ : Finset ι) (φ : ℕ → ℕ → ℝ) :
    DepOn (fun x => φ (cnt T₂ x) (cnt T₃ x)) (T₂ ∪ T₃) := fun _ _ h => by
  simp only [cnt_congr fun i hi => h i (mem_union_left _ hi),
    cnt_congr fun i hi => h i (mem_union_right _ hi)]

lemma evDepOn_cnt (T : Finset ι) (P : ℕ → Prop) : EvDepOn (fun x => P (cnt T x)) T :=
  fun _ _ h => by simp only [cnt_congr h]

lemma cnt_insert_update_true {T : Finset ι} {i : ι} (hi : i ∉ T) (x : ι → Bool) :
    cnt (insert i T) (Function.update x i true) = cnt T x + 1 := by
  unfold cnt
  rw [filter_insert, if_pos (by simp), card_insert_of_notMem (fun h => hi (mem_filter.1 h).1)]
  congr 2
  exact filter_congr fun j hj => by
    rw [Function.update_of_ne (fun h => hi (by subst h; exact hj))]

lemma cnt_insert_update_false {T : Finset ι} {i : ι} (hi : i ∉ T) (x : ι → Bool) :
    cnt (insert i T) (Function.update x i false) = cnt T x := by
  unfold cnt
  rw [filter_insert, if_neg (by simp)]
  congr 1
  exact filter_congr fun j hj => by
    rw [Function.update_of_ne (fun h => hi (by subst h; exact hj))]

lemma bin_zero_succ (N : ℕ) (p : ℝ) : bin (N + 1) 0 p = (1 - p) * bin N 0 p := by
  simp [bin, pow_succ]; ring

lemma bin_succ_succ (N k : ℕ) (p : ℝ) :
    bin (N + 1) (k + 1) p = p * bin N k p + (1 - p) * bin N (k + 1) p := by
  unfold bin
  rcases lt_or_ge k N with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, N = k + 1 + j := ⟨N - (k + 1), by omega⟩
    have e1 : k + 1 + j + 1 - (k + 1) = j + 1 := by omega
    have e2 : k + 1 + j - k = j + 1 := by omega
    have e3 : k + 1 + j - (k + 1) = j := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ]; push_cast; ring
  · have e1 : N + 1 - (k + 1) = 0 := by omega
    have e2 : N - k = 0 := by omega
    rw [e1, e2, Nat.choose_succ_succ, Nat.choose_eq_zero_of_lt (by omega : N < k + 1)]
    push_cast; ring

lemma Pr_cnt_eq {T : Finset ι} {p : ℝ} (hT : ∀ i ∈ T, q i = p) (k : ℕ) :
    Pr q (fun x => cnt T x = k) = bin T.card k p := by
  classical
  induction T using Finset.induction_on generalizing k with
  | empty =>
    rw [Pr_eq_E]
    simp only [cnt, filter_empty, card_empty]
    rw [E_const]
    cases k <;> simp [bin]
  | insert i T hi ih =>
    have hp : q i = p := hT i (mem_insert_self i T)
    have hT' : ∀ j ∈ T, q j = p := fun j hj => hT j (mem_insert_of_mem hj)
    rw [Pr_eq_E, ← E_Ei i]
    have : Ei q i (fun x => if cnt (insert i T) x = k then (1 : ℝ) else 0) =
        fun x => p * (if cnt T x + 1 = k then 1 else 0) + (1 - p) * (if cnt T x = k then 1 else 0) := by
      funext x
      simp only [Ei, cnt_insert_update_true hi, cnt_insert_update_false hi, hp]
    rw [this, E_add, E_const_mul, E_const_mul, ← Pr_eq_E, ← Pr_eq_E, ih hT' k,
      card_insert_of_notMem hi]
    cases k with
    | zero =>
      rw [bin_zero_succ]
      have : Pr q (fun x => cnt T x + 1 = 0) = 0 := by
        rw [Pr_eq_E]; simp [E_const]
      rw [this]; ring
    | succ k =>
      rw [bin_succ_succ, ← ih hT' k]
      simp

/-- Law of total probability over the count on `T`, for a functional whose remaining
dependence is on coordinates disjoint from `T`. -/
lemma E_cnt {T B : Finset ι} {p : ℝ} (hT : ∀ i ∈ T, q i = p) (ψ : ℕ → (ι → Bool) → ℝ)
    (hψ : ∀ k, DepOn (ψ k) B) (hTB : Disjoint T B) :
    E q (fun x => ψ (cnt T x) x) = ∑ k ∈ range (T.card + 1), bin T.card k p * E q (ψ k) := by
  classical
  have h1 : ∀ x, ψ (cnt T x) x =
      ∑ k ∈ range (T.card + 1), (if cnt T x = k then 1 else 0) * ψ k x := fun x => by
    rw [sum_eq_single (cnt T x)]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (mem_range.2 (Nat.lt_succ_of_le (cnt_le T x))) h
  rw [E_congr h1, E_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [E_mul_of_depOn ((evDepOn_cnt T (fun m => m = k)).ind) (hψ k) hTB, ← Pr_eq_E, Pr_cnt_eq hT]

lemma E_cnt_fun {T : Finset ι} {p : ℝ} (hT : ∀ i ∈ T, q i = p) (φ : ℕ → ℝ) :
    E q (fun x => φ (cnt T x)) = ∑ k ∈ range (T.card + 1), bin T.card k p * φ k := by
  rw [E_cnt hT (fun k _ => φ k) (fun k => DepOn.const _ ∅) (disjoint_empty_right T)]
  simp [E_const]

lemma E_cnt2 {T₁ T₂ : Finset ι} {p : ℝ} (h₁ : ∀ i ∈ T₁, q i = p) (h₂ : ∀ i ∈ T₂, q i = p)
    (hd : Disjoint T₁ T₂) (φ : ℕ → ℕ → ℝ) :
    E q (fun x => φ (cnt T₁ x) (cnt T₂ x)) =
      ∑ k₁ ∈ range (T₁.card + 1), ∑ k₂ ∈ range (T₂.card + 1),
        bin T₁.card k₁ p * bin T₂.card k₂ p * φ k₁ k₂ := by
  rw [E_cnt h₁ (fun k x => φ k (cnt T₂ x)) (fun k => depOn_cnt T₂ (φ k)) hd]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [E_cnt_fun h₂, mul_sum]
  exact sum_congr rfl fun k₂ _ => by ring

lemma E_cnt3 {T₁ T₂ T₃ : Finset ι} {p : ℝ} (h₁ : ∀ i ∈ T₁, q i = p) (h₂ : ∀ i ∈ T₂, q i = p)
    (h₃ : ∀ i ∈ T₃, q i = p) (h₁₂ : Disjoint T₁ T₂) (h₁₃ : Disjoint T₁ T₃) (h₂₃ : Disjoint T₂ T₃)
    (φ : ℕ → ℕ → ℕ → ℝ) :
    E q (fun x => φ (cnt T₁ x) (cnt T₂ x) (cnt T₃ x)) =
      ∑ k₁ ∈ range (T₁.card + 1), bin T₁.card k₁ p *
        ∑ k₂ ∈ range (T₂.card + 1), ∑ k₃ ∈ range (T₃.card + 1),
          bin T₂.card k₂ p * bin T₃.card k₃ p * φ k₁ k₂ k₃ := by
  rw [E_cnt h₁ (fun k x => φ k (cnt T₂ x) (cnt T₃ x)) (fun k => depOn_cnt2 T₂ T₃ (φ k))
    (disjoint_union_right.2 ⟨h₁₂, h₁₃⟩)]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [E_cnt2 h₂ h₃ h₂₃]

/-- Mean of a coordinate count. -/
lemma E_cnt_mean (T : Finset ι) : E q (fun x => (cnt T x : ℝ)) = ∑ i ∈ T, q i := by
  rw [E_congr (cnt_cast T), E_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← E_Ei i]
  have : Ei q i (fun x => if x i then (1 : ℝ) else 0) = fun _ => q i := by
    funext x; simp [Ei]
  rw [this, E_const]

lemma E_ind_coord (i : ι) : E q (fun x => if x i then (1 : ℝ) else 0) = q i := by
  rw [← E_Ei i]
  have : Ei q i (fun x => if x i then (1 : ℝ) else 0) = fun _ => q i := by
    funext x; simp [Ei]
  rw [this, E_const]

/-- Variance of a coordinate count. -/
lemma Var_cnt (T : Finset ι) : Var q (fun x => (cnt T x : ℝ)) = ∑ i ∈ T, q i * (1 - q i) := by
  have hV : Var q (fun x => (cnt T x : ℝ)) =
      Var q (fun x => ∑ i ∈ T, if x i then (1 : ℝ) else 0) := by
    unfold Var; rw [E_congr (cnt_cast T)]; exact E_congr fun x => by simp only [cnt_cast]
  rw [hV, Var_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_eq_single i]
  · rw [Cov, E_ind_coord]
    have : E q (fun x => (if x i then (1 : ℝ) else 0) * if x i then 1 else 0) =
        E q (fun x => if x i then (1 : ℝ) else 0) := E_congr fun x => by split_ifs <;> simp
    rw [this, E_ind_coord]; ring
  · intro j _ hji
    rw [Cov, E_mul_of_depOn (A := {i}) (B := {j})
      (fun x y h => by simp [h i (mem_singleton_self i)])
      (fun x y h => by simp [h j (mem_singleton_self j)])
      (by simpa using Ne.symm hji)]
    ring
  · intro h; exact absurd hi h

/-- Moment generating function of a coordinate count. -/
lemma E_exp_cnt {T : Finset ι} {p : ℝ} (hT : ∀ i ∈ T, q i = p) (θ : ℝ) :
    E q (fun x => Real.exp (θ * cnt T x)) = (1 - p + p * Real.exp θ) ^ T.card := by
  rw [E_cnt_fun hT (fun k => Real.exp (θ * k)), add_comm (1 - p) (p * Real.exp θ), add_pow]
  refine sum_congr rfl fun k _ => ?_
  rw [bin, mul_comm θ, Real.exp_nat_mul, mul_pow]
  ring

end MD
