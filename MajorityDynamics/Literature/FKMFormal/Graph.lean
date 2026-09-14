import MajorityDynamics.Literature.FKMFormal.Core

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! # Deterministic facts about the encoding, neighbourhood counts and the dynamics. -/

namespace MD

open Finset

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}

/-! ### Extra generic probability lemmas -/

lemma E_neg (F : (ι → Bool) → ℝ) : E q (fun x => -F x) = -E q F := by
  unfold E; rw [← sum_neg_distrib]; exact sum_congr rfl fun x _ => by ring

lemma abs_E_le (hq : IsProb q) (F : (ι → Bool) → ℝ) : |E q F| ≤ E q (fun x => |F x|) := by
  rw [abs_le]; constructor
  · have := E_mono hq (F := fun x => -|F x|) (G := F) fun x => neg_abs_le _
    rwa [E_neg] at this
  · exact E_mono hq fun x => le_abs_self _

lemma E_update (i : ι) (F : (ι → Bool) → ℝ) :
    E q F = q i * E q (fun x => F (Function.update x i true)) +
      (1 - q i) * E q (fun x => F (Function.update x i false)) := by
  rw [← E_Ei i F]; unfold Ei; rw [E_add, E_const_mul, E_const_mul]

lemma DepOn.update {F : (ι → Bool) → ℝ} {A : Finset ι} {i : ι} (h : DepOn F (insert i A))
    (b : Bool) : DepOn (fun x => F (Function.update x i b)) A := by
  intro x y hxy
  apply h; intro j hj
  by_cases hji : j = i
  · subst hji; simp
  · rw [Function.update_of_ne hji, Function.update_of_ne hji]
    exact hxy j ((mem_insert.1 hj).resolve_left hji)

/-- Covariance of two functions sharing exactly one coordinate `i`. -/
lemma Cov_update {F G : (ι → Bool) → ℝ} {A B : Finset ι} {i : ι}
    (hF : DepOn F (insert i A)) (hG : DepOn G (insert i B)) (hAB : Disjoint A B) :
    Cov q F G = q i * (1 - q i) *
      (E q (fun x => F (Function.update x i true)) - E q (fun x => F (Function.update x i false))) *
      (E q (fun x => G (Function.update x i true)) - E q (fun x => G (Function.update x i false))) := by
  unfold Cov
  rw [E_update i (fun x => F x * G x), E_update i F, E_update i G]
  rw [E_mul_of_depOn (hF.update true) (hG.update true) hAB,
    E_mul_of_depOn (hF.update false) (hG.update false) hAB]
  ring

lemma cnt_mono {A B : Finset ι} (h : A ⊆ B) (x : ι → Bool) : cnt A x ≤ cnt B x :=
  card_le_card (filter_subset_filter _ h)

lemma cnt_union_le (A B : Finset ι) (x : ι → Bool) : cnt (A ∪ B) x ≤ cnt A x + cnt B x := by
  unfold cnt; rw [filter_union]; exact card_union_le _ _

lemma cnt_union {A B : Finset ι} (h : Disjoint A B) (x : ι → Bool) :
    cnt (A ∪ B) x = cnt A x + cnt B x := by
  unfold cnt; rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

lemma cnt_update_of_not_mem {T : Finset ι} {i : ι} (hi : i ∉ T) (x : ι → Bool) (b : Bool) :
    cnt T (Function.update x i b) = cnt T x :=
  cnt_congr fun j hj => Function.update_of_ne (fun h => hi (by rw [← h]; exact hj)) _ _

lemma cnt_insert_update {T : Finset ι} {i : ι} (hi : i ∉ T) (x : ι → Bool) (b : Bool) :
    cnt (insert i T) (Function.update x i b) = cnt T x + if b then 1 else 0 := by
  cases b
  · simpa using cnt_insert_update_false hi x
  · simpa using cnt_insert_update_true hi x

lemma E_ind_coord_bool (i : ι) : E q (fun x => if x i = true then (1 : ℝ) else 0) = q i :=
  E_ind_coord i

end Generic

/-! ### The encoding of edges -/

variable {n : ℕ}

lemma edge_comm (u w : Fin n) : edge u w = edge w u := by
  unfold edge
  by_cases h : u = w
  · subst h; simp
  · rw [dif_neg h, dif_neg (Ne.symm h)]
    congr 1; exact Subtype.ext Sym2.eq_swap

lemma edge_inj {u w w' : Fin n} (hw : w ≠ u) (hw' : w' ≠ u) (h : edge u w = edge u w') :
    w = w' := by
  unfold edge at h
  rw [dif_neg (Ne.symm hw), dif_neg (Ne.symm hw')] at h
  have := congrArg Subtype.val (Sum.inr.inj h)
  rcases Sym2.eq_iff.1 this with ⟨-, h⟩ | ⟨h1, -⟩
  · exact h
  · exact (hw' h1.symm).elim

lemma edge_ne_inl {u w : Fin n} (hw : w ≠ u) (v : Fin n) : edge u w ≠ Sum.inl v := by
  unfold edge; rw [dif_neg (Ne.symm hw)]; simp

lemma edge_eq_edge {u w u' w' : Fin n} (hw : w ≠ u) (hw' : w' ≠ u')
    (h : edge u w = edge u' w') : (u = u' ∧ w = w') ∨ (u = w' ∧ w = u') := by
  unfold edge at h
  rw [dif_neg (Ne.symm hw), dif_neg (Ne.symm hw')] at h
  exact Sym2.eq_iff.1 (congrArg Subtype.val (Sum.inr.inj h))

lemma q_edge (p : ℝ) {u w : Fin n} (hw : w ≠ u) : q n p (edge u w) = p := by
  unfold edge q; rw [dif_neg (Ne.symm hw)]; simp

lemma isProb_q {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProb (q n p) := by
  rintro (v | e)
  · simp [q]; norm_num
  · simpa [q] using ⟨h0, h1⟩

lemma adj_comm (x : Ω n) (u w : Fin n) : adj x u w ↔ adj x w u := by
  unfold adj; rw [edge_comm]; exact and_congr ne_comm Iff.rfl

/-! ### Stars: the edge coordinates from a vertex into a vertex set -/

/-- Edge coordinates from `u` to the vertices of `A` (other than `u`). -/
def star (u : Fin n) (A : Finset (Fin n)) : Finset (Fin n ⊕ Edge n) := (A.erase u).image (edge u)

lemma mem_star {u w : Fin n} {A : Finset (Fin n)} (hw : w ≠ u) : edge u w ∈ star u A ↔ w ∈ A := by
  unfold star; rw [mem_image]; constructor
  · rintro ⟨w', hw', h⟩
    obtain ⟨hne, hA⟩ := mem_erase.1 hw'
    rwa [edge_inj hne hw h] at hA
  · intro h; exact ⟨w, mem_erase.2 ⟨hw, h⟩, rfl⟩

lemma mem_star_iff {u : Fin n} {A : Finset (Fin n)} {e : Fin n ⊕ Edge n} :
    e ∈ star u A ↔ ∃ w ∈ A, w ≠ u ∧ e = edge u w := by
  unfold star; simp only [mem_image, mem_erase]
  constructor
  · rintro ⟨w, ⟨h1, h2⟩, h3⟩; exact ⟨w, h2, h1, h3.symm⟩
  · rintro ⟨w, h2, h1, h3⟩; exact ⟨w, ⟨h1, h2⟩, h3.symm⟩

lemma inl_not_mem_star (u v : Fin n) (A : Finset (Fin n)) : Sum.inl v ∉ star u A := by
  rw [mem_star_iff]; rintro ⟨w, -, hw, h⟩; exact edge_ne_inl hw v h.symm

lemma q_star (p : ℝ) (u : Fin n) (A : Finset (Fin n)) : ∀ i ∈ star u A, q n p i = p := by
  intro i hi; obtain ⟨w, -, hw, rfl⟩ := mem_star_iff.1 hi; exact q_edge p hw

lemma card_star (u : Fin n) (A : Finset (Fin n)) : (star u A).card = (A.erase u).card :=
  card_image_of_injOn fun _w hw _w' hw' h =>
    edge_inj (mem_erase.1 hw).1 (mem_erase.1 hw').1 h

lemma card_star_le (u : Fin n) (A : Finset (Fin n)) : (star u A).card ≤ A.card :=
  (card_star u A).le.trans (card_erase_le)

lemma cnt_star (x : Ω n) (u : Fin n) (A : Finset (Fin n)) :
    cnt (star u A) x = ((A.erase u).filter fun w => x (edge u w) = true).card := by
  unfold cnt star
  rw [filter_image]
  exact card_image_of_injOn fun _w hw _w' hw' h =>
    edge_inj (mem_erase.1 (mem_filter.1 hw).1).1 (mem_erase.1 (mem_filter.1 hw').1).1 h

lemma star_subset {u : Fin n} {A B : Finset (Fin n)} (h : A ⊆ B) : star u A ⊆ star u B :=
  image_subset_image (erase_subset_erase _ h)

lemma star_union (u : Fin n) (A B : Finset (Fin n)) : star u (A ∪ B) = star u A ∪ star u B := by
  unfold star; rw [erase_union_distrib, image_union]

lemma star_disjoint {u : Fin n} {A B : Finset (Fin n)} (h : Disjoint A B) :
    Disjoint (star u A) (star u B) := by
  rw [disjoint_left]; intro e he he'
  obtain ⟨w, hwA, hw, rfl⟩ := mem_star_iff.1 he
  obtain ⟨w', hw'B, hw', h'⟩ := mem_star_iff.1 he'
  rw [edge_inj hw hw' h'] at hwA
  exact disjoint_left.1 h hwA hw'B

lemma star_disjoint_of_ne {u u' : Fin n} {A A' : Finset (Fin n)} (huu' : u ≠ u') (hu : u ∉ A') :
    Disjoint (star u A) (star u' A') := by
  rw [disjoint_left]; intro e he he'
  obtain ⟨w, -, hw, rfl⟩ := mem_star_iff.1 he
  obtain ⟨w', hw'A, hw', h'⟩ := mem_star_iff.1 he'
  rcases edge_eq_edge hw hw' h' with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact huu' h1
  · exact hu (h1 ▸ hw'A)

lemma star_erase {u v : Fin n} {A : Finset (Fin n)} (hv : v ≠ u) (hvA : v ∈ A) :
    star u A = insert (edge u v) (star u (A.erase v)) := by
  ext e
  rw [mem_insert, mem_star_iff, mem_star_iff]
  constructor
  · rintro ⟨w, hw, hwu, rfl⟩
    by_cases hwv : w = v
    · subst hwv; exact Or.inl rfl
    · exact Or.inr ⟨w, mem_erase.2 ⟨hwv, hw⟩, hwu, rfl⟩
  · rintro (rfl | ⟨w, hw, hwu, rfl⟩)
    · exact ⟨v, hvA, hv, rfl⟩
    · exact ⟨w, (mem_erase.1 hw).2, hwu, rfl⟩

lemma edge_not_mem_star_erase (u v : Fin n) (A : Finset (Fin n)) :
    edge u v ∉ star u (A.erase v) := by
  rw [mem_star_iff]; rintro ⟨w, hw, hwu, h⟩
  by_cases hvu : v = u
  · exact edge_ne_inl hwu u (by rw [← h, hvu]; unfold edge; simp)
  · exact (mem_erase.1 hw).1 (edge_inj hwu hvu h.symm)

/-- Counting along a star after fixing the coordinate `edge u v`. -/
lemma cnt_star_update {u v : Fin n} (hv : v ≠ u) (A : Finset (Fin n)) (x : Ω n) (b : Bool) :
    cnt (star u A) (Function.update x (edge u v) b) =
      cnt (star u (A.erase v)) x + if v ∈ A ∧ b then 1 else 0 := by
  by_cases hvA : v ∈ A
  · rw [star_erase hv hvA, cnt_insert_update (edge_not_mem_star_erase u v A)]
    simp [hvA]
  · rw [erase_eq_of_notMem hvA, cnt_update_of_not_mem (by rwa [mem_star hv]) x b]
    simp [hvA]

lemma cnt_star_erase {u v : Fin n} (hv : v ≠ u) (A : Finset (Fin n)) (x : Ω n) :
    cnt (star u A) x = cnt (star u (A.erase v)) x + if v ∈ A ∧ x (edge u v) then 1 else 0 := by
  have := cnt_star_update hv A x (x (edge u v))
  rwa [Function.update_eq_self] at this

/-! ### Neighbour sums via stars -/

/-- Vertices in state `b`. -/
def sset (s : Fin n → Bool) (b : Bool) : Finset (Fin n) := univ.filter fun w => s w = b

lemma sset_disjoint (s : Fin n → Bool) : Disjoint (sset s true) (sset s false) := by
  rw [disjoint_left]; intro w h1 h2
  simp only [sset, mem_filter] at h1 h2; rw [h1.2] at h2; exact Bool.noConfusion h2.2

lemma sset_union (s : Fin n → Bool) : sset s true ∪ sset s false = univ := by
  ext w; simp only [sset, mem_union, mem_filter, mem_univ, true_and]
  cases s w <;> simp

lemma card_sset_add (s : Fin n → Bool) : (sset s true).card + (sset s false).card = n := by
  rw [← card_union_of_disjoint (sset_disjoint s), sset_union, card_univ, Fintype.card_fin]

lemma sset_false_eq (s : Fin n → Bool) : sset s false = univ \ sset s true := by
  ext w; simp only [sset, mem_filter, mem_univ, true_and, mem_sdiff]; cases s w <;> simp

lemma sset_true_eq (s : Fin n → Bool) : sset s true = univ \ sset s false := by
  ext w; simp only [sset, mem_filter, mem_univ, true_and, mem_sdiff]; cases s w <;> simp

lemma nsum_eq_cnt (x : Ω n) (s : Fin n → Bool) (u : Fin n) :
    nsum x s u = (cnt (star u (sset s true)) x : ℤ) - cnt (star u (sset s false)) x := by
  unfold nsum
  rw [cnt_star, cnt_star, ← sum_filter]
  have hval : ∀ w, val (s w) = if s w = true then (1 : ℤ) else -1 := fun w => by
    unfold val; cases s w <;> simp
  simp_rw [hval]
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_neg_one]
  have e1 : (univ.filter fun w => adj x u w).filter (fun w => s w = true) =
      ((sset s true).erase u).filter (fun w => x (edge u w) = true) := by
    ext w; simp only [mem_filter, mem_univ, true_and, mem_erase, sset]; unfold adj
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨Ne.symm h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨Ne.symm h1, h2⟩, h3⟩
  have e2 : (univ.filter fun w => adj x u w).filter (fun w => ¬ s w = true) =
      ((sset s false).erase u).filter (fun w => x (edge u w) = true) := by
    ext w; simp only [mem_filter, mem_univ, true_and, mem_erase, sset, Bool.not_eq_true]; unfold adj
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨Ne.symm h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨Ne.symm h1, h2⟩, h3⟩
  rw [e1, e2]; ring

lemma nsum_congr {x y : Ω n} (s : Fin n → Bool) (u : Fin n)
    (h : ∀ i ∈ star u univ, x i = y i) : nsum x s u = nsum y s u := by
  rw [nsum_eq_cnt, nsum_eq_cnt,
    cnt_congr fun i hi => h i (star_subset (subset_univ _) hi),
    cnt_congr fun i hi => h i (star_subset (subset_univ _) hi)]

lemma step_congr {x y : Ω n} (s : Fin n → Bool) (u : Fin n)
    (h : ∀ i ∈ star u univ, x i = y i) : step x s u = step y s u := by
  unfold step; rw [nsum_congr s u h]

lemma step_pos {x : Ω n} {s : Fin n → Bool} {u : Fin n} (h : 0 < nsum x s u) :
    step x s u = true := by unfold step; rw [if_pos h]

lemma nsum_nonpos_of_step_false {x : Ω n} {s : Fin n → Bool} {u : Fin n}
    (h : step x s u = false) : nsum x s u ≤ 0 := by
  by_contra h'; rw [step_pos (not_le.1 h')] at h; exact Bool.noConfusion h

/-! ### Dynamics from a prescribed initial state -/

/-- State after `t` rounds started from `s₀` on the graph encoded in `x`. -/
def Sfix (x : Ω n) (s₀ : Fin n → Bool) : ℕ → Fin n → Bool
  | 0 => s₀
  | t + 1 => step x (Sfix x s₀ t)

lemma S_eq_Sfix (x : Ω n) (t : ℕ) : S x t = Sfix x (init x) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [S, Sfix, ih]

lemma Sfix_congr {x y : Ω n} (s₀ : Fin n → Bool) (h : ∀ e, x (Sum.inr e) = y (Sum.inr e)) (t : ℕ) :
    Sfix x s₀ t = Sfix y s₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext u
    simp only [Sfix, ih]
    apply step_congr; intro i hi
    obtain ⟨w, -, hw, rfl⟩ := mem_star_iff.1 hi
    unfold edge; rw [dif_neg (Ne.symm hw)]; exact h _

/-! ### Global sign flip -/

/-- Negate all initial states, keep the graph. -/
def flip (x : Ω n) : Ω n := fun i => match i with
  | Sum.inl v => !x (Sum.inl v)
  | Sum.inr e => x (Sum.inr e)

lemma flip_flip (x : Ω n) : flip (flip x) = x := by
  funext i; cases i <;> simp [flip]

lemma val_not (b : Bool) : val (!b) = -val b := by cases b <;> simp [val]

lemma nsum_not (x : Ω n) (s : Fin n → Bool) (u : Fin n) :
    nsum x (fun w => !s w) u = -nsum x s u := by
  unfold nsum; rw [← sum_neg_distrib]
  exact sum_congr rfl fun w _ => by split_ifs <;> simp [val_not]

lemma step_not (x : Ω n) (s : Fin n → Bool) (u : Fin n) :
    step x (fun w => !s w) u = !step x s u := by
  unfold step; rw [nsum_not]
  rcases lt_trichotomy (nsum x s u) 0 with h | h | h
  · simp [h, h.le.not_gt]
  · simp [h]
  · simp [h, h.le.not_gt]

lemma Sfix_not (x : Ω n) (s₀ : Fin n → Bool) (t : ℕ) :
    Sfix x (fun v => !s₀ v) t = fun v => !Sfix x s₀ t v := by
  induction t with
  | zero => rfl
  | succ t ih => funext u; simp only [Sfix, ih, step_not]

lemma S_flip (x : Ω n) (t : ℕ) : S (flip x) t = fun v => !S x t v := by
  rw [S_eq_Sfix, S_eq_Sfix, Sfix_congr (x := flip x) (y := x) (init (flip x)) (fun e => rfl)]
  have : init (flip x) = fun v => !init x v := by funext v; rfl
  rw [this, Sfix_not]

lemma tot_flip (x : Ω n) : tot (flip x) = -tot x := by
  unfold tot; rw [← sum_neg_distrib]
  exact sum_congr rfl fun v _ => by simp [init, flip, val_not]

lemma Good_flip (x : Ω n) : Good (flip x) ↔ Good x := by
  unfold Good; rw [S_flip, tot_flip]
  simp only [val_not, Int.sign_neg, neg_inj]

lemma wt_flip (p : ℝ) (x : Ω n) : wt (q n p) (flip x) = wt (q n p) x := by
  unfold wt
  refine prod_congr rfl fun i _ => ?_
  cases i with
  | inl v => simp [flip, q]; cases x (Sum.inl v) <;> norm_num
  | inr e => rfl

lemma E_flip (p : ℝ) (F : Ω n → ℝ) : E (q n p) (fun x => F (flip x)) = E (q n p) F := by
  unfold E
  have hinv : Function.Involutive (flip (n := n)) := flip_flip
  rw [← Equiv.sum_comp hinv.toPerm (fun y => wt (q n p) y * F y)]
  exact sum_congr rfl fun x _ => by simp only [Function.Involutive.coe_toPerm, wt_flip]

lemma Pr_flip (p : ℝ) (A : Ω n → Prop) : Pr (q n p) (fun x => A (flip x)) = Pr (q n p) A := by
  classical
  unfold Pr; exact E_flip p (fun x => if A x then 1 else 0)

/-! ### The last two rounds are deterministic given two graph properties -/

/-- Rounds 3 and 4 finish the job: if at most `n/10` vertices are `-1` after round 2, then
property (i) (few vertices see a non-positive majority against any small set) and (ii)
(minimum degree `≥ 2w`) force unanimity. -/
lemma final_rounds (x : Ω n) (s : Fin n → Bool) {w : ℕ}
    (hP₁ : ∀ N : Finset (Fin n), 10 * N.card ≤ n →
      (univ.filter fun v => cnt (star v (univ \ N)) x ≤ cnt (star v N) x).card < w)
    (hP₂ : ∀ v, 2 * w ≤ cnt (star v univ) x)
    (hN : 10 * (sset s false).card ≤ n) :
    ∀ v, step x (step x s) v = true := by
  intro v
  set s₃ := step x s
  have hsub : sset s₃ false ⊆
      univ.filter fun v => cnt (star v (univ \ sset s false)) x ≤ cnt (star v (sset s false)) x := by
    intro u hu
    rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
    have := nsum_nonpos_of_step_false (mem_filter.1 hu).2
    rw [nsum_eq_cnt, sset_true_eq] at this
    omega
  have h3 : (sset s₃ false).card < w := lt_of_le_of_lt (card_le_card hsub) (hP₁ _ hN)
  apply step_pos
  rw [nsum_eq_cnt]
  have hdeg := hP₂ v
  have hsplit : cnt (star v univ) x = cnt (star v (sset s₃ true)) x + cnt (star v (sset s₃ false)) x := by
    rw [← sset_union s₃, star_union, cnt_union (star_disjoint (sset_disjoint s₃))]
  have hle : cnt (star v (sset s₃ false)) x ≤ (sset s₃ false).card :=
    (cnt_le _ _).trans (card_star_le _ _)
  omega

end MD
