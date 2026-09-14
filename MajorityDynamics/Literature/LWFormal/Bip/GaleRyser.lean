import MajorityDynamics.Literature.LWFormal.Bip.Counting

set_option autoImplicit true

/-!
# Realizability of bipartite degree sequences (Gale–Ryser)

`GR s t`: `∑_{v ∈ X} t_v ≤ ∑_a min(s_a, |X|)` for all `X ⊆ T`.  Together with `∑ s = ∑ t` this is
sufficient (and necessary) for the existence of a bipartite graph with degrees `(s, t)`.
We prove sufficiency by induction on the number of edges, and deduce the analogue of
Lemma 2.5: near-regular balanced sequences are realizable.
-/

namespace LW.Bip

open Finset

variable {ℓ n : ℕ}

/-- The Gale–Ryser condition. -/
def GR (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : Prop :=
  ∀ X : Finset (Fin n), ∑ v ∈ X, t v ≤ ∑ a, min (s a) X.card

/-- A set of `k` vertices of `S` of largest `s`-value. -/
theorem exists_top (s : Fin ℓ → ℕ) (k : ℕ) (hk : k ≤ ℓ) :
    ∃ A : Finset (Fin ℓ), A.card = k ∧ ∀ a ∈ A, ∀ a' ∉ A, s a' ≤ s a := by
  induction k with
  | zero => exact ⟨∅, card_empty, fun a ha => absurd ha (notMem_empty a)⟩
  | succ k ih =>
    obtain ⟨A, hA, hmax⟩ := ih (by omega)
    have hne : (Aᶜ).Nonempty := by
      rw [← card_pos, card_compl, Fintype.card_fin]; omega
    obtain ⟨a₀, ha₀, hmax₀⟩ := exists_max_image Aᶜ s hne
    have ha₀A : a₀ ∉ A := mem_compl.1 ha₀
    refine ⟨insert a₀ A, by rw [card_insert_of_notMem ha₀A, hA], fun a ha a' ha' => ?_⟩
    have ha'A : a' ∉ A := fun h => ha' (mem_insert_of_mem h)
    rcases mem_insert.1 ha with rfl | ha
    · exact hmax₀ a' (mem_compl.2 ha'A)
    · exact hmax a ha a' ha'A

theorem ldeg_union_prod (E : BGraph ℓ n) (A : Finset (Fin ℓ)) (v : Fin n)
    (hdisj : ∀ a, (a, v) ∉ E) (a : Fin ℓ) :
    ldeg (E ∪ A ×ˢ {v}) a = ldeg E a + if a ∈ A then 1 else 0 := by
  unfold ldeg
  rw [filter_union, card_union_of_disjoint]
  · congr 1
    split_ifs with h
    · rw [card_eq_one]; refine ⟨(a, v), ?_⟩; ext ⟨b, w⟩
      simp only [mem_filter, mem_product, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hb, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨h, rfl⟩, rfl⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro ⟨b, w⟩ hb rfl
      exact h (mem_product.1 hb).1
  · rw [disjoint_left]
    rintro ⟨b, w⟩ hb hb'
    simp only [mem_filter, mem_product, mem_singleton] at hb hb'
    exact hdisj b (hb'.1.2 ▸ hb.1)

theorem rdeg_union_prod (E : BGraph ℓ n) (A : Finset (Fin ℓ)) (v : Fin n)
    (hdisj : ∀ a, (a, v) ∉ E) (w : Fin n) :
    rdeg (E ∪ A ×ˢ {v}) w = rdeg E w + if w = v then A.card else 0 := by
  unfold rdeg
  rw [filter_union, card_union_of_disjoint]
  · congr 1
    split_ifs with h
    · subst h
      rw [filter_true_of_mem fun p hp => (mem_singleton.1 (mem_product.1 hp).2), card_product,
        card_singleton, mul_one]
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro ⟨b, w'⟩ hb rfl
      exact h (mem_singleton.1 (mem_product.1 hb).2)
  · rw [disjoint_left]
    rintro ⟨b, w'⟩ hb hb'
    simp only [mem_filter, mem_product, mem_singleton] at hb hb'
    exact hdisj b (hb'.1.2 ▸ hb.1)

/-- Sufficiency in the Gale–Ryser theorem. -/
theorem gale_ryser (s : Fin ℓ → ℕ) (t : Fin n → ℕ) (hsum : ∑ a, s a = ∑ v, t v) (hGR : GR s t) :
    ∃ E : BGraph ℓ n, (∀ a, ldeg E a = s a) ∧ ∀ v, rdeg E v = t v := by
  induction' hm : ∑ v, t v using Nat.strong_induction_on with m ih generalizing s t
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · refine ⟨∅, fun a => ?_, fun v => ?_⟩
    · have := (sum_eq_zero_iff.1 (hsum.trans hm)) a (mem_univ a)
      simp [ldeg, this]
    · have := (sum_eq_zero_iff.1 hm) v (mem_univ v)
      simp [rdeg, this]
  -- pick `v` with `t v > 0`
  obtain ⟨v, -, hv⟩ : ∃ v ∈ univ, 0 < t v := by
    by_contra h
    push Not at h
    have : ∑ v, t v = 0 := sum_eq_zero fun v hv => Nat.le_zero.1 (h v hv)
    omega
  set k := t v with hk
  -- `k ≤ #{a | 1 ≤ s a} ≤ ℓ`
  have hk1 : k ≤ (univ.filter fun a => 1 ≤ s a).card := by
    have := hGR {v}
    rw [sum_singleton, card_singleton] at this
    refine this.trans (le_of_eq ?_)
    rw [card_eq_sum_ones, sum_filter]
    exact sum_congr rfl fun a _ => by split_ifs <;> omega
  have hkℓ : k ≤ ℓ := hk1.trans ((card_le_univ _).trans_eq (Fintype.card_fin _))
  obtain ⟨A, hA, hmax⟩ := exists_top s k hkℓ
  -- all of `A` has positive degree
  have hA1 : ∀ a ∈ A, 1 ≤ s a := by
    intro a ha
    by_contra h0
    have h0 : s a = 0 := by omega
    have hsub : univ.filter (fun a => 1 ≤ s a) ⊆ A.erase a := by
      intro a' ha'
      rw [mem_filter] at ha'
      rw [mem_erase]
      refine ⟨fun h => by subst h; omega, ?_⟩
      by_contra ha'A
      have := hmax a ha a' ha'A
      omega
    have := card_le_card hsub
    rw [card_erase_of_mem ha, hA] at this
    omega
  set s' : Fin ℓ → ℕ := fun a => s a - if a ∈ A then 1 else 0 with hs'
  set t' : Fin n → ℕ := Function.update t v 0 with ht'
  have hs'A : ∀ a, s a = s' a + if a ∈ A then 1 else 0 := by
    intro a; simp only [hs']; split_ifs with h
    · have := hA1 a h; omega
    · rfl
  have hcard : ∑ a, (if a ∈ A then 1 else 0) = k := by
    rw [sum_boole]; simp [hA]
  have hsum_s' : ∑ a, s' a = m - k := by
    have h1 : ∑ a, s a = ∑ a, s' a + k := by
      rw [sum_congr rfl fun a _ => hs'A a, sum_add_distrib, hcard]
    omega
  have hsum_t' : ∑ w, t' w = m - k := by
    have : ∑ w, t w = ∑ w, t' w + k := by
      rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v)]
      simp only [ht', Function.update_self, zero_add]
      rw [sum_congr rfl fun w hw => Function.update_of_ne (ne_of_mem_erase hw) 0 t]
      ring
    omega
  have hGR' : GR s' t' := by
    intro X
    -- reduce to `v ∉ X`
    wlog hvX : v ∉ X generalizing X
    · have := this (X.erase v) (notMem_erase v X)
      rw [← add_sum_erase _ _ (not_not.1 hvX)] at *
      simp only [ht', Function.update_self, zero_add] at this ⊢
      refine this.trans (sum_le_sum fun a _ => ?_)
      exact min_le_min_left _ (card_erase_le)
    have hX : ∑ w ∈ X, t' w = ∑ w ∈ X, t w :=
      sum_congr rfl fun w hw => Function.update_of_ne (fun h => hvX (by rw [← h]; exact hw)) 0 t
    rw [hX]
    by_cases hj : ∃ a ∈ A, s a ≤ X.card
    · obtain ⟨a₁, ha₁, hsa₁⟩ := hj
      have hout : ∀ a, a ∉ A → s a ≤ X.card := fun a ha => (hmax a₁ ha₁ a ha).trans hsa₁
      have hGX := hGR (insert v X)
      rw [sum_insert hvX, card_insert_of_notMem hvX, ← hk] at hGX
      have hpt : ∀ a, min (s a) (X.card + 1) ≤ min (s' a) X.card + if a ∈ A then 1 else 0 := by
        intro a
        simp only [hs']
        split_ifs with h
        · have := hA1 a h; omega
        · have := hout a h; omega
      have : ∑ a, min (s a) (X.card + 1) ≤ ∑ a, min (s' a) X.card + k :=
        calc ∑ a, min (s a) (X.card + 1)
            ≤ ∑ a, (min (s' a) X.card + if a ∈ A then 1 else 0) := sum_le_sum fun a _ => hpt a
          _ = ∑ a, min (s' a) X.card + k := by rw [sum_add_distrib, hcard]
      omega
    · push Not at hj
      have : ∀ a, min (s' a) X.card = min (s a) X.card := by
        intro a
        simp only [hs']
        split_ifs with h
        · have := hj a h; omega
        · rfl
      rw [sum_congr rfl fun a _ => this a]
      exact hGR X
  obtain ⟨E', hE'l, hE'r⟩ := ih (m - k) (by omega) s' t' (by omega) hGR' hsum_t'
  have hdisj : ∀ a, (a, v) ∉ E' := by
    intro a ha
    have := hE'r v
    simp only [ht', Function.update_self, rdeg, card_eq_zero, filter_eq_empty_iff] at this
    exact this ha rfl
  refine ⟨E' ∪ A ×ˢ {v}, fun a => ?_, fun w => ?_⟩
  · rw [ldeg_union_prod E' A v hdisj, hE'l, hs'A a]
  · rw [rdeg_union_prod E' A v hdisj, hE'r, hA]
    simp only [ht']
    by_cases h : w = v
    · subst h; simp; omega
    · simp [h]

/-- Lemma 2.5 (bipartite analogue): if `1 ≤ δ ≤ s_a ≤ Δ`, `t_v ≤ Δ' ≤ ℓ` and `Δ Δ' ≤ ℓ δ`,
then a balanced `(s, t)` satisfies the Gale–Ryser condition. -/
theorem GR_of_near_regular (s : Fin ℓ → ℕ) (t : Fin n → ℕ) (hsum : ∑ a, s a = ∑ v, t v)
    {δ Δ Δ' : ℕ} (hδ : ∀ a, δ ≤ s a) (hΔ : ∀ a, s a ≤ Δ) (hΔ' : ∀ v, t v ≤ Δ') (hΔ'ℓ : Δ' ≤ ℓ)
    (hΔΔ : Δ * Δ' ≤ ℓ * δ) : GR s t := by
  intro X
  have hX : ∑ v ∈ X, t v ≤ X.card * Δ' := by
    calc ∑ v ∈ X, t v ≤ ∑ v ∈ X, Δ' := sum_le_sum fun v _ => hΔ' v
      _ = X.card * Δ' := by rw [sum_const, smul_eq_mul]
  rcases le_or_gt Δ X.card with h | h
  · calc ∑ v ∈ X, t v ≤ ∑ v, t v := sum_le_sum_of_subset (subset_univ X)
      _ = ∑ a, s a := hsum.symm
      _ = ∑ a, min (s a) X.card := sum_congr rfl fun a _ =>
          (min_eq_left ((hΔ a).trans h)).symm
  · rcases le_or_gt X.card δ with h' | h'
    · calc ∑ v ∈ X, t v ≤ X.card * Δ' := hX
        _ ≤ X.card * ℓ := Nat.mul_le_mul_left _ hΔ'ℓ
        _ = ∑ a : Fin ℓ, X.card := by simp [mul_comm]
        _ = ∑ a, min (s a) X.card := sum_congr rfl fun a _ =>
            (min_eq_right (h'.trans (hδ a))).symm
    · calc ∑ v ∈ X, t v ≤ X.card * Δ' := hX
        _ ≤ Δ * Δ' := Nat.mul_le_mul_right _ h.le
        _ ≤ ℓ * δ := hΔΔ
        _ = ∑ a : Fin ℓ, δ := by simp
        _ ≤ ∑ a, min (s a) X.card := sum_le_sum fun a _ => le_min (hδ a) h'.le

/-- Realizability of near-regular balanced sequences. -/
theorem N_pos_of_near_regular (d : BSeq ℓ n) (hbal : M1 d.1 = M1 d.2) {δ Δ Δ' : ℕ}
    (hδ : ∀ a, (δ : ℤ) ≤ d.1 a) (hΔ : ∀ a, d.1 a ≤ Δ) (ht0 : ∀ v, 0 ≤ d.2 v)
    (hΔ' : ∀ v, d.2 v ≤ Δ') (hΔ'ℓ : Δ' ≤ ℓ) (hΔΔ : Δ * Δ' ≤ ℓ * δ) : 0 < N d := by
  set s : Fin ℓ → ℕ := fun a => (d.1 a).toNat
  set t : Fin n → ℕ := fun v => (d.2 v).toNat
  have hs : ∀ a, (s a : ℤ) = d.1 a := fun a => Int.toNat_of_nonneg ((Int.natCast_nonneg δ).trans (hδ a))
  have ht : ∀ v, (t v : ℤ) = d.2 v := fun v => Int.toNat_of_nonneg (ht0 v)
  have hsum : ∑ a, s a = ∑ v, t v := by
    have : ((∑ a, s a : ℕ) : ℤ) = ((∑ v, t v : ℕ) : ℤ) := by
      push_cast; simp only [hs, ht]; exact hbal
    exact_mod_cast this
  obtain ⟨E, hEl, hEr⟩ := gale_ryser s t hsum (GR_of_near_regular s t hsum
    (fun a => by have := hδ a; rw [← hs] at this; exact_mod_cast this)
    (fun a => by have := hΔ a; rw [← hs] at this; exact_mod_cast this)
    (fun v => by have := hΔ' v; rw [← ht] at this; exact_mod_cast this) hΔ'ℓ hΔΔ)
  rw [N, card_pos]
  exact ⟨E, mem_graphs.2 ⟨fun a => by rw [hEl, hs], fun v => by rw [hEr, ht]⟩⟩

end LW.Bip
