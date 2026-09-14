import MajorityDynamics.Literature.Graphicality.Basic
import MajorityDynamics.Literature.Graphicality.BipartiteRelation
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum

/-! A finite Hall reduction for the Gale–Ryser theorem. Row tokens request
occupied cells; column tokens request the complementary unoccupied cells.
This is a new Lean proof using Mathlib's proved finite Hall theorem. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma sum_le_sorted_prefix {l : ℕ} (a : Fin l → ℕ) (ha : Antitone a)
    (S : Finset (Fin l)) :
    ∑ i ∈ S, a i ≤ ∑ i ∈ prefixSet l S.card (by simpa using card_le_univ S), a i := by
  have hle : ∀ k (hk : k < S.card), k ≤ (S.orderEmbOfFin rfl ⟨k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      have hk' : k < S.card := by omega
      have hi := ih hk'
      have h := (S.orderEmbOfFin rfl).strictMono
        (show (⟨k,hk'⟩ : Fin S.card) < ⟨k+1,hk⟩ from Nat.lt_succ_self k)
      change (S.orderEmbOfFin rfl ⟨k,hk'⟩).val <
        (S.orderEmbOfFin rfl ⟨k+1,hk⟩).val at h
      omega
  calc
    _ = ∑ i : Fin S.card, a (S.orderEmbOfFin rfl i) := by
      conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl, sum_map]
      rfl
    _ ≤ ∑ i : Fin S.card, a (Fin.castLE (by simpa using card_le_univ S) i) := by
      exact sum_le_sum fun i _ => ha (hle i.val i.isLt)
    _ = _ := by simp [prefixSet]

abbrev GaleTokens {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ) :=
  (Σ i, Fin (a i)) ⊕ (Σ j, Fin (l - b j))

def galeNeighbors {l n : ℕ} {a : Fin l → ℕ} {b : Fin n → ℕ}
    (t : GaleTokens a b) : Finset (Fin l × Fin n) :=
  match t with
  | .inl x => {x.1} ×ˢ univ
  | .inr x => univ ×ˢ {x.1}

lemma gale_hall {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (hb : ∀ j, b j ≤ l)
    (hcap : ∀ A : Finset (Fin l), ∑ i ∈ A, a i ≤ ∑ j, min A.card (b j))
    (S : Finset (GaleTokens a b)) : S.card ≤ (S.biUnion galeNeighbors).card := by
  let A := S.toLeft.image Sigma.fst
  let B := S.toRight.image Sigma.fst
  have hleft : S.toLeft.card ≤ ∑ i ∈ A, a i := by
    calc
      _ ≤ (A.sigma fun i => (univ : Finset (Fin (a i)))).card := card_le_card (by
        intro x hx
        simp only [mem_sigma, mem_univ, and_true]
        exact mem_image_of_mem Sigma.fst hx)
      _ = _ := by simp
  have hright : S.toRight.card ≤ ∑ j ∈ B, (l - b j) := by
    calc
      _ ≤ (B.sigma fun j => (univ : Finset (Fin (l - b j)))).card := card_le_card (by
        intro x hx
        simp only [mem_sigma, mem_univ, and_true]
        exact mem_image_of_mem Sigma.fst hx)
      _ = _ := by simp
  have hN : S.biUnion galeNeighbors = (A ×ˢ Bᶜ) ∪ (univ ×ˢ B) := by
    ext ⟨i,j⟩
    simp only [mem_biUnion, mem_union, mem_product, mem_univ, true_and, mem_compl]
    constructor
    · rintro ⟨x,hx,hij⟩
      cases x with
      | inl x =>
        have hi : i = x.1 := by simpa [galeNeighbors, eq_comm] using hij
        have hiA : i ∈ A := hi ▸ mem_image_of_mem Sigma.fst (by simpa using hx)
        by_cases hj : j ∈ B
        · exact Or.inr hj
        · exact Or.inl ⟨hiA,hj⟩
      | inr x =>
        have hj : j = x.1 := by simpa [galeNeighbors, eq_comm] using hij
        exact Or.inr (hj ▸ mem_image_of_mem Sigma.fst (by simpa using hx))
    · rintro (⟨hi,_⟩ | hj)
      · obtain ⟨x,hx,hxi⟩ := mem_image.mp hi
        exact ⟨.inl x, by simpa using hx, by simp [galeNeighbors,hxi]⟩
      · obtain ⟨x,hx,hxj⟩ := mem_image.mp hj
        exact ⟨.inr x, by simpa using hx, by simp [galeNeighbors,hxj]⟩
  have hdis : Disjoint (A ×ˢ Bᶜ) (univ ×ˢ B) := by
    simp [disjoint_left]
  rw [hN, card_union_of_disjoint hdis, card_product, card_product, card_univ]
  have hsplit : (∑ j, min A.card (b j)) ≤
      (∑ j ∈ B, b j) + Bᶜ.card * A.card := by
    rw [← sum_add_sum_compl B]
    apply add_le_add
    · exact sum_le_sum fun j _ => min_le_right _ _
    · simpa using (sum_le_sum (s := Bᶜ) (fun j _ => min_le_left A.card (b j)))
  have hcancel : (∑ j ∈ B, b j) + (∑ j ∈ B, (l-b j)) = B.card * l := by
    rw [← sum_add_distrib]
    simp [Nat.add_sub_of_le (hb _)]
  have hc := hcap A
  have hs := S.card_toLeft_add_card_toRight
  simp only [Fintype.card_fin]
  nlinarith

lemma gale_matching {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (hb : ∀ j, b j ≤ l) (ht : (∑ i, a i) = ∑ j, b j)
    (hcap : ∀ A : Finset (Fin l), ∑ i ∈ A, a i ≤ ∑ j, min A.card (b j)) :
    ∃ e : GaleTokens a b ≃ (Fin l × Fin n), ∀ t, e t ∈ galeNeighbors t := by
  obtain ⟨f,hf,hn⟩ := (all_card_le_biUnion_card_iff_existsInjective' galeNeighbors).mp
    (gale_hall a b hb hcap)
  have hc : Fintype.card (GaleTokens a b) = Fintype.card (Fin l × Fin n) := by
    simp only [GaleTokens, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
      Fintype.card_prod]
    rw [ht, ← sum_add_distrib]
    simp [Nat.add_sub_of_le (hb _), Nat.mul_comm]
  have hsurj : Function.Surjective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩ |>.2
  exact ⟨Equiv.ofBijective f ⟨hf,hsurj⟩,hn⟩
lemma gale_matching_bigraphical {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (hb : ∀ j, b j ≤ l) (e : GaleTokens a b ≃ (Fin l × Fin n))
    (he : ∀ t, e t ∈ galeNeighbors t) : Bigraphical a b := by
  classical
  have hrow (i : Fin l) (k : Fin (a i)) : (e (.inl ⟨i,k⟩)).1 = i := by
    exact mem_singleton.mp (mem_product.mp (he (.inl ⟨i,k⟩))).1
  have hcol (j : Fin n) (k : Fin (l-b j)) : (e (.inr ⟨j,k⟩)).2 = j := by
    exact mem_singleton.mp (mem_product.mp (he (.inr ⟨j,k⟩))).2
  let R : Fin l → Fin n → Prop := fun i j => ∃ k : Fin (a i), e (.inl ⟨i,k⟩) = (i,j)
  have hr (i : Fin l) : (univ.filter (R i)).card = a i := by
    symm
    calc
      _ = (univ : Finset (Fin (a i))).card := by simp
      _ = _ := by
        apply card_bij (fun k _ => (e (.inl ⟨i,k⟩)).2)
        · intro k hk
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨k, Prod.ext (hrow i k) rfl⟩
        · intro k hk k' hk' hkk
          have hpair : e (.inl ⟨i,k⟩) = e (.inl ⟨i,k'⟩) :=
            Prod.ext ((hrow i k).trans (hrow i k').symm) hkk
          have hin := Sum.inl.inj (e.injective hpair)
          exact eq_of_heq (Sigma.mk.inj_iff.mp hin).2
        · intro j hj
          obtain ⟨k,hk⟩ := (mem_filter.mp hj).2
          exact ⟨k, mem_univ _, congrArg Prod.snd hk⟩
  have hnot (i : Fin l) (j : Fin n) : ¬ R i j ↔
      ∃ k : Fin (l-b j), e (.inr ⟨j,k⟩) = (i,j) := by
    constructor
    · intro hij
      obtain ⟨t,ht⟩ := e.surjective (i,j)
      cases t with
      | inl x =>
        obtain ⟨i',k⟩ := x
        have hi : i' = i := (hrow i' k).symm.trans (congrArg Prod.fst ht)
        subst i'
        exact False.elim (hij ⟨k,ht⟩)
      | inr x =>
        obtain ⟨j',k⟩ := x
        have hj : j' = j := (hcol j' k).symm.trans (congrArg Prod.snd ht)
        subst j'
        exact ⟨k,ht⟩
    · rintro ⟨k,hk⟩ ⟨q,hq⟩
      cases e.injective (hq.trans hk.symm)
  have hc (j : Fin n) : (univ.filter (fun i => ¬ R i j)).card = l-b j := by
    symm
    calc
      _ = (univ : Finset (Fin (l-b j))).card := by simp
      _ = _ := by
        apply card_bij (fun k _ => (e (.inr ⟨j,k⟩)).1)
        · intro k hk
          simp only [mem_filter, mem_univ, true_and]
          exact (hnot _ _).mpr ⟨k, Prod.ext rfl (hcol j k)⟩
        · intro k hk k' hk' hkk
          have hpair : e (.inr ⟨j,k⟩) = e (.inr ⟨j,k'⟩) :=
            Prod.ext hkk ((hcol j k).trans (hcol j k').symm)
          have hin := Sum.inr.inj (e.injective hpair)
          exact eq_of_heq (Sigma.mk.inj_iff.mp hin).2
        · intro i hi
          obtain ⟨k,hk⟩ := (hnot _ _).mp (mem_filter.mp hi).2
          exact ⟨k, mem_univ _, congrArg Prod.fst hk⟩
  apply bigraphical_of_relation R a b
  · intro i
    convert hr i using 1
    congr 1
    ext x
    simp only [mem_filter]
  · intro j
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin l)))
      (fun i => R i j)
    rw [hc, card_univ, Fintype.card_fin] at hsum
    have hj : (univ.filter (fun i => R i j)).card = b j := by
      have := hb j
      omega
    convert hj using 1
    congr 1
    ext x
    simp only [mem_filter]

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
