import MajorityDynamics.Literature.RandomGraph.EdgeCount

/-!
# Splitting ordered edge counts into genuine Bernoulli edge families

Ordering the vertex labels divides ordered adjacent pairs into two injective
families of unordered edges. This accounts for overlaps without asserting
independence of the two families (which need not be independent).
-/

noncomputable section
open Finset
open MajorityDynamics.Paper

namespace MajorityDynamics.Literature.RandomGraph

attribute [local instance] Classical.propDecidable

def lowerPairs {N : ℕ} (U W : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (U ×ˢ W).filter fun vw => vw.1 < vw.2

def lowerEdges {N : ℕ} (U W : Finset (Fin N)) : Finset (Sym2 (Fin N)) :=
  (lowerPairs U W).image fun vw => s(vw.1, vw.2)

lemma lowerPairs_inj {N : ℕ} (U W : Finset (Fin N)) :
    Set.InjOn (fun vw : Fin N × Fin N => s(vw.1, vw.2)) (lowerPairs U W) := by
  intro a ha b hb he
  have hla := (mem_filter.mp ha).2
  have hlb := (mem_filter.mp hb).2
  rcases Sym2.eq_iff.mp he with h | h
  · exact Prod.ext h.1 h.2
  · rw [h.1, h.2] at hla
    exact (lt_asymm hla hlb).elim

lemma card_lowerEdges {N : ℕ} (U W : Finset (Fin N)) :
    (lowerEdges U W).card = (lowerPairs U W).card := by
  classical
  exact card_image_of_injOn (lowerPairs_inj U W)

lemma lowerEdges_subset {N : ℕ} (U W : Finset (Fin N)) :
    (lowerEdges U W : Set (Sym2 (Fin N))) ⊆ Sym2.diagSetᶜ := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := mem_image.mp he
  simpa using ne_of_lt (mem_filter.mp ha).2

lemma edgeCount_lowerEdges {N : ℕ} (U W : Finset (Fin N)) (G : Graph N) :
    edgeCount (lowerEdges U W) G =
      ((lowerPairs U W).filter fun vw => G.Adj vw.1 vw.2).card := by
  classical
  have he : (lowerEdges U W : Set (Sym2 (Fin N))) ∩ G.edgeSet =
      ((((lowerPairs U W).filter fun vw => G.Adj vw.1 vw.2).image
        fun vw => s(vw.1, vw.2)) : Set (Sym2 (Fin N))) := by
    ext e
    simp only [mem_coe, Set.mem_inter_iff, lowerEdges, mem_image, mem_filter]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, he⟩
      exact ⟨a, ⟨ha, he⟩, rfl⟩
    · rintro ⟨a, ⟨ha, he⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, he⟩
  rw [edgeCount, he, Set.ncard_coe_finset]
  exact card_image_of_injOn ((lowerPairs_inj U W).mono (filter_subset _ _))

lemma card_lowerEdges_le {N : ℕ} (U W : Finset (Fin N)) :
    (lowerEdges U W).card ≤ U.card * W.card := by
  rw [card_lowerEdges, ← card_product]
  exact card_filter_le _ _

lemma orderedEdgeCount_split {N : ℕ} (U W : Finset (Fin N)) (G : Graph N) :
    orderedEdgeCount G U W =
      edgeCount (lowerEdges U W) G + edgeCount (lowerEdges W U) G := by
  classical
  rw [edgeCount_lowerEdges, edgeCount_lowerEdges]
  simp only [orderedEdgeCount, lowerPairs, card_eq_sum_ones, sum_filter, sum_product]
  rw [sum_comm (s := W) (t := U), ← sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro w hw
  by_cases ha : G.Adj u w
  · rcases lt_or_gt_of_ne ha.ne with h | h
    · simp [ha, h, not_lt.mpr h.le]
    · simp [ha, ha.symm, h, not_lt.mpr h.le]
  · have hwa : ¬ G.Adj w u := fun h => ha h.symm
    simp [ha, hwa]

lemma card_lowerEdges_add {N : ℕ} (U W : Finset (Fin N)) :
    (lowerEdges U W).card + (lowerEdges W U).card + (U ∩ W).card =
      U.card * W.card := by
  classical
  have heq : (U ∩ W).card = ∑ u ∈ U, ∑ w ∈ W, if u = w then 1 else 0 := by
    simp only [sum_ite_eq, sum_boole, filter_mem_eq_inter, Nat.cast_id]
  rw [card_lowerEdges, card_lowerEdges, heq, ← card_product]
  simp only [lowerPairs, card_eq_sum_ones, sum_filter, sum_product]
  rw [sum_comm (s := W) (t := U), ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro w hw
  rcases lt_trichotomy u w with h | h | h
  · simp [h, not_lt.mpr h.le, h.ne]
  · simp [h]
  · simp [h, not_lt.mpr h.le, h.ne']

end MajorityDynamics.Literature.RandomGraph
