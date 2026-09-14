import MajorityDynamics.Literature.Graphicality.Basic

/-! A finite zero-one relation gives a labeled bipartite simple graph with its
row and column cardinalities as degrees. This adapter has no graphicality
criterion as an input. -/

namespace MajorityDynamics.Combinatorics.SufficientGraphicality

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The simple bipartite graph associated to a relation between its two sides. -/
def relationGraph {l n : ℕ} (R : Fin l → Fin n → Prop) :
    SimpleGraph (Fin l ⊕ Fin n) where
  Adj
    | .inl i, .inr j => R i j
    | .inr j, .inl i => R i j
    | _, _ => False
  symm := ⟨by rintro (i | j) (i' | j') <;> simp_all⟩
  loopless := ⟨by rintro (i | j) <;> simp⟩

/-- Row and column cardinalities of a finite relation are realized by an actual
simple graph on the disjoint union of the original labeled vertex sets. -/
theorem bigraphical_of_relation {l n : ℕ} (R : Fin l → Fin n → Prop)
    (a : Fin l → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, (univ.filter (R i)).card = a i)
    (hb : ∀ j, (univ.filter (fun i => R i j)).card = b j) : Bigraphical a b := by
  refine ⟨relationGraph R, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp [relationGraph]
  · intro i j
    simp [relationGraph]
  · intro i
    have hneighbors : (relationGraph R).neighborFinset (.inl i) =
        (univ.filter (R i)).image Sum.inr := by
      ext x
      rw [SimpleGraph.mem_neighborFinset]
      cases x <;> simp [relationGraph]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors,
      card_image_of_injective _ Sum.inr_injective]
    exact ha i
  · intro j
    have hneighbors : (relationGraph R).neighborFinset (.inr j) =
        (univ.filter (fun i => R i j)).image Sum.inl := by
      ext x
      rw [SimpleGraph.mem_neighborFinset]
      cases x <;> simp [relationGraph]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors,
      card_image_of_injective _ Sum.inl_injective]
    exact hb j

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
