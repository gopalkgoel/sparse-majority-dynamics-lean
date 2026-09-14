import MajorityDynamics.Probability.FixedDegreeSampling.BipartiteBasic
noncomputable section
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {L R : Type*} [Fintype L] [Fintype R]
omit [Fintype L] [Fintype R] in
theorem bipartiteGraph_adj_inl_inr (E : CrossEdges L R) (i : L) (j : R) :
    (bipartiteGraph E).Adj (Sum.inl i) (Sum.inr j) ↔ (i, j) ∈ E := by
  simp only [bipartiteGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Sym2.eq_iff,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false, or_false,
    ne_eq, not_false_eq_true, and_true]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl, rfl⟩
    exact hab
  · intro h
    exact ⟨(i, j), h, rfl, rfl⟩

omit [Fintype L] [Fintype R] in
theorem bipartiteGraph_not_adj_inl_inl (E : CrossEdges L R) (i i' : L) :
    ¬ (bipartiteGraph E).Adj (Sum.inl i) (Sum.inl i') := by
  simp [bipartiteGraph, SimpleGraph.fromEdgeSet_adj]

omit [Fintype L] [Fintype R] in
theorem bipartiteGraph_not_adj_inr_inr (E : CrossEdges L R) (j j' : R) :
    ¬ (bipartiteGraph E).Adj (Sum.inr j) (Sum.inr j') := by
  simp [bipartiteGraph, SimpleGraph.fromEdgeSet_adj]

omit [Fintype L] [Fintype R] in
/-- Every cross-edge set is determined by its graph. -/
theorem bipartiteGraph_injective : Function.Injective (bipartiteGraph (L := L) (R := R)) := by
  intro E E' h
  ext ⟨i, j⟩
  rw [← bipartiteGraph_adj_inl_inr, ← bipartiteGraph_adj_inl_inr, h]

theorem measurable_bipartiteGraph : Measurable (bipartiteGraph (L := L) (R := R)) :=
  measurable_of_countable _

open Classical in
/-- The degree of a left vertex in the bipartite graph is its left degree. -/
theorem degree_inl (E : CrossEdges L R) (i : L) :
    (bipartiteGraph E).degree (Sum.inl i) = leftDegree E i := by
  unfold leftDegree leftNeighbors
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (bipartiteGraph E).neighborFinset (Sum.inl i) =
      (Finset.univ.filter fun j : R ↦ (i, j) ∈ E).map Function.Embedding.inr := by
    ext y
    rcases y with i' | j
    · simp [bipartiteGraph_not_adj_inl_inl]
    · simp [bipartiteGraph_adj_inl_inr]
  rw [this, Finset.card_map]

open Classical in
/-- The degree of a right vertex in the bipartite graph is its right degree. -/
theorem degree_inr (E : CrossEdges L R) (j : R) :
    (bipartiteGraph E).degree (Sum.inr j) = rightDegree E j := by
  unfold rightDegree rightNeighbors
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (bipartiteGraph E).neighborFinset (Sum.inr j) =
      (Finset.univ.filter fun i : L ↦ (i, j) ∈ E).map Function.Embedding.inl := by
    ext y
    rcases y with i | j'
    · simp [(bipartiteGraph E).adj_comm, bipartiteGraph_adj_inl_inr]
    · simp [bipartiteGraph_not_adj_inr_inr]
  rw [this, Finset.card_map]


omit [Fintype L] [Fintype R] in
/-- Every labeled graph with no same-side edges has the cross-edge representation. -/
theorem bipartiteGraph_surjective (G : SimpleGraph (L ⊕ R))
    (hl : ∀ u v : L, ¬ G.Adj (.inl u) (.inl v))
    (hr : ∀ u v : R, ¬ G.Adj (.inr u) (.inr v)) :
    bipartiteGraph {x : L × R | G.Adj (.inl x.1) (.inr x.2)} = G := by
  ext x y
  cases x with
  | inl u =>
    cases y with
    | inl v => simp [bipartiteGraph_not_adj_inl_inl, hl]
    | inr w => simp [bipartiteGraph_adj_inl_inr]
  | inr w =>
    cases y with
    | inl u => simp [SimpleGraph.adj_comm, bipartiteGraph_adj_inl_inr]
    | inr z => simp [bipartiteGraph_not_adj_inr_inr, hr]

end MajorityDynamics.Probability.FixedDegreeSampling
