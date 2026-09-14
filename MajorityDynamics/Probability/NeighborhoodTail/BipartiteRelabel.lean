import MajorityDynamics.Probability.NeighborhoodBulk.Relabel

/-! Exact transport of bipartite neighborhood events under arbitrary finite relabeling. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk
variable {L L' R R' : Type*}
  [Fintype L] [Fintype L'] [Fintype R] [Fintype R']
  [DecidableEq R] [DecidableEq R']

omit [Fintype L] [Fintype L'] in
/-- The actual neighborhood count is invariant under relabeling both sides. -/
theorem bipartite_neighborhood_card_relabel (e : L ≃ L') (f : R ≃ R')
    (E : CrossEdges L R) (v : L) (S : Finset R) :
    ((leftNeighbors (crossRelabel e f E) (e v) ∩ S.map f.toEmbedding).card : ℤ) =
      ((leftNeighbors E v ∩ S).card : ℤ) := by
  rw [crossRelabel_leftNeighbors]
  simp only [Equiv.symm_apply_apply, ← Finset.map_inter, Finset.card_map]

/-- Uniform fixed-degree sampling transports the literal neighborhood-count event. -/
theorem bipartite_neighborhood_relabel (e : L ≃ L') (f : R ≃ R')
    (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R) (t : ℤ) :
    (bipartiteFixedDegreeLaw a b).real
        {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} =
      (bipartiteFixedDegreeLaw (fun l => a (e.symm l)) (fun r => b (f.symm r))).real
        {E | ((leftNeighbors E (e v) ∩ S.map f.toEmbedding).card : ℤ) = t} := by
  rw [← bipartiteFixedDegreeLaw_relabel e f a b,
    map_measureReal_apply .of_discrete (Set.toFinite _).measurableSet]
  congr 1
  ext E
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, bipartite_neighborhood_card_relabel]

end MajorityDynamics.Probability.NeighborhoodTail
