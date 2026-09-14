import MajorityDynamics.Probability.NeighborhoodBulk.Relabel

/-! Exact transport of graph neighborhood counts and their actual fixed-degree law.
These identities also hold when the prescribed degree family is empty. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Relabeling carries the actual neighbor finset to its image. -/
theorem graph_neighborFinset_relabel (e : V ≃ W) (G : SimpleGraph V) (v : V) :
    (e.simpleGraph G).neighborFinset (e v) = (G.neighborFinset v).map e.toEmbedding := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  change G.Adj (e.symm (e v)) (e.symm w) ↔ _
  simp

/-- The actual number of neighbors in an image subset is unchanged. -/
theorem graph_neighborhood_card_relabel (e : V ≃ W) (G : SimpleGraph V)
    (v : V) (S : Finset V) :
    ((e.simpleGraph G).neighborFinset (e v) ∩ S.map e.toEmbedding).card =
      (G.neighborFinset v ∩ S).card := by
  rw [graph_neighborFinset_relabel, ← Finset.map_inter, Finset.card_map]

/-- Exact integer point-event transport for the actual uniform fixed-degree laws. -/
theorem graph_neighborhood_relabel (e : V ≃ W) (d : V → ℕ)
    (v : V) (S : Finset V) (t : ℤ) :
    (fixedDegreeLaw d).real {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} =
      (fixedDegreeLaw (fun w => d (e.symm w))).real
        {H | ((H.neighborFinset (e v) ∩ S.map e.toEmbedding).card : ℤ) = t} := by
  rw [← fixedDegreeLaw_relabel e d,
    map_measureReal_apply .of_discrete (Set.toFinite _).measurableSet]
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, graph_neighborhood_card_relabel]

end MajorityDynamics.Probability.NeighborhoodTail
