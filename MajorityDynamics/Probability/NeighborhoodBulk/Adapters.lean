import MajorityDynamics.Probability.NeighborhoodBulk.ZeroCases
import MajorityDynamics.Probability.FixedDegreeSampling.BipartiteGraph
import MajorityDynamics.Literature.DegreeEnumeration.FixedEdges

/-! Literal graph events and real-valued removal identities. -/
noncomputable section
open MeasureTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

theorem graph_removal_real (d : V → ℕ) (v : V) (S : Finset V)
    (h : graphAdmissible d v S) :
    (fixedDegreeLaw d).real {G | G.neighborFinset v = S} =
      (graphCount (residualDegree d v S) : ℝ) / graphCount d := by
  rw [measureReal_def, graph_neighborhood_probability d v S h]
  simp

theorem bipartite_removal_real (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R)
    (h : bipartiteAdmissible a b v S) :
    (bipartiteFixedDegreeLaw a b).real {E | leftNeighbors E v = S} =
      (bipartiteCount (fun u : Remaining v => a u) (residualRightDegree b S) : ℝ) /
        bipartiteCount a b := by
  rw [measureReal_def, bipartite_neighborhood_probability a b v S h]
  simp

theorem bipartite_neighbor_inter (E : CrossEdges L R) (v : L) (S : Finset R) :
    (bipartiteGraph E).neighborFinset (Sum.inl v) ∩ S.map Function.Embedding.inr =
      (leftNeighbors E v ∩ S).map Function.Embedding.inr := by
  ext y
  cases y with
  | inl i => simp
  | inr j => simp [leftNeighbors, bipartiteGraph_adj_inl_inr]

theorem bipartite_event_adapter (a : L → ℕ) (b : R → ℕ) (v : L)
    (S : Finset R) (t : ℤ) :
    ((bipartiteFixedDegreeLaw a b).map bipartiteGraph).real
      {G | ((G.neighborFinset (Sum.inl v) ∩ S.map Function.Embedding.inr).card : ℤ) = t} =
    (bipartiteFixedDegreeLaw a b).real {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} := by
  rw [measureReal_def, Measure.map_apply measurable_bipartiteGraph
    (Set.toFinite _).measurableSet]
  congr 2
  ext E
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, bipartite_neighbor_inter, Finset.card_map]

omit [Fintype V] [Fintype L] [Fintype R] in
theorem standardizedDegree_reconstruct (p size : ℝ) (d : ℤ)
    (h : 0 < p * size) :
    (d : ℝ) = p * size + standardizedDegree p size d * Real.sqrt (p * size) := by
  have hs := (Real.sqrt_pos.mpr h).ne'
  unfold standardizedDegree
  field_simp
  ring

omit [Fintype V] [Fintype L] [Fintype R] in
theorem degree_sub_toNat (d t : ℤ) (ht : 0 ≤ t) (htd : t ≤ d) :
    ((d - t).toNat : ℤ) = d - t ∧ (d - t).toNat = d.toNat - t.toNat := by
  omega

end MajorityDynamics.Probability.NeighborhoodBulk
