import MajorityDynamics.Literature.LWAdapters.GraphLaws
import MajorityDynamics.Literature.LWAdapters.BipartiteLaws
import MajorityDynamics.Literature.LWFormal.Final16
import MajorityDynamics.Literature.LWFormal.Bip.Final15

noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Literature.LWAdapters
open MajorityDynamics.Probability.FixedDegreeSampling

theorem degree_asGraph {n : ℕ} {E : LW.Graph n} (hs : LW.IsSimple E) (v : Fin n) :
    (asGraph E).degree v = LW.deg E v := by
  have hh := degree_edgeFinset (asGraph E) v
  rw [fromEdgeSet_finset hs] at hh
  exact hh.symm

theorem asGraph_family {n : ℕ} {E : LW.Graph n} (hs : LW.IsSimple E) (d : Fin n → ℕ) :
    asGraph E ∈ graphFamily d ↔ ∀ v, LW.deg E v = d v := by
  simp only [graphFamily, Set.mem_ofPred_eq, degree_asGraph hs]

theorem adj_asGraph {n : ℕ} (E : LW.Graph n) (a b : Fin n) (hab : a ≠ b) :
    (asGraph E).Adj a b ↔ s(a,b) ∈ E := by
  simp [asGraph, hab]

theorem graphCount_eq {n : ℕ} (d : Fin n → ℕ) : graphCount d = LW.N (LW.toZ d) := by
  unfold graphCount
  rw [graph_card_transport]
  unfold LW.N LW.graphs
  apply congrArg Finset.card
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hs : LW.IsSimple E
  · simp [hs, asGraph_family hs, LW.HasDegSeq, LW.toZ]
  · simp [hs, LW.HasDegSeq]

theorem graph_edge_law {n m : ℕ} (d : Fin n → ℕ) (hs : ∑ i, d i = 2*m)
    (hr : (graphFamily d).Nonempty) (a b : Fin n) (hab : a ≠ b) :
    (fixedDegreeLaw d).real {G | G.Adj a b} = LW.probEdge n m d a b := by
  have hN : 0 < LW.N (LW.toZ d) := by
    rw [← graphCount_eq]
    exact (Set.ncard_pos (Set.toFinite _)).mpr hr
  rw [LW.probEdge_eq_P hs hN, measureReal_def, fixedDegreeLaw, uniform_apply,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  change _ / (graphCount d : ℝ) = _
  rw [graphCount_eq]
  unfold LW.P
  congr 1
  rw [graph_card_transport]
  unfold LW.Nav LW.NE
  apply congrArg (fun s : Finset (LW.Graph n) => (s.card : ℝ))
  ext E
  simp only [LW.graphsWith, LW.graphs, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.singleton_subset_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  by_cases hE : LW.IsSimple E
  · simp [LW.HasDegSeq, LW.toZ, hE, asGraph_family hE, adj_asGraph E a b hab]
  · simp [LW.HasDegSeq, hE]

theorem bipartiteCount_eq {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ) :
    bipartiteCount a b = LW.Bip.N (LW.Bip.toSeq a b) := by
  unfold bipartiteCount
  rw [bip_card_transport]
  unfold LW.Bip.N LW.Bip.graphs
  apply congrArg Finset.card
  ext E
  simp [bipartiteFamily, LW.Bip.HasDeg, LW.Bip.toSeq, leftDegree_finset, rightDegree_finset]

theorem bipartite_edge_law {l n m : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (hs : ∑ i, a i = m) (hr : (bipartiteFamily a b).Nonempty) (i : Fin l) (j : Fin n) :
    (bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} = LW.Bip.probEdge l n m a b i j := by
  have hN : 0 < LW.Bip.N (LW.Bip.toSeq a b) := by
    rw [← bipartiteCount_eq]
    exact (Set.ncard_pos (Set.toFinite _)).mpr hr
  rw [LW.Bip.probEdge_eq_P hs hN, measureReal_def, bipartiteFixedDegreeLaw, uniform_apply,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  change _ / (bipartiteCount a b : ℝ) = _
  rw [bipartiteCount_eq]
  unfold LW.Bip.P
  congr 1
  rw [bip_card_transport]
  apply congrArg (fun s : Finset (LW.Bip.BGraph l n) => (s.card : ℝ))
  ext E
  simp [LW.Bip.graphsWith, LW.Bip.graphs, LW.Bip.HasDeg,
    LW.Bip.toSeq, bipartiteFamily, leftDegree_finset, rightDegree_finset, and_assoc]

end MajorityDynamics.Literature.LWAdapters
