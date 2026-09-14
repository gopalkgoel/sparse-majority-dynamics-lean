import MajorityDynamics.Local.CoarseData
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Literal finite partition counts used by the state space in §2. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.History
variable {V L M : Type*} [Fintype V] [Fintype L] [Fintype M]

def block (π : V → L) (s : L) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => π v = s)

omit [Fintype L] in
@[simp] theorem mem_block (π : V → L) (s : L) (v : V) :
    v ∈ block π s ↔ π v = s := by
  classical
  simp [block]

omit [Fintype L] in
theorem block_cover (π : V → L) (v : V) : ∃ s, v ∈ block π s := ⟨π v, by simp⟩

omit [Fintype L] in
theorem block_disjoint (π : V → L) {s t : L} (h : s ≠ t) :
    Disjoint (block π s) (block π t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hs ht
  exact h ((mem_block π s v).mp hs |>.symm.trans ((mem_block π t v).mp ht))

theorem sum_block_card (π : V → L) : ∑ s, (block π s).card = Fintype.card V := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise (f := π)
    (s := Finset.univ) (t := Finset.univ) (by simp)).symm


theorem graph_degree_eq_sum (G : SimpleGraph V) (v : V) :
    (G.degree v : ℤ) = ∑ w : V, if G.Adj v w then 1 else 0 := by
  classical
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  rw [Finset.sum_boole, Set.toFinset_ofPred]

/-- The integer count of neighbors in a specified partition fiber. -/
def degreeArray (π : V → L) (G : SimpleGraph V) (v : V) (t : L) : ℤ := by
  classical
  exact ∑ w ∈ block π t, if G.Adj v w then 1 else 0

/-- Ordered totals; on the diagonal each undirected edge is counted twice. -/
def edgeTotals (π : V → L) (d : V → L → ℤ) (s t : L) : ℤ :=
  ∑ v ∈ block π s, d v t

omit [Fintype L] in
theorem degreeArray_eq_card (π : V → L) (G : SimpleGraph V) (v : V) (t : L) :
    degreeArray π G v t = ((block π t).filter (G.Adj v)).card := by
  classical
  simp [degreeArray, Finset.sum_boole]

omit [Fintype L] in
theorem degreeArray_nonneg (π : V → L) (G : SimpleGraph V) (v : V) (t : L) :
    0 ≤ degreeArray π G v t := by rw [degreeArray_eq_card]; positivity

omit [Fintype L] in
theorem degreeArray_upper (π : V → L) (G : SimpleGraph V) (v : V) (t : L) :
    degreeArray π G v t ≤ ((block π t).card : ℤ) - if π v = t then 1 else 0 := by
  classical
  rw [degreeArray_eq_card]
  by_cases h : π v = t
  · rw [if_pos h]
    have hs : (block π t).filter (G.Adj v) ⊆ (block π t).erase v := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_erase] at *
      exact ⟨fun he => G.irrefl (he ▸ hw.2), hw.1⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem (by simpa using h)] at hc
    have hp : 0 < (block π t).card := Finset.card_pos.mpr ⟨v, by simpa using h⟩
    omega
  · rw [if_neg h, sub_zero]
    exact_mod_cast Finset.card_filter_le (block π t) (G.Adj v)

theorem sum_block (π : V → L) {A : Type*} [AddCommMonoid A] (a : V → A) :
    ∑ t, ∑ v ∈ block π t, a v = ∑ v, a v := by
  classical
  simp only [block, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_degreeArray (π : V → L) (G : SimpleGraph V) (v : V) :
    ∑ t, degreeArray π G v t = (G.degree v : ℤ) := by
  classical
  simp only [degreeArray]
  rw [sum_block]
  exact (graph_degree_eq_sum G v).symm

omit [Fintype L] in
theorem edgeTotals_nonneg (π : V → L) (G : SimpleGraph V) (s t : L) :
    0 ≤ edgeTotals π (degreeArray π G) s t := by
  exact Finset.sum_nonneg fun _ _ => degreeArray_nonneg π G _ t

omit [Fintype L] in
theorem edgeTotals_symm (π : V → L) (G : SimpleGraph V) (s t : L) :
    edgeTotals π (degreeArray π G) s t = edgeTotals π (degreeArray π G) t s := by
  classical
  unfold edgeTotals degreeArray
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [G.adj_comm]

omit [Fintype L] in
theorem edgeTotals_upper (π : V → L) (G : SimpleGraph V) (s t : L) :
    edgeTotals π (degreeArray π G) s t ≤
      ((block π s).card : ℤ) * (((block π t).card : ℤ) - if s = t then 1 else 0) := by
  classical
  calc
    _ ≤ ∑ v ∈ block π s, (((block π t).card : ℤ) - if s = t then 1 else 0) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [(mem_block π s v).mp hv] using degreeArray_upper π G v t
    _ = _ := by simp [mul_sub, mul_ite]

/-- The actual induced graph on the specified block. -/
def internalGraph (π : V → L) (G : SimpleGraph V) (s : L) :
    SimpleGraph {v : V // π v = s} := G.induce {v | π v = s}

def internalEdgeCount (π : V → L) (G : SimpleGraph V) (s : L) : ℕ := by
  classical
  exact (internalGraph π G s).edgeFinset.card

omit [Fintype L] in
theorem internalGraph_degree (π : V → L) (G : SimpleGraph V) (s : L)
    (v : {v : V // π v = s}) :
    ((internalGraph π G s).degree v : ℤ) = degreeArray π G v s := by
  classical
  rw [graph_degree_eq_sum]
  simpa only [internalGraph, SimpleGraph.induce_adj, degreeArray, block, Finset.sum_filter]
    using (Finset.sum_subtype (block π s) (fun w => mem_block π s w)
      (fun w => if G.Adj (v : V) w then (1 : ℤ) else 0)).symm

omit [Fintype L] in
theorem edgeTotals_diagonal (π : V → L) (G : SimpleGraph V) (s : L) :
    edgeTotals π (degreeArray π G) s s = 2 * (internalEdgeCount π G s : ℤ) := by
  classical
  have h := congrArg (Nat.cast : ℕ → ℤ) (internalGraph π G s).sum_degrees_eq_twice_card_edges
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at h
  change _ = 2 * ((internalGraph π G s).edgeFinset.card : ℤ)
  rw [← h]
  simp_rw [internalGraph_degree]
  unfold edgeTotals block
  exact Finset.sum_subtype _ (by simp) _

omit [Fintype L] in
theorem edgeTotals_even (π : V → L) (G : SimpleGraph V) (s : L) :
    Even (edgeTotals π (degreeArray π G) s s) := by
  rw [edgeTotals_diagonal]
  exact even_two_mul _

@[simp] theorem block_card_partSizes {n : ℕ} (π : V → Universal.History (n + 1))
    (s : Universal.History (n + 1)) : (block π s).card = Local.partSizes π s := by
  unfold block Local.partSizes
  congr 1
  ext v
  simp


def toCoarseData {n : ℕ} (π : V → Universal.History (n + 1))
    (G : SimpleGraph V) (flag : Bool) : Local.CoarseData V n where
  part := π
  edge := edgeTotals π (degreeArray π G)
  edge_symm := edgeTotals_symm π G
  edge_even := edgeTotals_even π G
  edge_nonneg := edgeTotals_nonneg π G
  edge_upper := by
    intro s t
    have h := edgeTotals_upper π G s t
    rw [block_card_partSizes, block_card_partSizes] at h
    by_cases he : s = t <;> simpa only [he, if_true, if_false] using h
  reg := flag


end MajorityDynamics.GraphProcess.History
