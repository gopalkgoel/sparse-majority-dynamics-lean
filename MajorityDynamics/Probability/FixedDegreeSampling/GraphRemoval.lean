import MajorityDynamics.Probability.FixedDegreeSampling.Basic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V]

/-- Delete the selected vertex by taking the induced graph. -/
def deleteVertex (v : V) (G : SimpleGraph V) : SimpleGraph (Remaining v) :=
  G.induce {u | u ≠ v}

/-- Insert a vertex with exactly the supplied neighborhood. -/
def insertVertex (v : V) (R : Finset V) (H : SimpleGraph (Remaining v)) : SimpleGraph V where
  Adj x y := if hx : x = v then y ≠ v ∧ y ∈ R
    else if hy : y = v then x ∈ R else H.Adj ⟨x, hx⟩ ⟨y, hy⟩
  symm := ⟨by
    intro x y h
    by_cases hx : x = v <;> by_cases hy : y = v <;>
      simp_all [H.adj_comm]⟩
  loopless := ⟨by
    intro x
    by_cases hx : x = v <;> simp [hx]⟩

omit [Fintype V] in
@[simp] theorem delete_insert (v : V) (R : Finset V)
    (H : SimpleGraph (Remaining v)) : deleteVertex v (insertVertex v R H) = H := by
  ext x y
  simp [deleteVertex, insertVertex, x.property, y.property]

theorem insert_delete (v : V) (R : Finset V) (G : SimpleGraph V)
    (h : G.neighborFinset v = R) : insertVertex v R (deleteVertex v G) = G := by
  ext x y
  by_cases hx : x = v <;> by_cases hy : y = v <;>
    simp_all [SimpleGraph.mem_neighborFinset, insertVertex, deleteVertex, ← h, G.adj_comm]

theorem insert_neighborhood (v : V) (R : Finset V) (hv : v ∉ R)
    (H : SimpleGraph (Remaining v)) : (insertVertex v R H).neighborFinset v = R := by
  ext u
  rw [SimpleGraph.mem_neighborFinset]
  by_cases hu : u = v <;> simp_all [insertVertex]

theorem delete_degree (v : V) (G : SimpleGraph V) (u : Remaining v) :
    (deleteVertex v G).degree u = G.degree u - if G.Adj u v then 1 else 0 := by
  have hmap : ((deleteVertex v G).neighborFinset u).map (Function.Embedding.subtype _) =
      (G.neighborFinset u).erase v := by
    ext w
    simp only [Finset.mem_map, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    change (∃ a : Remaining v, G.Adj u a ∧ a.val = w) ↔ w ≠ v ∧ G.Adj u w
    aesop
  have hc := congrArg Finset.card hmap
  simp only [Finset.card_map] at hc
  rw [SimpleGraph.degree, hc]
  by_cases h : G.Adj u v
  · rw [if_pos h, Finset.card_erase_of_mem (by simpa using h)]
    rfl
  · rw [if_neg h, Finset.erase_eq_of_notMem (by simpa using h), Nat.sub_zero]
    rfl

theorem insert_degree (v : V) (R : Finset V) (H : SimpleGraph (Remaining v))
    (u : Remaining v) :
    (insertVertex v R H).degree u = H.degree u + if u.val ∈ R then 1 else 0 := by
  have hd := delete_degree v (insertVertex v R H) u
  rw [delete_insert] at hd
  by_cases hu : u.val ∈ R
  · have ha : (insertVertex v R H).Adj u v := by simp [insertVertex, u.property, hu]
    have hp := ha.degree_pos_left
    simp only [ha, ite_true] at hd
    simp only [hu, ite_true]
    omega
  · simpa [insertVertex, u.property, hu] using hd.symm

theorem neighborhood_admissible (d : V → ℕ) (v : V) (R : Finset V)
    (G : graphNeighborhoodFiber d v R) : graphAdmissible d v R := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← G.property.2]; exact G.val.notMem_neighborFinset_self v
  · rw [← G.property.2]; exact G.property.1 v
  · intro u hu
    have ha : G.val.Adj v u := by simpa [← G.property.2] using hu
    have hp := ha.degree_pos_right
    rw [G.property.1 u] at hp
    exact hp

omit [Fintype V] in
theorem residualDegree_add (d : V → ℕ) (v : V) (R : Finset V)
    (h : graphAdmissible d v R) (u : Remaining v) :
    residualDegree d v R u + (if u.val ∈ R then 1 else 0) = d u := by
  unfold residualDegree
  apply Nat.sub_add_cancel
  split_ifs with hu
  · exact h.2.2 u hu
  · exact Nat.zero_le _

/-- Explicit induced-deletion / insertion equivalence, including empty residual fibers. -/
def graph_neighborhood_removal_equiv (d : V → ℕ) (v : V) (R : Finset V)
    (h : graphAdmissible d v R) :
    graphNeighborhoodFiber d v R ≃ graphFamily (residualDegree d v R) where
  toFun G := ⟨deleteVertex v G.val, by
    intro u
    rw [delete_degree, G.property.1]
    simp [residualDegree, ← G.property.2, G.val.adj_comm]⟩
  invFun H := ⟨insertVertex v R H.val, by
    constructor
    · intro u
      by_cases hu : u = v
      · subst u
        rw [← SimpleGraph.card_neighborFinset_eq_degree, insert_neighborhood v R h.1]
        exact h.2.1
      · rw [show (insertVertex v R H.val).degree u =
          H.val.degree ⟨u, hu⟩ + (if u ∈ R then 1 else 0) from insert_degree v R H.val ⟨u, hu⟩]
        rw [H.property ⟨u, hu⟩]
        exact residualDegree_add d v R h ⟨u, hu⟩
    · exact insert_neighborhood v R h.1 H.val⟩
  left_inv G := Subtype.ext (insert_delete v R G.val G.property.2)
  right_inv H := Subtype.ext (delete_insert v R H.val)

end MajorityDynamics.Probability.FixedDegreeSampling
