import MajorityDynamics.Literature.Graphicality.Basic

/-!
# Finite simple-graph edits

Elementary edge edits used in the exchange proof of Erdős–Gallai by
A. Tripathi, S. Venugopalan and D. B. West, “A short constructive proof of the
Erdős–Gallai characterization of graphic lists” (preprint September 6, 2009),
<https://dwest.web.illinois.edu/pubs/tripathi.pdf>.
The implementation and degree bookkeeping below are original Lean proofs.
-/

namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*}

/-- Add the undirected edge with distinct endpoints `x`, `y`. -/
def addEdge (G : SimpleGraph V) (x y : V) (hxy : x ≠ y) : SimpleGraph V where
  Adj v w := G.Adj v w ∨ (v = x ∧ w = y) ∨ (v = y ∧ w = x)
  symm := ⟨by
    intro v w h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨by
    intro v h
    rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact G.irrefl h
    · exact hxy h
    · exact hxy h.symm⟩

@[simp] theorem addEdge_adj (G : SimpleGraph V) (x y : V) (hxy : x ≠ y) (v w : V) :
    (addEdge G x y hxy).Adj v w ↔
      G.Adj v w ∨ (v = x ∧ w = y) ∨ (v = y ∧ w = x) := Iff.rfl

/-- Delete the undirected edge with endpoints `x`, `y`. -/
def removeEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ ¬ (v = x ∧ w = y) ∧ ¬ (v = y ∧ w = x)
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, fun h' => h.2.2 ⟨h'.2, h'.1⟩,
      fun h' => h.2.1 ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨by intro v h; exact G.irrefl h.1⟩

@[simp] theorem removeEdge_adj (G : SimpleGraph V) (x y v w : V) :
    (removeEdge G x y).Adj v w ↔
      G.Adj v w ∧ ¬ (v = x ∧ w = y) ∧ ¬ (v = y ∧ w = x) := Iff.rfl

variable [Fintype V] [DecidableEq V]

/-- Adding a missing edge increases precisely the two endpoint degrees. -/
theorem degree_addEdge (G : SimpleGraph V) (x y : V) (hxy : x ≠ y)
    (h : ¬ G.Adj x y) (v : V) :
    (addEdge G x y hxy).degree v = G.degree v +
      (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
  by_cases hvx : v = x
  · subst v
    have hn : (addEdge G x y hxy).neighborFinset x = insert y (G.neighborFinset x) := by
      ext w
      simp [hxy, eq_comm, or_comm]
    simp [-SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree, hn, h, hxy]
  · by_cases hvy : v = y
    · subst v
      have hn : (addEdge G x y hxy).neighborFinset y = insert x (G.neighborFinset y) := by
        ext w
        simp [hxy.symm, eq_comm, or_comm]
      have hyx : ¬ G.Adj y x := fun ha => h ha.symm
      simp [-SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree, hn, hyx, hxy.symm]
    · have hn : (addEdge G x y hxy).neighborFinset v = G.neighborFinset v := by
        ext w
        simp [hvx, hvy]
      simp [-SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree, hn, hvx, hvy]

/-- An additive degree identity for deleting an existing edge. -/
theorem degree_removeEdge (G : SimpleGraph V) (x y : V) (h : G.Adj x y) (v : V) :
    (removeEdge G x y).degree v + (if v = x then 1 else 0) +
      (if v = y then 1 else 0) = G.degree v := by
  have hxy : x ≠ y := h.ne
  by_cases hvx : v = x
  · subst v
    have hn : (removeEdge G x y).neighborFinset x = (G.neighborFinset x).erase y := by
      ext w
      simp [hxy, and_comm, ne_comm]
    simpa [-SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree, hn, hxy] using
      (Finset.card_erase_add_one (s := G.neighborFinset x) (a := y) (by simpa using h))
  · by_cases hvy : v = y
    · subst v
      have hn : (removeEdge G x y).neighborFinset y = (G.neighborFinset y).erase x := by
        ext w
        simp [hxy.symm, and_comm, ne_comm]
      simpa [-SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree, hn, hxy, hxy.symm] using
        (Finset.card_erase_add_one (s := G.neighborFinset y) (a := x) (by simpa using h.symm))
    · have hn : (removeEdge G x y).neighborFinset v = G.neighborFinset v := by
        ext w
        simp [hvx, hvy]
      simp [-SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree, hn, hvx, hvy]

/-- A larger-degree vertex has a neighbor that can be shifted to the smaller-degree
vertex without creating either a loop or a duplicate edge. -/
theorem exists_neighbor_of_degree_lt (G : SimpleGraph V) {r i : V}
    (hdeg : G.degree r < G.degree i) :
    ∃ u, u ≠ r ∧ G.Adj i u ∧ ¬ G.Adj r u := by
  by_contra! hn
  have hs : (G.neighborFinset i).erase r ⊆ (G.neighborFinset r).erase i := by
    intro u hu
    obtain ⟨hur, hiu⟩ := Finset.mem_erase.mp hu
    have hiu' : G.Adj i u := by simpa using hiu
    exact Finset.mem_erase.mpr ⟨fun hui => by subst u; exact G.irrefl hiu',
      by simpa using hn u hur hiu'⟩
  have hc := Finset.card_le_card hs
  by_cases hri : G.Adj r i
  · have h1 := Finset.card_erase_add_one (s := G.neighborFinset i) (a := r)
      (by simpa using hri.symm)
    have h2 := Finset.card_erase_add_one (s := G.neighborFinset r) (a := i)
      (by simpa using hri)
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at h1 h2
    omega
  · have hir : ¬ G.Adj i r := fun h => hri h.symm
    apply not_le_of_gt hdeg
    simpa [Finset.erase_eq_of_notMem (by simpa using hir : r ∉ G.neighborFinset i),
      Finset.erase_eq_of_notMem (by simpa using hri : i ∉ G.neighborFinset r)] using
      hc

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
