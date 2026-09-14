import MajorityDynamics.GraphProcess.BlockDecomposition.Fibers
import MajorityDynamics.Probability.FixedDegreeSampling.Conditioning
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.BlockDecomposition
open History
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder L]

/-- The unordered label cell of an edge. -/
def cell (π : V → L) : Sym2 V → Sym2 L := Sym2.map π

def cellEdges (π : V → L) (G : SimpleGraph V) (c : Sym2 L) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ cell π e = c}

omit [Fintype V] [Fintype L] [LinearOrder L] in
theorem cellEdges_disjoint (π : V → L) (G : SimpleGraph V) {c d : Sym2 L} (h : c ≠ d) :
    Disjoint (cellEdges π G c) (cellEdges π G d) := by
  rw [Set.disjoint_left]
  intro e hc hd
  exact h (hc.2.symm.trans hd.2)

omit [Fintype V] [Fintype L] [LinearOrder L] in
theorem cellEdges_cover (π : V → L) (G : SimpleGraph V) :
    (⋃ c, cellEdges π G c) = G.edgeSet := by
  ext e
  simp [cellEdges]

/-- Internal labels and increasing distinct pairs enumerate unordered cells once. -/
def cellLabel : L ⊕ Pair L → Sym2 L
  | .inl s => s(s, s)
  | .inr p => s(p.val.1, p.val.2)

omit [Fintype V] [Fintype L] in
theorem cellLabel_injective : Function.Injective (cellLabel (L := L)) := by
  intro a b h
  cases a with
  | inl s =>
    cases b with
    | inl t =>
      change s(s,s) = s(t,t) at h
      have hst := (Sym2.eq_iff.mp h).elim And.left And.left
      exact congrArg Sum.inl hst
    | inr p =>
      change s(s,s) = s(p.val.1,p.val.2) at h
      rcases Sym2.eq_iff.mp h with h | h
      · exact False.elim ((ne_of_lt p.property) (h.1.symm.trans h.2))
      · exact False.elim ((ne_of_lt p.property) (h.2.symm.trans h.1))
  | inr p =>
    cases b with
    | inl t =>
      change s(p.val.1,p.val.2) = s(t,t) at h
      rcases Sym2.eq_iff.mp h with h | h
      · exact False.elim ((ne_of_lt p.property) (h.1.trans h.2.symm))
      · exact False.elim ((ne_of_lt p.property) (h.1.trans h.2.symm))
    | inr q =>
      change s(p.val.1,p.val.2) = s(q.val.1,q.val.2) at h
      rcases Sym2.eq_iff.mp h with h | h
      · exact congrArg Sum.inr (Subtype.ext (Prod.ext h.1 h.2))
      · have hp := p.property
        rw [h.1, h.2] at hp
        exact False.elim (not_lt_of_gt q.property hp)

omit [Fintype V] [Fintype L] [LinearOrder L] in
@[simp] theorem cell_mk (π : V → L) (v w : V) : cell π s(v,w) = s(π v, π w) := rfl

omit [Fintype V] [Fintype L] in
theorem indexed_cellEdges_disjoint (π : V → L) (G : SimpleGraph V)
    {a b : L ⊕ Pair L} (h : a ≠ b) :
    Disjoint (cellEdges π G (cellLabel a)) (cellEdges π G (cellLabel b)) :=
  cellEdges_disjoint π G (fun he => h (cellLabel_injective he))

omit [Fintype L] [LinearOrder L] in
theorem cross_edgeTotals (π : V → L) (G : SimpleGraph V) (s t : L) :
    edgeTotals π (degreeArray π G) s t = ((cross π G s t).ncard : ℤ) := by
  rw [bipartite_edge_count, Nat.cast_sum]
  simp_rw [cross_leftDegree]
  exact Finset.sum_subtype (block π s) (fun v => mem_block π s v) (fun v => degreeArray π G v t)

omit [Fintype V] in
theorem sum_pairs (f : L → L → ℤ) :
    (∑ p : Pair L, f p.val.1 p.val.2) = ∑ s, ∑ t, if s < t then f s t else 0 := by
  have h := (Finset.sum_subtype (Finset.univ.filter (fun p : L × L => p.1 < p.2))
    (p := fun p : L × L => p.1 < p.2) (F := inferInstance) (by simp) (fun p : L × L => f p.1 p.2)).symm
  simpa only [Finset.sum_filter, Fintype.sum_prod_type] using h

omit [Fintype V] in
theorem sum_symmetric (f : L → L → ℤ) (hf : ∀ s t, f s t = f t s) :
    (∑ s, ∑ t, f s t) = (∑ s, f s s) + 2 * ∑ p : Pair L, f p.val.1 p.val.2 := by
  rw [sum_pairs]
  have h (s t : L) : f s t = (if s = t then f s s else 0) +
      (if s < t then f s t else 0) + (if t < s then f s t else 0) := by
    rcases lt_trichotomy s t with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · subst t; simp
    · simp [h, ne_of_gt h, not_lt_of_gt h]
  calc
    _ = ∑ s, ∑ t, ((if s = t then f s s else 0) +
        (if s < t then f s t else 0) + (if t < s then f s t else 0)) := by
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro t _; exact h s t
    _ = (∑ s, f s s) + (∑ s, ∑ t, if s < t then f s t else 0) +
        (∑ s, ∑ t, if t < s then f s t else 0) := by simp [Finset.sum_add_distrib]
    _ = _ := by
      have hh : (∑ s, ∑ t, if t < s then f s t else 0) =
          ∑ s, ∑ t, if s < t then f s t else 0 := by
        rw [Finset.sum_comm]
        congr 1; funext s
        congr 1; funext t
        rw [hf]
      rw [hh]
      ring

/-- Whole edges are the sum of internal edges and once-oriented cross edges. -/
theorem edge_count_decomposition (π : V → L) (G : SimpleGraph V) :
    (G.edgeFinset.card : ℤ) =
      (∑ s, ((internalGraph π G s).edgeFinset.card : ℤ)) +
      ∑ p : Pair L, ((cross π G p.val.1 p.val.2).ncard : ℤ) := by
  have htotal : (∑ s, ∑ t, edgeTotals π (degreeArray π G) s t) =
      2 * (G.edgeFinset.card : ℤ) := by
    unfold edgeTotals
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := block π _)]
    simp_rw [sum_degreeArray]
    rw [sum_block]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hsplit := sum_symmetric (edgeTotals π (degreeArray π G)) (edgeTotals_symm π G)
  rw [htotal] at hsplit
  simp_rw [edgeTotals_diagonal, cross_edgeTotals] at hsplit
  simp only [← Finset.mul_sum, internalEdgeCount] at hsplit
  omega

/-- The same edge-count formula directly on arbitrary sampled components. -/
theorem glue_edge_count (π : V → L) (C : Components π) :
    ((glue π C).edgeFinset.card : ℤ) =
      (∑ s, ((C.1 s).edgeFinset.card : ℤ)) + ∑ p : Pair L, ((C.2 p).ncard : ℤ) := by
  have h := edge_count_decomposition π (glue π C)
  have hi (s : L) : internalGraph π (glue π C) s = C.1 s :=
    congrFun (congrArg Prod.fst (restrict_glue π C)) s
  have hc (p : Pair L) : cross π (glue π C) p.val.1 p.val.2 = C.2 p :=
    congrFun (congrArg Prod.snd (restrict_glue π C)) p
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h ⊢
  simpa only [hi, hc] using h

end MajorityDynamics.GraphProcess.BlockDecomposition
