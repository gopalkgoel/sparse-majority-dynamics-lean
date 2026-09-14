import MajorityDynamics.GraphProcess.GraphicalArray.Counts
import Mathlib.Data.Nat.Choose.Cast

noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.GraphicalArray
open History BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeSampling

/-- Select an arbitrary loopless edge subset of the complete graph. -/
theorem exists_graph_card (A : Type*) [Fintype A] (q : ℕ)
    (hq : q ≤ (Fintype.card A).choose 2) :
    ∃ G : SimpleGraph A, G.edgeFinset.card = q := by
  have hq' : q ≤ (⊤ : SimpleGraph A).edgeFinset.card := by
    simpa only [SimpleGraph.card_edgeFinset_top_eq_card_choose_two] using hq
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hq'
  let G := SimpleGraph.fromEdgeSet (s : Set (Sym2 A))
  have he : G.edgeSet = (s : Set (Sym2 A)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact And.left
    · intro he
      refine ⟨he, ?_⟩
      have hh : e ∈ (⊤ : SimpleGraph A).edgeSet :=
        SimpleGraph.mem_edgeFinset.mp (hs he)
      exact SimpleGraph.edgeSet_subset_compl_diagSet ⊤ hh
  refine ⟨G, ?_⟩
  have hfin : G.edgeFinset = s := by
    apply Finset.coe_injective
    simpa only [SimpleGraph.coe_edgeFinset] using he
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
    (congrArg Finset.card hfin).trans hcard

/-- Ordered internal counts are even and bounded by the loopless capacity. -/
theorem exists_internal_count (A : Type*) [Fintype A] (m : ℤ)
    (hm : 0 ≤ m) (he : Even m)
    (hu : m ≤ (Fintype.card A : ℤ) * ((Fintype.card A : ℤ) - 1)) :
    ∃ G : SimpleGraph A, 2 * (G.edgeFinset.card : ℤ) = m := by
  obtain ⟨z, hz⟩ := he
  have hz0 : 0 ≤ z := by omega
  have hc : 2 * ((Fintype.card A).choose 2 : ℤ) =
      (Fintype.card A : ℤ) * ((Fintype.card A : ℤ) - 1) := by
    have hh : (2 : ℚ) * ((Fintype.card A).choose 2 : ℚ) =
        (Fintype.card A : ℚ) * ((Fintype.card A : ℚ) - 1) := by
      rw [Nat.cast_choose_two]
      ring
    exact_mod_cast hh
  have hb : z.toNat ≤ (Fintype.card A).choose 2 := by
    have hcast := Int.toNat_of_nonneg hz0
    exact_mod_cast (show (z.toNat : ℤ) ≤ ((Fintype.card A).choose 2 : ℤ) by omega)
  obtain ⟨G, hG⟩ := exists_graph_card A z.toNat hb
  refine ⟨G, ?_⟩
  rw [hG, Int.toNat_of_nonneg hz0]
  omega

theorem exists_cross_count (A B : Type*) [Fintype A] [Fintype B] (m : ℤ)
    (hm : 0 ≤ m) (hu : m ≤ (Fintype.card A : ℤ) * (Fintype.card B : ℤ)) :
    ∃ E : CrossEdges A B, (E.ncard : ℤ) = m := by
  have hb : m.toNat ≤ (Finset.univ : Finset (A × B)).card := by
    simp only [Finset.card_univ, Fintype.card_prod]
    exact_mod_cast (show (m.toNat : ℤ) ≤ (Fintype.card A : ℤ) * (Fintype.card B : ℤ) by
      simpa only [Int.toNat_of_nonneg hm] using hu)
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hb
  exact ⟨(s : Set (A × B)), by simp [hs, Int.toNat_of_nonneg hm]⟩

variable {V : Type*} [Fintype V] {n : ℕ}

theorem block_card_eq_sizes (y : MajorityDynamics.Local.CoarseData V n)
    (s : MajorityDynamics.Universal.History (n+1)) :
    Fintype.card (Block y.part s) = MajorityDynamics.Local.partSizes y.part s := by
  rw [Fintype.card_subtype]
  rfl

theorem internalCount_nonempty (y : MajorityDynamics.Local.CoarseData V n)
    (s : MajorityDynamics.Universal.History (n+1)) :
    Nonempty (InternalCountFiber y.part y.edge s) := by
  obtain ⟨G, hG⟩ := exists_internal_count (Block y.part s) (y.edge s s)
    (y.edge_nonneg s s) (y.edge_even s) (by
      simpa only [block_card_eq_sizes, ite_true, ↓reduceIte] using y.edge_upper s s)
  refine ⟨⟨G, ?_⟩⟩
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hG

theorem crossCount_nonempty (y : MajorityDynamics.Local.CoarseData V n)
    (p : Pair (MajorityDynamics.Universal.History (n+1))) :
    Nonempty (CrossCountFiber y.part y.edge p) := by
  obtain ⟨E, hE⟩ := exists_cross_count (Block y.part p.val.1) (Block y.part p.val.2)
    (y.edge p.val.1 p.val.2) (y.edge_nonneg _ _) (by
      simpa only [block_card_eq_sizes, if_neg (ne_of_lt p.property), sub_zero]
        using y.edge_upper p.val.1 p.val.2)
  exact ⟨⟨E, hE⟩⟩

theorem countComponents_nonempty (y : MajorityDynamics.Local.CoarseData V n) :
    Nonempty (CountComponents y.part y.edge) :=
  ⟨⟨fun s => Classical.choice (internalCount_nonempty y s),
     fun p => Classical.choice (crossCount_nonempty y p)⟩⟩

/-- Broad coarse capacities alone imply an actual graph realization. -/
theorem coarse_fixedCount_nonempty (y : MajorityDynamics.Local.CoarseData V n) :
    (fixedCountFamily y.part y.edge).Nonempty := by
  let C := Classical.choice (countComponents_nonempty y)
  exact ⟨(countGlue y.part y.edge y.edge_symm C).val,
    (countGlue y.part y.edge y.edge_symm C).property⟩

end MajorityDynamics.GraphProcess.GraphicalArray
