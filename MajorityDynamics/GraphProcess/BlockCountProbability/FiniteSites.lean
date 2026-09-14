import MajorityDynamics.GraphProcess.GraphicalArray.Components
import MajorityDynamics.Probability.DegreeConcentration.Sites

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockCountProbability
open History BlockDecomposition GraphicalArray
open MajorityDynamics.Probability.DegreeConcentration
variable {V L : Type*} [Fintype V] [LinearOrder L]

def internalEmbedding (π : V → L) (s : L) : Sym2 (Block π s) ↪ Sym2 V :=
  (⟨Subtype.val, Subtype.val_injective⟩ : Block π s ↪ V).sym2Map

def crossEmbedding (π : V → L) (z : Pair L) :
    (Block π z.val.1 × Block π z.val.2) ↪ Sym2 V where
  toFun e := s(e.1.val, e.2.val)
  inj' := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · have hh := congrArg π h.1
      rw [a.1.property, b.2.property] at hh
      exact False.elim (ne_of_lt z.property hh)

def internalSites (π : V → L) (s : L) : Finset (Sym2 V) :=
  (⊤ : SimpleGraph (Block π s)).edgeFinset.map (internalEmbedding π s)

def crossSites (π : V → L) (z : Pair L) : Finset (Sym2 V) :=
  Finset.univ.map (crossEmbedding π z)

omit [LinearOrder L] in
theorem internalSites_card (π : V → L) (s : L) :
    (internalSites π s).card = (Fintype.card (Block π s)).choose 2 := by
  rw [internalSites, Finset.card_map, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

theorem crossSites_card (π : V → L) (z : Pair L) :
    (crossSites π z).card = Fintype.card (Block π z.val.1) *
      Fintype.card (Block π z.val.2) := by
  simp [crossSites]

def sites (π : V → L) : L ⊕ Pair L → Finset (Sym2 V) :=
  Sum.elim (internalSites π) (crossSites π)

def signature : L ⊕ Pair L → Sym2 L :=
  Sum.elim (fun s => s(s,s)) (fun z => s(z.val.1,z.val.2))

theorem signature_injective : Function.Injective (@signature L _) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => simpa [signature, Sym2.eq_iff] using h
    | inr b =>
      change s(a,a) = s(b.val.1,b.val.2) at h
      rcases Sym2.eq_iff.mp h with h | h
      · exact False.elim (ne_of_lt b.property (h.1.symm.trans h.2))
      · exact False.elim (ne_of_lt b.property (h.2.symm.trans h.1))
  | inr a =>
    cases b with
    | inl b =>
      change s(a.val.1,a.val.2) = s(b,b) at h
      rcases Sym2.eq_iff.mp h with h | h <;>
        exact False.elim (ne_of_lt a.property (h.1.trans h.2.symm))
    | inr b =>
      change s(a.val.1,a.val.2) = s(b.val.1,b.val.2) at h
      rcases Sym2.eq_iff.mp h with h | h
      · exact congrArg Sum.inr (Subtype.ext (Prod.ext h.1 h.2))
      · have ha := a.property
        rw [h.1, h.2] at ha
        exact False.elim (not_lt_of_gt b.property ha)

theorem sites_signature (π : V → L) (j : L ⊕ Pair L) (e : Sym2 V)
    (he : e ∈ sites π j) : Sym2.map π e = signature j := by
  cases j with
  | inl s =>
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp he
    induction a using Sym2.ind with
    | _ v w => simp [internalEmbedding, signature, v.property, w.property]
  | inr z =>
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp he
    change s(π a.1.val, π a.2.val) = s(z.val.1,z.val.2)
    rw [a.1.property, a.2.property]

theorem sites_disjoint (π : V → L) : Pairwise fun i j => Disjoint (sites π i) (sites π j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hi hj
  exact hij (signature_injective ((sites_signature π i e hi).symm.trans
    (sites_signature π j e hj)))

theorem sites_nondiag (π : V → L) (j : L ⊕ Pair L) :
    (sites π j : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by
  intro e he
  cases j with
  | inl s =>
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    have ha' := SimpleGraph.edgeSet_subset_compl_diagSet ⊤
      (SimpleGraph.mem_edgeFinset.mp ha)
    change ¬ (Sym2.map (Subtype.val : Block π s → V) a).IsDiag
    rw [Sym2.isDiag_map Subtype.val_injective]
    exact ha'
  | inr z =>
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp he
    change ¬ (s(a.1.val, a.2.val)).IsDiag
    rw [Sym2.mk_isDiag_iff]
    intro h
    exact ne_of_lt z.property (a.1.property.symm.trans ((congrArg π h).trans a.2.property))

def graphOf (ω : Sym2 V → Prop) : SimpleGraph V := SimpleGraph.fromEdgeSet {e | ω e}

omit [LinearOrder L] in
theorem internalSites_count (π : V → L) (s : L) (ω : Sym2 V → Prop) :
    blockCount (internalSites π s) ω =
      (internalGraph π (graphOf ω) s).edgeFinset.card := by
  rw [blockCount_eq_card, internalSites, Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.ext
  intro e
  induction e using Sym2.ind with
  | _ v w =>
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
    change (v ≠ w ∧ ω s(v.val,w.val)) ↔
      (graphOf ω).Adj v.val w.val
    rw [graphOf, SimpleGraph.fromEdgeSet_adj]
    change (v ≠ w ∧ ω s(v.val,w.val)) ↔ (ω s(v.val,w.val) ∧ v.val ≠ w.val)
    constructor
    · rintro ⟨hne, hw⟩
      exact ⟨hw, fun h => hne (Subtype.ext h)⟩
    · rintro ⟨hw, hne⟩
      exact ⟨fun h => hne (congrArg Subtype.val h), hw⟩

theorem crossSites_count (π : V → L) (z : Pair L) (ω : Sym2 V → Prop) :
    blockCount (crossSites π z) ω =
      (cross π (graphOf ω) z.val.1 z.val.2).ncard := by
  rw [blockCount_eq_card, crossSites, Finset.filter_map, Finset.card_map]
  rw [← Set.ncard_coe_finset]
  apply congrArg Set.ncard
  ext e
  have hne : e.1.val ≠ e.2.val := by
    intro h
    exact ne_of_lt z.property (e.1.property.symm.trans ((congrArg π h).trans e.2.property))
  change e ∈ Finset.univ.filter (fun a => ω s(a.1.val,a.2.val)) ↔
    (graphOf ω).Adj e.1.val e.2.val
  simp [graphOf, SimpleGraph.fromEdgeSet_adj, hne]

end MajorityDynamics.GraphProcess.BlockCountProbability
