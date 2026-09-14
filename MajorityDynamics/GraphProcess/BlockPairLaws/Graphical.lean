import MajorityDynamics.GraphProcess.GraphicalArray.Components

set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open History BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Restriction to the actual vertices of an internal block. -/
def internalVector (π : V → Universal.History (n+1)) (d : RowArray.Ambient π)
    (s : Universal.History (n+1)) : Block π s → ℕ :=
  fun v => RowArray.naturalRows d v.val s

/-- The two actual degree vectors for one orientation of a distinct block pair. -/
def crossVector (π : V → Universal.History (n+1)) (d : RowArray.Ambient π)
    (p : Pair (Universal.History (n+1))) :
    (Block π p.val.1 → ℕ) × (Block π p.val.2 → ℕ) :=
  (fun v => RowArray.naturalRows d v.val p.val.2,
   fun w => RowArray.naturalRows d w.val p.val.1)

/-- Degree sequence of an actual uniform simple graph with doubled edge count m[s,s]. -/
def internalGraphLaw (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (s : Universal.History (n+1)) : Measure (Block π s → ℕ) :=
  (uniformOn {G : SimpleGraph (Block π s) | 2 * (G.edgeFinset.card : ℤ) = m s s}).map
    (fun G v => G.degree v)

/-- Degree sequences of an actual uniform fixed-count bipartite edge set. -/
def crossGraphLaw (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (p : Pair (Universal.History (n+1))) :
    Measure ((Block π p.val.1 → ℕ) × (Block π p.val.2 → ℕ)) :=
  (uniformOn {E : CrossEdges (Block π p.val.1) (Block π p.val.2) |
    (E.ncard : ℤ) = m p.val.1 p.val.2}).map (fun E => ((fun v => leftDegree E v), (fun w => rightDegree E w)))

theorem internalGraphLaw_probability (y : Local.CoarseData V n)
    (s : Universal.History (n+1)) : IsProbabilityMeasure (internalGraphLaw y.part y.edge s) := by
  obtain ⟨G,hG⟩ := GraphicalArray.internalCount_nonempty y s
  have := isProbabilityMeasure_uniformOn
    (Set.toFinite {G : SimpleGraph (Block y.part s) | 2 * (G.edgeFinset.card : ℤ) = y.edge s s}) ⟨G,by simpa only [Set.mem_ofPred_eq, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hG⟩
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem crossGraphLaw_probability (y : Local.CoarseData V n)
    (p : Pair (Universal.History (n+1))) : IsProbabilityMeasure (crossGraphLaw y.part y.edge p) := by
  obtain ⟨E,hE⟩ := GraphicalArray.crossCount_nonempty y p
  have := isProbabilityMeasure_uniformOn
    (Set.toFinite {E : CrossEdges (Block y.part p.val.1) (Block y.part p.val.2) |
      (E.ncard : ℤ) = y.edge p.val.1 p.val.2}) ⟨E,by simpa only [Set.mem_ofPred_eq] using hE⟩
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem internalGraphLaw_half_count (y : Local.CoarseData V n)
    (s : Universal.History (n+1)) :
    internalGraphLaw y.part y.edge s =
      (uniformOn {G : SimpleGraph (Block y.part s) |
        G.edgeFinset.card = (y.edge s s / 2).toNat}).map (fun G v => G.degree v) := by
  have he : {G : SimpleGraph (Block y.part s) | 2 * (G.edgeFinset.card : ℤ) = y.edge s s} =
      {G : SimpleGraph (Block y.part s) | G.edgeFinset.card = (y.edge s s / 2).toNat} := by
    ext G
    simp only [Set.mem_ofPred_eq]
    have hnonneg := y.edge_nonneg s s
    rcases y.edge_even s with ⟨k,hk⟩
    omega
  unfold internalGraphLaw
  rw [he]

theorem internalVector_glue (π : V → Universal.History (n+1))
    (C : Components π) (s : Universal.History (n+1)) :
    internalVector π (RowArray.graphArray π (glue π C)) s = (fun v => (C.1 s).degree v) := by
  funext v
  apply Int.ofNat_inj.mp
  change RowArray.values (RowArray.graphArray π (glue π C)) v s = _
  rw [RowArray.values_graphArray]
  convert glue_internal_degree π C s v using 1
  simp only [SimpleGraph.degree]
  congr 2
  ext w
  simp

theorem crossVector_glue (π : V → Universal.History (n+1))
    (C : Components π) (p : Pair (Universal.History (n+1))) :
    crossVector π (RowArray.graphArray π (glue π C)) p =
      ((fun v => leftDegree (C.2 p) v), (fun w => rightDegree (C.2 p) w)) := by
  apply Prod.ext
  · funext v
    apply Int.ofNat_inj.mp
    change RowArray.values (RowArray.graphArray π (glue π C)) v p.val.2 = _
    rw [RowArray.values_graphArray]
    convert glue_left_degree π C p v using 1
    simp only [leftDegree, leftNeighbors]
    congr 2
    ext w
    simp
  · funext w
    apply Int.ofNat_inj.mp
    change RowArray.values (RowArray.graphArray π (glue π C)) w p.val.1 = _
    rw [RowArray.values_graphArray]
    convert glue_right_degree π C p w using 1
    simp only [rightDegree, rightNeighbors]
    congr 2
    ext v
    simp

/-- The full collection of block-pair vectors uniquely determines an ambient array. -/
theorem vectors_injective (π : V → Universal.History (n+1)) (a b : RowArray.Ambient π)
    (hi : ∀ s, internalVector π a s = internalVector π b s)
    (hc : ∀ p, crossVector π a p = crossVector π b p) : a = b := by
  apply RowArray.naturalRows_injective π
  funext v t
  rcases lt_trichotomy (π v) t with h | h | h
  · exact congrFun (congrArg Prod.fst (hc ⟨(π v,t),h⟩)) ⟨v,rfl⟩
  · subst t
    exact congrFun (hi (π v)) ⟨v,rfl⟩
  · exact congrFun (congrArg Prod.snd (hc ⟨(t,π v),h⟩)) ⟨v,rfl⟩

/-- Full joint law, not only individual graph-component marginals. -/
theorem graphical_rectangle (y : Local.CoarseData V n)
    (A : ∀ s : Universal.History (n+1), Set (Block y.part s → ℕ))
    (B : ∀ p : Pair (Universal.History (n+1)),
      Set ((Block y.part p.val.1 → ℕ) × (Block y.part p.val.2 → ℕ))) :
    GraphicalArray.law y.part y.edge
      {d | (∀ s, internalVector y.part d s ∈ A s) ∧
        ∀ p, crossVector y.part d p ∈ B p} =
      (∏ s, internalGraphLaw y.part y.edge s (A s)) *
        ∏ p, crossGraphLaw y.part y.edge p (B p) := by
  rw [← GraphicalArray.component_array_law y,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  simp only [Set.preimage_ofPred_eq, internalVector_glue, crossVector_glue]
  have hrect := GraphicalArray.component_rectangle y.part y.edge
    (fun s => {G | (fun v => G.degree v) ∈ A s})
    (fun p => {E | ((fun v => leftDegree E v), (fun w => rightDegree E w)) ∈ B p})
  simp only [Set.mem_ofPred_eq] at hrect
  convert hrect using 1
  · congr 1
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro s _
      rw [internalGraphLaw, Measure.map_apply (measurable_of_countable _)
        (Set.to_countable _).measurableSet]
      rfl
    · apply Finset.prod_congr rfl
      intro p _
      rw [crossGraphLaw, Measure.map_apply (measurable_of_countable _)
        (Set.to_countable _).measurableSet]
      rfl

/-- First identity in B.2's eq:enum-factor, valid even for nongraphical arrays.
The identity in fact holds on every bounded array, without a total-count premise. -/
theorem graphical_atom (y : Local.CoarseData V n) (d : RowArray.Ambient y.part) :
    GraphicalArray.law y.part y.edge {d} =
      (∏ s, internalGraphLaw y.part y.edge s {internalVector y.part d s}) *
        ∏ p, crossGraphLaw y.part y.edge p {crossVector y.part d p} := by
  have he : {a : RowArray.Ambient y.part |
      (∀ s, internalVector y.part a s ∈ ({internalVector y.part d s} : Set _)) ∧
      ∀ p, crossVector y.part a p ∈ ({crossVector y.part d p} : Set _)} = {d} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi,hc⟩
      exact vectors_injective y.part a d hi hc
    · rintro rfl
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  simpa only [he] using graphical_rectangle y (fun s => {internalVector y.part d s})
    (fun p => {crossVector y.part d p})

end MajorityDynamics.GraphProcess.BlockPairLaws
