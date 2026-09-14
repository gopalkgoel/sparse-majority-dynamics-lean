import MajorityDynamics.GraphProcess.GraphicalArray.Law
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.GraphicalArray
open History BlockDecomposition FineKernel
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Ordered diagonal counts sample exactly m[s,s]/2 loopless edges. -/
theorem internal_half_count (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (s : Universal.History (n+1)) (G : InternalCountFiber π m s) :
    G.val.edgeFinset.card = (m s s / 2).toNat := by
  have h := G.property
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h ⊢
  omega

/-- Independent uniform fixed-edge-count blocks, before imposing histories or regularity. -/
def componentLaw (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ) :
    Measure (CountComponents π m) := uniformOn Set.univ

theorem componentLaw_probability (y : Local.CoarseData V n) :
    IsProbabilityMeasure (componentLaw y.part y.edge) := by
  obtain ⟨G,hG⟩ := coarse_fixedCount_nonempty y
  have : Nonempty (CountComponents y.part y.edge) :=
    ⟨countRestrict y.part y.edge y.edge_symm ⟨G,hG⟩⟩
  exact ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ

theorem internal_value_law (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (s : Universal.History (n+1)) :
    (uniformOn (Set.univ : Set (InternalCountFiber π m s))).map Subtype.val =
      uniformOn {G : SimpleGraph (Block π s) | 2 * (G.edgeFinset.card : ℤ) = m s s} := by
  let e : InternalCountFiber π m s ≃
      {G : SimpleGraph (Block π s) // 2 * (G.edgeFinset.card : ℤ) = m s s} :=
    { toFun G := ⟨G.val, by
        have h := G.property
        simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h⟩
      invFun G := ⟨G.val, by
        have h := G.property
        simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h⟩ }
  exact map_uniform_fiber _ e

/-- Full joint rectangle law for actual internal graphs and single-orientation cross edges. -/
theorem component_rectangle (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (A : ∀ s : Universal.History (n+1), Set (SimpleGraph (Block π s)))
    (B : ∀ p : Pair (Universal.History (n+1)),
      Set (CrossEdges (Block π p.val.1) (Block π p.val.2))) :
    componentLaw π m {F | (∀ s, (F.1 s).val ∈ A s) ∧ ∀ p, (F.2 p).val ∈ B p} =
      (∏ s, uniformOn {G : SimpleGraph (Block π s) | 2 * (G.edgeFinset.card : ℤ) = m s s} (A s)) *
      ∏ p : Pair (Universal.History (n+1)),
        uniformOn {E : CrossEdges (Block π p.val.1) (Block π p.val.2) |
          (E.ncard : ℤ) = m p.val.1 p.val.2} (B p) := by
  change uniformOn Set.univ
    (({F : ∀ s, InternalCountFiber π m s | ∀ s, (F s).val ∈ A s}) ×ˢ
      ({F : ∀ p : Pair (Universal.History (n+1)), CrossCountFiber π m p |
        ∀ p, (F p).val ∈ B p})) = _
  rw [uniform_prod_rectangle]
  apply congrArg₂ (· * ·)
  · calc
      _ = ∏ s, uniformOn (Set.univ : Set (InternalCountFiber π m s))
          {G | G.val ∈ A s} := uniform_pi_rectangle _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro s _
        rw [← internal_value_law, Measure.map_apply (measurable_of_countable _)
          (Set.toFinite _).measurableSet]
        rfl
  · calc
      _ = ∏ p : Pair (Universal.History (n+1)),
          uniformOn (Set.univ : Set (CrossCountFiber π m p))
            {E | E.val ∈ B p} := uniform_pi_rectangle _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p _
        have h := congrArg (fun μ : Measure (CrossEdges (Block π p.val.1) (Block π p.val.2)) => μ (B p))
          (map_uniform_subtype {E : CrossEdges (Block π p.val.1) (Block π p.val.2) |
            (E.ncard : ℤ) = m p.val.1 p.val.2})
        rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet] at h
        exact h

/-- Literal gluing of the independently sampled fixed-count blocks is the uniform graph law. -/
theorem glue_componentLaw (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (hm : ∀ s t, m s t = m t s) :
    (componentLaw π m).map (fun C => glue π (countComponents π m C)) = graphLaw π m :=
  map_uniform_fiber _ (countFiberEquiv π m hm).symm

theorem component_array_law (y : Local.CoarseData V n) :
    (componentLaw y.part y.edge).map
      (fun C => RowArray.graphArray y.part (glue y.part (countComponents y.part y.edge C))) =
        law y.part y.edge := by
  rw [← Function.comp_def, ← Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _), glue_componentLaw y.part y.edge y.edge_symm]
  rfl

end MajorityDynamics.GraphProcess.GraphicalArray
