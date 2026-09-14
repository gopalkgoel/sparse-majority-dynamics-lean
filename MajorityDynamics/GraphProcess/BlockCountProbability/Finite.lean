import MajorityDynamics.GraphProcess.BlockCountProbability.FiniteSites

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockCountProbability
open History BlockDecomposition GraphicalArray
open MajorityDynamics.Probability.DegreeConcentration
variable {V : Type*} [Fintype V] {n : ℕ}

theorem diagonal_target_cast (y : Local.CoarseData V n) (s : Universal.History (n+1)) :
    2 * (((y.edge s s / 2).toNat : ℕ) : ℤ) = y.edge s s := by
  obtain ⟨z,hz⟩ := y.edge_even s
  have hn := y.edge_nonneg s s
  omega

theorem cross_target_cast (y : Local.CoarseData V n)
    (z : Pair (Universal.History (n+1))) :
    ((y.edge z.val.1 z.val.2).toNat : ℤ) = y.edge z.val.1 z.val.2 :=
  Int.toNat_of_nonneg (y.edge_nonneg _ _)

theorem fixedCount_event (y : Local.CoarseData V n) :
    fixedCountFamily y.part y.edge =
      {G : SimpleGraph V | History.edgeTotals y.part (History.degreeArray y.part G) = y.edge} := rfl

theorem fixedCount_site_event (y : Local.CoarseData V n) (ω : Sym2 V → Prop) :
    graphOf ω ∈ fixedCountFamily y.part y.edge ↔
      (∀ s, blockCount (internalSites y.part s) ω = (y.edge s s / 2).toNat) ∧
      (∀ z : Pair (Universal.History (n+1)),
        blockCount (crossSites y.part z) ω = (y.edge z.val.1 z.val.2).toNat) := by
  rw [counts_iff y.part y.edge y.edge_symm]
  apply and_congr
  · apply forall_congr'
    intro s
    rw [internalSites_count]
    have hh := diagonal_target_cast y s
    omega
  · apply forall_congr'
    intro z
    rw [crossSites_count]
    have hh := cross_target_cast y z
    omega

/-- Exact finite product of the actual Bernoulli graph's block-count probabilities.
The identity holds also for endpoint parameters and empty blocks. -/
theorem exact_factorization (p : unitInterval) (y : Local.CoarseData V n) :
    (SimpleGraph.binomialRandom V p).real (fixedCountFamily y.part y.edge) =
      (∏ s, (binomial ((y.sizes s).choose 2) p).real {(y.edge s s / 2).toNat}) *
      (∏ z : Pair (Universal.History (n+1)),
        (binomial (y.sizes z.val.1 * y.sizes z.val.2) p).real
          {(y.edge z.val.1 z.val.2).toNat}) := by
  let k : Universal.History (n+1) ⊕ Pair (Universal.History (n+1)) → ℕ :=
    Sum.elim (fun s => (y.edge s s / 2).toNat)
      (fun z => (y.edge z.val.1 z.val.2).toNat)
  let μ := siteLaw (Sym2.diagSetᶜ : Set (Sym2 V)) p
  have hgraph : SimpleGraph.binomialRandom V p = μ.map graphOf :=
    binomialRandom_eq_map_siteLaw V p
  have hind := blockCount_iIndepFun (Sym2.diagSetᶜ : Set (Sym2 V)) p
    (sites y.part) (sites_disjoint y.part)
  have hprod := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun j => {k j}) (fun _ _ => measurableSet_singleton _)
  have hevent : graphOf ⁻¹' fixedCountFamily y.part y.edge =
      ⋂ j, blockCount (sites y.part j) ⁻¹' ({k j} : Set ℕ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_singleton_iff,
      fixedCount_site_event]
    constructor
    · intro h j
      cases j with
      | inl s => exact h.1 s
      | inr z => exact h.2 z
    · intro h
      exact ⟨fun s => h (.inl s), fun z => h (.inr z)⟩
  simp only [Finset.mem_univ, Set.iInter_true] at hprod
  have hatom (j : Universal.History (n+1) ⊕ Pair (Universal.History (n+1))) :
      μ (blockCount (sites y.part j) ⁻¹' ({k j} : Set ℕ)) =
        binomial (sites y.part j).card p {k j} := by
    rw [← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      siteLaw_map_blockCount _ p _ (sites_nondiag y.part j)]
  rw [hgraph, map_measureReal_apply (measurable_of_countable _) (Set.toFinite _).measurableSet,
    hevent, measureReal_def]
  change (μ (⋂ j, blockCount (sites y.part j) ⁻¹' {k j})).toReal = _
  rw [hprod]
  change (∏ j, μ (blockCount (sites y.part j) ⁻¹' {k j})).toReal = _
  simp_rw [hatom]
  rw [ENNReal.toReal_prod, Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro s _
    change (binomial (internalSites y.part s).card p {(y.edge s s / 2).toNat}).toReal = _
    rw [internalSites_card]
    have hc : Fintype.card (Block y.part s) = y.sizes s := by
      rw [Fintype.card_subtype]
      rfl
    simp only [← Nat.card_eq_fintype_card] at hc ⊢
    rw [hc]
    rfl
  · apply Finset.prod_congr rfl
    intro z _
    change (binomial (crossSites y.part z).card p {(y.edge z.val.1 z.val.2).toNat}).toReal = _
    rw [crossSites_card]
    have hc (s : Universal.History (n+1)) : Fintype.card (Block y.part s) = y.sizes s := by
      rw [Fintype.card_subtype]
      rfl
    simp only [← Nat.card_eq_fintype_card] at hc ⊢
    rw [hc, hc]
    rfl

end MajorityDynamics.GraphProcess.BlockCountProbability
