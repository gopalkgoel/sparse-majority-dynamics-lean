import MajorityDynamics.GraphProcess.BlockPairLaws.Main
import MajorityDynamics.Literature.DegreeEnumeration.ComparisonLaws

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Universal BlockDecomposition
open Literature.DegreeEnumeration
variable {V : Type*} [Fintype V] {n : ℕ}

theorem internalGraphLaw_eq_source (y : Local.CoarseData V n) (s : History (n+1)) :
    BlockPairLaws.internalGraphLaw y.part y.edge s =
      graphDegreeLaw (Block y.part s) (y.edge s s / 2).toNat := by
  rw [BlockPairLaws.internalGraphLaw_half_count]
  rfl

theorem crossGraphLaw_eq_source (y : Local.CoarseData V n) (r : Pair (History (n+1))) :
    BlockPairLaws.crossGraphLaw y.part y.edge r =
      bipartiteDegreeLaw (Block y.part r.val.1) (Block y.part r.val.2)
        (y.edge r.val.1 r.val.2).toNat := by
  have he : {E : Probability.FixedDegreeSampling.CrossEdges
      (Block y.part r.val.1) (Block y.part r.val.2) |
      (E.ncard : ℤ) = y.edge r.val.1 r.val.2} =
      crossEdgeFamily (Block y.part r.val.1) (Block y.part r.val.2)
        (y.edge r.val.1 r.val.2).toNat := by
    ext E
    have hn := y.edge_nonneg r.val.1 r.val.2
    simp only [crossEdgeFamily, Set.mem_ofPred_eq]
    omega
  unfold BlockPairLaws.crossGraphLaw bipartiteDegreeLaw fixedEdgeBipartiteLaw
  rw [he]

theorem internalBinomialLaw_eq_source (y : Local.CoarseData V n) (s : History (n+1)) :
    BlockPairLaws.internalBinomialLaw y.part y.edge s =
      graphBinomialLaw (Block y.part s) (y.edge s s / 2).toNat := by
  have hc : Fintype.card (Block y.part s) = Local.partSizes y.part s := by
    simp [Block, Local.partSizes, Fintype.card_subtype]
  have he : {a : Block y.part s → ℕ | ∑ v, (a v : ℤ) = y.edge s s} =
      {a | ∑ v, a v = 2 * (y.edge s s / 2).toNat} := by
    ext a
    have hn := y.edge_nonneg s s
    obtain ⟨j,hj⟩ := y.edge_even s
    have hsum : ∑ v, (a v : ℤ) = ((∑ v, a v : ℕ) : ℤ) := by simp
    simp only [Set.mem_ofPred_eq, hsum]
    omega
  rw [BlockPairLaws.internalBinomialLaw_eq, he]
  unfold graphBinomialLaw independentBinomials
  rw [hc]
  rfl

theorem cond_prod_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set A) (T : Set B) :
    (cond μ S).prod (cond ν T) = cond (μ.prod ν) (S ×ˢ T) := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.prod_restrict, smul_smul, Measure.prod_prod, ENNReal.mul_inv]
  · exact Or.inr (measure_ne_top _ _)
  · exact Or.inl (measure_ne_top _ _)

theorem crossBinomialLaw_eq_source (y : Local.CoarseData V n) (r : Pair (History (n+1))) :
    BlockPairLaws.crossBinomialLaw y.part y.edge r =
      bipartiteBinomialLaw (Block y.part r.val.1) (Block y.part r.val.2)
        (y.edge r.val.1 r.val.2).toNat := by
  have hc (s : History (n+1)) : Fintype.card (Block y.part s) = Local.partSizes y.part s := by
    simp [Block, Local.partSizes, Fintype.card_subtype]
  have he (s : History (n+1)) :
      {a : Block y.part s → ℕ | ∑ v, (a v : ℤ) = y.edge r.val.1 r.val.2} =
      {a | ∑ v, a v = (y.edge r.val.1 r.val.2).toNat} := by
    ext a
    have hn := y.edge_nonneg r.val.1 r.val.2
    have hsum : ∑ v, (a v : ℤ) = ((∑ v, a v : ℕ) : ℤ) := by simp
    simp only [Set.mem_ofPred_eq, hsum]
    omega
  rw [BlockPairLaws.crossBinomialLaw_eq, he, he, cond_prod_eq]
  unfold bipartiteBinomialLaw bipartiteIndependentLaw independentBinomials
  rw [hc, hc]
  rfl

end MajorityDynamics.GraphProcess.EnumerationComparison
