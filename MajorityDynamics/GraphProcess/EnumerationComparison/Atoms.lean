import MajorityDynamics.GraphProcess.EnumerationComparison.Relabel
import MajorityDynamics.GraphProcess.EnumerationComparison.ComponentLaws
import MajorityDynamics.GraphProcess.EnumerationComparison.Corrections

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Universal BlockDecomposition EnumerationBounds BlockPairLaws
open Literature.DegreeEnumeration
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Transport the cited finite-ordinal graph atom estimate to the literal internal
component. The diagonal half count and correction are unchanged. -/
theorem relative_internal (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    {T p : ℝ} (h : Prepared y d T p) (htot : RowArray.totals d = y.edge)
    (s : History (n+1))
    (hsource : RelativeApproximation (1/2)
      ((graphDegreeLaw (Fin (y.sizes s)) (y.edge s s/2).toNat).real {vec y d s s})
      ((graphBinomialLaw (Fin (y.sizes s)) (y.edge s s/2).toNat).real {vec y d s s} *
        graphCorrection (y.edge s s/2).toNat (vec y d s s))) :
    RelativeApproximation (1/2)
      ((internalGraphLaw y.part y.edge s).real {internalVector y.part d s})
      (((internalBinomialLaw y.part y.edge s).real {internalVector y.part d s}) *
        Real.exp (internalCorrection y d s)) := by
  have hv := vec_source_internal y d h htot s
  have hs : ∑ v, internalVector y.part d s v = 2*(y.edge s s/2).toNat := by
    have hh := (blockEquiv y s).symm.sum_comp (internalVector y.part d s)
    rw [← hh]
    exact hv.2.1
  have hcap : 2*(y.edge s s/2).toNat ≤
      Fintype.card (Block y.part s)*(Fintype.card (Block y.part s)-1) := by
    rw [block_card, ← hv.2.1]
    calc
      _ ≤ ∑ _i : Fin (y.sizes s), (y.sizes s-1) :=
        Finset.sum_le_sum fun i _ => hv.1 i
      _ = _ := by simp
  rw [internalGraphLaw_eq_source, internalBinomialLaw_eq_source,
    graphDegreeLaw_real_relabel (blockEquiv y s) _ _ hs,
    graphBinomialLaw_real_relabel (blockEquiv y s) _ _ hcap hs]
  rw [internal_correction_eq] at hsource
  exact hsource

/-- Both literal oriented cross vectors transport together, retaining the actual
cross total and its two variance corrections. -/
theorem relative_cross (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    {T p : ℝ} (h : Prepared y d T p) (htot : RowArray.totals d = y.edge)
    (r : Pair (History (n+1)))
    (hsource : RelativeApproximation (1/2)
      ((bipartiteDegreeLaw (Fin (y.sizes r.val.1)) (Fin (y.sizes r.val.2))
        (y.edge r.val.1 r.val.2).toNat).real
        {(vec y d r.val.1 r.val.2,vec y d r.val.2 r.val.1)})
      ((bipartiteBinomialLaw (Fin (y.sizes r.val.1)) (Fin (y.sizes r.val.2))
        (y.edge r.val.1 r.val.2).toNat).real
        {(vec y d r.val.1 r.val.2,vec y d r.val.2 r.val.1)} *
        bipartiteCorrection (y.edge r.val.1 r.val.2).toNat
          (vec y d r.val.1 r.val.2) (vec y d r.val.2 r.val.1))) :
    RelativeApproximation (1/2)
      ((crossGraphLaw y.part y.edge r).real {crossVector y.part d r})
      (((crossBinomialLaw y.part y.edge r).real {crossVector y.part d r}) *
        Real.exp (crossCorrection y d r.val.1 r.val.2)) := by
  have hv := vec_source_cross y d h htot r.val.1 r.val.2 (ne_of_lt r.property)
  have ha : ∑ v, (crossVector y.part d r).1 v = (y.edge r.val.1 r.val.2).toNat := by
    rw [← (blockEquiv y r.val.1).symm.sum_comp (crossVector y.part d r).1]
    exact hv.2.2.1
  have hb : ∑ v, (crossVector y.part d r).2 v = (y.edge r.val.1 r.val.2).toNat := by
    rw [← (blockEquiv y r.val.2).symm.sum_comp (crossVector y.part d r).2]
    exact hv.2.2.2.1
  have hcap : (y.edge r.val.1 r.val.2).toNat ≤
      Fintype.card (Block y.part r.val.1)*Fintype.card (Block y.part r.val.2) := by
    rw [block_card,block_card,← hv.2.2.1]
    calc
      _ ≤ ∑ _i : Fin (y.sizes r.val.1), y.sizes r.val.2 :=
        Finset.sum_le_sum fun i _ => hv.1 i
      _ = _ := by simp
  rw [crossGraphLaw_eq_source,crossBinomialLaw_eq_source]
  change RelativeApproximation _
    ((bipartiteDegreeLaw _ _ _).real {((crossVector y.part d r).1,(crossVector y.part d r).2)})
    (((bipartiteBinomialLaw _ _ _).real {((crossVector y.part d r).1,(crossVector y.part d r).2)}) * _)
  rw [bipartiteDegreeLaw_real_relabel (blockEquiv y r.val.1) (blockEquiv y r.val.2) _ _ _ ha,
    bipartiteBinomialLaw_real_relabel (blockEquiv y r.val.1) (blockEquiv y r.val.2) _ _ _ hcap ha hb]
  rw [cross_correction_eq] at hsource
  exact hsource

end MajorityDynamics.GraphProcess.EnumerationComparison

/-- info: 'MajorityDynamics.GraphProcess.EnumerationComparison.relative_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationComparison.relative_internal

/-- info: 'MajorityDynamics.GraphProcess.EnumerationComparison.relative_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationComparison.relative_cross
