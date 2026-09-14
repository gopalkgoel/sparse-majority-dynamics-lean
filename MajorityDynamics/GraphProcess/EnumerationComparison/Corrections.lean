import MajorityDynamics.GraphProcess.EnumerationComparison.Data

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Universal BlockDecomposition EnumerationBounds
open Literature.DegreeEnumeration
variable {V : Type*} [Fintype V] {n : ℕ}

theorem vec_squareSum (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) :
    (∑ i, ((vec y d s t i : ℝ) - avg y s t)^2) = squareSum y d s t := by
  change (∑ i, ((RowArray.values d ((blockEquiv y s).symm i) t : ℝ)-avg y s t)^2) = _
  rw [(blockEquiv y s).symm.sum_comp
    (fun v : Block y.part s => ((RowArray.values d v t : ℝ)-avg y s t)^2)]
  exact (Finset.sum_subtype (GraphProcess.History.block y.part s)
    (fun v => GraphProcess.History.mem_block y.part s v)
    (fun v => ((RowArray.values d v t : ℝ)-avg y s t)^2)).symm

theorem internal_correction_eq (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s : History (n+1)) :
    graphCorrection (y.edge s s /2).toNat (vec y d s s) =
      Real.exp (internalCorrection y d s) := by
  have he : graphAverage (y.sizes s) (y.edge s s /2).toNat = avg y s s := by
    rw [graphAverage, internal_count_cast]; rfl
  simp only [graphCorrection, graphGamma, graphDensity, he, vec_squareSum,
    internalCorrection, gamma2, muI]

theorem cross_correction_eq (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) :
    bipartiteCorrection (y.edge s t).toNat (vec y d s t) (vec y d t s) =
      Real.exp (crossCorrection y d s t) := by
  have he : leftAverage (y.sizes s) (y.edge s t).toNat = avg y s t := by
    rw [leftAverage, edge_cast]; rfl
  have he' : rightAverage (y.sizes t) (y.edge s t).toNat = avg y t s := by
    rw [rightAverage, edge_cast, y.edge_symm s t]; rfl
  simp only [bipartiteCorrection, leftVariance, rightVariance, he, he', vec_squareSum,
    bipartiteDensity, edge_cast, crossCorrection, variance, muC]
  congr 1
  ring

end MajorityDynamics.GraphProcess.EnumerationComparison
