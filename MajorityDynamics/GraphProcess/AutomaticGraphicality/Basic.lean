import MajorityDynamics.GraphProcess.GraphicalArray.Law

/-! Literal degree sums on the actual partition blocks. -/
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.AutomaticGraphicality
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

theorem block_sum (π : V → Universal.History (n + 1))
    (d : RowArray.Ambient π) (s t : Universal.History (n + 1)) :
    (∑ v : Block π s, RowArray.values d v t) = RowArray.totals d s t := by
  exact (Finset.sum_subtype (History.block π s) (fun v => History.mem_block π s v)
    (fun v => RowArray.values d v t)).symm

theorem block_sum_eq (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (htot : RowArray.totals d = y.edge) (s t : Universal.History (n + 1)) :
    (∑ v : Block y.part s, RowArray.values d v t) = y.edge s t := by
  rw [block_sum, htot]

theorem block_sum_even (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (htot : RowArray.totals d = y.edge) (s : Universal.History (n + 1)) :
    Even (∑ v : Block y.part s, RowArray.values d v s) := by
  rw [block_sum_eq y d htot]
  exact y.edge_even s

theorem opposite_sums (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (htot : RowArray.totals d = y.edge) (s t : Universal.History (n + 1)) :
    (∑ v : Block y.part s, RowArray.values d v t) =
      ∑ w : Block y.part t, RowArray.values d w s := by
  rw [block_sum_eq y d htot, block_sum_eq y d htot, y.edge_symm]

end MajorityDynamics.GraphProcess.AutomaticGraphicality
