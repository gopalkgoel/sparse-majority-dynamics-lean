import MajorityDynamics.GraphProcess.EnumerationComparison.Scales
import MajorityDynamics.GraphProcess.AutomaticGraphicality.Basic

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Universal BlockDecomposition EnumerationBounds
open Literature.DegreeEnumeration Probability.NeighborhoodBulk
variable {V : Type*} [Fintype V] {n : ℕ}

theorem block_card (y : Local.CoarseData V n) (s : History (n+1)) :
    Fintype.card (Block y.part s) = y.sizes s := by
  change Fintype.card {v // y.part v = s} = _
  simp [Local.CoarseData.sizes, Local.partSizes, Fintype.card_subtype]

def blockEquiv (y : Local.CoarseData V n) (s : History (n+1)) :
    Block y.part s ≃ Fin (y.sizes s) := Fintype.equivFinOfCardEq (block_card y s)

def vec (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) : Fin (y.sizes s) → ℕ :=
  fun i => RowArray.naturalRows d ((blockEquiv y s).symm i) t

theorem vec_sum (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (htot : RowArray.totals d = y.edge) (s t : History (n+1)) :
    ∑ i, vec y d s t i = (y.edge s t).toNat := by
  have hz : ((∑ i, vec y d s t i : ℕ) : ℤ) = y.edge s t := by
    push_cast
    change (∑ i, RowArray.values d ((blockEquiv y s).symm i) t) = _
    rw [(blockEquiv y s).symm.sum_comp (fun v : Block y.part s => RowArray.values d v t)]
    exact AutomaticGraphicality.block_sum_eq y d htot s t
  omega

theorem internal_count_cast (y : Local.CoarseData V n) (s : History (n+1)) :
    2 * (((y.edge s s / 2).toNat : ℕ) : ℝ) = (y.edge s s : ℝ) := by
  have hn := y.edge_nonneg s s
  obtain ⟨j,hj⟩ := y.edge_even s
  have he : 2 * ((y.edge s s / 2).toNat : ℤ) = y.edge s s := by omega
  exact_mod_cast he

theorem edge_cast (y : Local.CoarseData V n) (s t : History (n+1)) :
    (((y.edge s t).toNat : ℕ) : ℝ) = (y.edge s t : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (y.edge_nonneg s t)

theorem vec_source_internal (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    {T p : ℝ} (h : Prepared y d T p) (htot : RowArray.totals d = y.edge)
    (s : History (n+1)) :
    GraphSourceData (7/12) (y.sizes s) (y.edge s s / 2).toNat (vec y d s s) := by
  have he : graphAverage (y.sizes s) (y.edge s s / 2).toNat = avg y s s := by
    rw [graphAverage, internal_count_cast]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hb : RowArray.naturalRows d ((blockEquiv y s).symm i) s ≤
        Local.trials (Local.partSizes y.part) (y.part ((blockEquiv y s).symm i)) s :=
      Nat.le_of_lt_succ (d ((blockEquiv y s).symm i) s).isLt
    have hv := ((blockEquiv y s).symm i).property
    rw [hv] at hb
    simpa only [vec, Local.CoarseData.sizes,
      Local.trials_self, Nat.lt_succ_iff] using hb
  · rw [vec_sum y d htot]
    have hn := y.edge_nonneg s s
    obtain ⟨j,hj⟩ := y.edge_even s
    omega
  · intro i
    rw [he]
    exact_mod_cast h.entry_enumeration s s ((blockEquiv y s).symm i)
      (History.mem_block _ _ _ |>.mpr ((blockEquiv y s).symm i).property)

theorem vec_source_cross (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    {T p : ℝ} (h : Prepared y d T p) (htot : RowArray.totals d = y.edge)
    (s t : History (n+1)) (hst : s ≠ t) :
    BipartiteSourceData (7/12) (y.sizes s) (y.sizes t) (y.edge s t).toNat
      (vec y d s t) (vec y d t s) := by
  have he : leftAverage (y.sizes s) (y.edge s t).toNat = avg y s t := by
    rw [leftAverage, edge_cast]; rfl
  have he' : rightAverage (y.sizes t) (y.edge s t).toNat = avg y t s := by
    rw [rightAverage, edge_cast, y.edge_symm s t]; rfl
  refine ⟨?_, ?_, vec_sum y d htot s t, ?_, ?_, ?_⟩
  · intro i
    have hb : RowArray.naturalRows d ((blockEquiv y s).symm i) t ≤
        Local.trials (Local.partSizes y.part) (y.part ((blockEquiv y s).symm i)) t :=
      Nat.le_of_lt_succ (d ((blockEquiv y s).symm i) t).isLt
    have hv := ((blockEquiv y s).symm i).property
    rw [hv] at hb
    simpa only [vec, Local.CoarseData.sizes,
      Local.trials_other _ hst, Nat.lt_succ_iff] using hb
  · intro i
    have hb : RowArray.naturalRows d ((blockEquiv y t).symm i) s ≤
        Local.trials (Local.partSizes y.part) (y.part ((blockEquiv y t).symm i)) s :=
      Nat.le_of_lt_succ (d ((blockEquiv y t).symm i) s).isLt
    have hv := ((blockEquiv y t).symm i).property
    rw [hv] at hb
    simpa only [vec, Local.CoarseData.sizes,
      Local.trials_other _ hst.symm, Nat.lt_succ_iff] using hb
  · rw [vec_sum y d htot, y.edge_symm t s]
  · intro i
    rw [he]
    exact_mod_cast h.entry_enumeration s t ((blockEquiv y s).symm i)
      (History.mem_block _ _ _ |>.mpr ((blockEquiv y s).symm i).property)
  · intro i
    rw [he']
    exact_mod_cast h.entry_enumeration t s ((blockEquiv y t).symm i)
      (History.mem_block _ _ _ |>.mpr ((blockEquiv y t).symm i).property)

end MajorityDynamics.GraphProcess.EnumerationComparison
