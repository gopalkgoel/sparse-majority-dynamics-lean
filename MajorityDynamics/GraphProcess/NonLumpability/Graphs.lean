import MajorityDynamics.GraphProcess.CoarseKernel.Basic

/-! Two concrete graph-realizable states in one coarse fiber. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.NonLumpability
open Universal FineState History CoarseKernel

/-- False is the first four vertices, true the last four. -/
def coloring (v : Fin 8) : Bool := decide (4 ≤ v.val)

/-- The common two cycles, followed by one of two four-edge cross graphs. -/
def edges (variant : Bool) : Finset (ℕ × ℕ) :=
  {(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4)} ∪
    if variant then {(0,4),(0,5),(0,6),(1,7)} else {(0,4),(1,5),(2,6),(3,7)}

def graph (variant : Bool) : SimpleGraph (Fin 8) where
  Adj v w := v.val ≠ w.val ∧ ((v.val,w.val) ∈ edges variant ∨ (w.val,v.val) ∈ edges variant)
  symm := ⟨by intro v w h; exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- One-bit history with prescribed color. No ordering of `bits` is assumed. -/
def label (b : Bool) : Universal.History 1 := (bits 1).symm (fun _ => b)

theorem label_injective : Function.Injective label := by
  intro a b h
  have hh := congrArg (fun s => bits 1 s 0) h
  simpa [label] using hh

theorem label_exhaust (s : Universal.History 1) : label (bits 1 s 0) = s := by
  apply (bits 1).injective
  ext i
  fin_cases i
  simp [label]

def partition (v : Fin 8) : Universal.History 1 := label (coloring v)

def state (variant : Bool) : State (Fin 8) 0 := actualState (graph variant) coloring 0

theorem state_part (variant : Bool) : (state variant).part = partition := by
  funext v
  apply (bits 1).injective
  ext i
  fin_cases i
  simp [state, actualState, actualHistory, partition, label,
    Probability.RandomOpinionsReduction.coloringOnDayV]

/-- The actual integer degree in a color block. -/
def rawDegree (variant : Bool) (v : Fin 8) (b : Bool) : ℤ :=
  ∑ w : Fin 8, if coloring w = b ∧ (graph variant).Adj v w then 1 else 0

theorem state_degree (variant : Bool) (v : Fin 8) (b : Bool) :
    (state variant).deg v (label b) = rawDegree variant v b := by
  classical
  change degreeArray (state variant).part (graph variant) v (label b) = _
  rw [state_part]
  simp only [degreeArray, block, Finset.sum_filter, partition, label_injective.eq_iff]
  unfold rawDegree
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp_all

set_option maxHeartbeats 1000000 in
theorem rawDegree_bounds (variant : Bool) (v : Fin 8) (b : Bool) :
    0 ≤ rawDegree variant v b ∧ rawDegree variant v b ≤ 3 := by
  simp only [rawDegree, Fin.sum_univ_succ, Fin.sum_univ_zero]
  cases variant <;> fin_cases v <;> cases b <;>
    norm_num [coloring, graph, edges]
  all_goals norm_num [Fin.ext_iff]

theorem partition_size (b : Bool) : Local.partSizes partition (label b) = 4 := by
  classical
  rw [← block_card_partSizes]
  simp only [block, partition, label_injective.eq_iff]
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  cases b <;> norm_num [coloring]

set_option maxHeartbeats 1000000 in
theorem state_edges (variant : Bool) (a b : Bool) :
    edgeTotals (state variant).part (state variant).deg (label a) (label b) =
      if a = b then 8 else 4 := by
  classical
  rw [state_part]
  simp only [edgeTotals, block, Finset.sum_filter, partition, label_injective.eq_iff,
    state_degree]
  simp only [rawDegree, Fin.sum_univ_succ, Fin.sum_univ_zero]
  cases variant <;> cases a <;> cases b <;>
    norm_num [coloring, graph, edges]
  all_goals norm_num [Fin.ext_iff]

end MajorityDynamics.GraphProcess.NonLumpability
