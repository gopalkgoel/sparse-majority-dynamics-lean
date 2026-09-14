import MajorityDynamics.GraphProcess.RowArray.Conditioning

/-! Literal Section 3 array statistics, before imposing graphicality or exact totals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowArray
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

def totals {π : V → History (n + 1)} (d : Ambient π) := History.edgeTotals π (values d)
def exactTotals (π : V → History (n + 1))
    (m : History (n + 1) → History (n + 1) → ℤ) : Set (Ambient π) := {d | totals d = m}

/-- The exact Gamma predicate, using total real division also on empty fibers. -/
def Gamma (π : V → History (n + 1))
    (m : History (n + 1) → History (n + 1) → ℤ) (C p : ℝ) (d : Ambient π) : Prop :=
  ∀ s t, (1 / (p * (Fintype.card V : ℝ)^2)) *
    (∑ v ∈ History.block π s,
      ((values d v t : ℝ) - (m s t : ℝ) / (Local.partSizes π s : ℝ))^2) ≤ C

/-- Reuse the exact existing kappa predicate, centered at p times full part size. -/
def Regular (p : ℝ) {π : V → History (n + 1)} (d : Ambient π) : Prop :=
  CoarseKernel.Regular p π (values d)

/-- The paper's W_d[sb], defined on every ambient array. -/
def childSet {π : V → History (n + 1)} (d : Ambient π)
    (s : History (n + 1)) (b : Bool) : Finset V :=
  (History.block π s).filter fun v => realRow d v ∈ Universal.childEvent s b

/-- The paper's L_d[sb,t], an integer degree mass. -/
def childMass {π : V → History (n + 1)} (d : Ambient π)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) : ℤ :=
  ∑ v ∈ childSet d s b, values d v t

@[simp] theorem mem_childSet {π : V → History (n + 1)} (d : Ambient π)
    (s : History (n + 1)) (b : Bool) (v : V) :
    v ∈ childSet d s b ↔ π v = s ∧ realRow d v ∈ Universal.childEvent s b := by
  simp [childSet]

theorem childSet_disjoint {π : V → History (n + 1)} (d : Ambient π)
    (s : History (n + 1)) : Disjoint (childSet d s false) (childSet d s true) := by
  apply Finset.disjoint_left.mpr
  intro v hf ht
  exact Set.disjoint_left.mp (Universal.childEvent_disjoint s)
    ((mem_childSet _ _ _ _).mp hf).2 ((mem_childSet _ _ _ _).mp ht).2

theorem childSet_union {π : V → History (n + 1)} (d : Ambient π)
    (h : d ∈ history π) (s : History (n + 1)) :
    childSet d s false ∪ childSet d s true = History.block π s := by
  ext v
  simp only [Finset.mem_union, mem_childSet, History.mem_block, ← and_or_left]
  constructor
  · exact And.left
  · intro hv
    refine ⟨hv, ?_⟩
    have hh := h v
    rw [hv] at hh
    exact (Set.ext_iff.mp (Universal.childEvent_union s) (realRow d v)).mpr hh

theorem child_card_conservation {π : V → History (n + 1)} (d : Ambient π)
    (h : d ∈ history π) (s : History (n + 1)) :
    (childSet d s false).card + (childSet d s true).card = Local.partSizes π s := by
  rw [← Finset.card_union_of_disjoint (childSet_disjoint d s), childSet_union d h,
    History.block_card_partSizes]

theorem childMass_conservation {π : V → History (n + 1)} (d : Ambient π)
    (h : d ∈ history π) (s t : History (n + 1)) :
    childMass d s false t + childMass d s true t = totals d s t := by
  unfold childMass totals History.edgeTotals
  rw [← Finset.sum_union (childSet_disjoint d s), childSet_union d h]

@[simp] theorem stateArray_history (σ : FineState.State V n) : stateArray σ ∈ history σ.part := by
  intro v
  rw [realRow_stateArray]
  exact σ.history v

@[simp] theorem childSet_stateArray (σ : FineState.State V n)
    (s : History (n + 1)) (b : Bool) :
    childSet (stateArray σ) s b = History.block (FineState.refinement σ) (append s b) := by
  ext v
  simp only [mem_childSet, realRow_stateArray, History.mem_block]
  exact (FineState.refinement_fiber σ v s b).symm

@[simp] theorem childMass_stateArray (σ : FineState.State V n)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    childMass (stateArray σ) s b t =
      ∑ v ∈ History.block (FineState.refinement σ) (append s b), σ.deg v t := by
  simp only [childMass, childSet_stateArray, values_stateArray]

@[simp] theorem totals_graphArray (π : V → History (n + 1)) (G : SimpleGraph V) :
    totals (graphArray π G) = History.edgeTotals π (History.degreeArray π G) := by
  simp only [totals, values_graphArray]

@[simp] theorem totals_stateArray (σ : FineState.State V n) :
    totals (stateArray σ) = History.edgeTotals σ.part σ.deg := by
  simp only [totals, values_stateArray]

@[simp] theorem regular_stateArray (p : ℝ) (σ : FineState.State V n) :
    Regular p (stateArray σ) ↔ CoarseKernel.Regular p σ.part σ.deg := by
  simp only [Regular, values_stateArray]

end MajorityDynamics.GraphProcess.RowArray
