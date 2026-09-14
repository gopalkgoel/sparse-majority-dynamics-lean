import MajorityDynamics.GraphProcess.History.Aggregation

/-! Section 2's actual history partitions, degree arrays, and deterministic refinement. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.History
open Universal
open Probability.RandomOpinionsReduction (coloringOnDayV)
variable {V : Type*} [Fintype V]

theorem opinion_injective : Function.Injective Paper.opinion := by
  intro a b h
  cases a <;> cases b <;> simp_all [Paper.opinion]

theorem mem_actualBlock_opinions (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (s : Universal.History k) :
    v ∈ block (actualHistory G c k) s ↔ ∀ r : Fin k,
      Paper.opinion (coloringOnDayV G c (r.val + 1) v) = Paper.opinion (bits k s r) := by
  simp only [mem_actualBlock, opinion_injective.eq_iff]

/-- The literal paper convention for all natural-number days 1 through k. -/
theorem mem_actualBlock_days (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (s : Universal.History k) :
    v ∈ block (actualHistory G c k) s ↔ ∀ r : ℕ, (hr : 1 ≤ r ∧ r ≤ k) →
      Paper.opinion (coloringOnDayV G c r v) =
        Paper.opinion (bits k s ⟨r - 1, by omega⟩) := by
  rw [mem_actualBlock_opinions]
  constructor
  · intro h r hr
    simpa only [Nat.sub_add_cancel hr.1] using h ⟨r - 1, by omega⟩
  · intro h r
    simpa only [Nat.add_sub_cancel] using h (r.val + 1) ⟨by omega, by omega⟩

/-- An actual graph supplies every structural coarse-state field, for either flag. -/
def actualCoarseData (G : SimpleGraph V) (c : V → Bool) (n : ℕ) (flag : Bool) :
    Local.CoarseData V n := toCoarseData (actualHistory G c (n + 1)) G flag

@[simp] theorem actualCoarseData_part (G : SimpleGraph V) (c : V → Bool) (n : ℕ) (flag : Bool) :
    (actualCoarseData G c n flag).part = actualHistory G c (n + 1) := rfl

@[simp] theorem actualCoarseData_edge (G : SimpleGraph V) (c : V → Bool) (n : ℕ) (flag : Bool) :
    (actualCoarseData G c n flag).edge =
      edgeTotals (actualHistory G c (n + 1)) (degreeArray (actualHistory G c (n + 1)) G) := rfl

@[simp] theorem actualCoarseData_reg (G : SimpleGraph V) (c : V → Bool) (n : ℕ) (flag : Bool) :
    (actualCoarseData G c n flag).reg = flag := rfl

/-- Set-level deterministic refinement, with the original child event and integer degrees. -/
theorem child_block_event_set (G : SimpleGraph V) (c : V → Bool) (n : ℕ)
    (s : Universal.History (n + 1)) (b : Bool) :
    ({v : V | actualHistory G c (n + 2) v = append s b} : Set V) =
      {v | actualHistory G c (n + 1) v = s ∧
        actualRow G c (n + 1) v ∈ childEvent s b} := by
  ext v
  simpa only [Set.mem_ofPred_eq, mem_block] using child_block_event G c n v s b

end MajorityDynamics.GraphProcess.History
