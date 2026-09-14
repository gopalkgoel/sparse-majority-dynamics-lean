import MajorityDynamics.GraphProcess.FineState.Projection

/-! The next partition is determined by the state; every realizer gives a valid next state. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.FineState
open Universal History
open Probability.RandomOpinionsReduction (coloringOnDayV nextColoringV)
variable {V : Type*} [Fintype V] {n : ℕ}
local instance : DecidableEq V := Classical.typeDecidableEq V

def decideColor (old : Bool) (z : ℝ) : Bool :=
  if 0 < z then false else if z < 0 then true else old

theorem decideColor_eq_iff (old b : Bool) (z : ℝ) :
    decideColor old z = b ↔ decision old b z := by
  rcases lt_trichotomy 0 z with hp | hz | hn
  · cases b <;> simp [decideColor, hp, decision, sign, ne_of_gt hp, not_lt.mpr hp.le]
  · subst z
    simp [decideColor, decision, eq_comm]
  · cases b <;> simp [decideColor, hn, not_lt.mpr hn.le, decision, sign, ne_of_lt hn]

def refinement (σ : State V n) : V → Universal.History (n + 2) := fun v =>
  append (σ.part v) (decideColor (last (σ.part v)) (imbalance (Fin.last n) (row σ.deg v)))

@[simp] theorem parent_refinement (σ : State V n) (v : V) :
    parent (refinement σ v) = σ.part v := by simp [refinement]

theorem refinement_actualState (G : SimpleGraph V) (c : V → Bool) :
    refinement (actualState G c n) = actualHistory G c (n + 2) := by
  funext v
  rw [actualHistory_succ]
  change append (actualHistory G c (n + 1) v) _ = append (actualHistory G c (n + 1) v) _
  congr 1
  apply (decideColor_eq_iff _ _ _).mpr
  change decision (last (actualHistory G c (n + 1) v)) _
    (imbalance (Fin.last n) (actualRow G c (n + 1) v))
  rw [last_actualHistory, imbalance_actualRow]
  change decision (coloringOnDayV G c (n + 1) v) (coloringOnDayV G c (n + 2) v) _
  rw [coloringOnDay_succ]
  exact (nextColoring_decision G _ v _).mp rfl

theorem refinement_fiber (σ : State V n) (v : V)
    (s : Universal.History (n + 1)) (b : Bool) :
    refinement σ v = append s b ↔ σ.part v = s ∧ row σ.deg v ∈ childEvent s b := by
  obtain ⟨G, c, rfl⟩ := attained σ
  rw [refinement_actualState]
  simpa only [mem_block, actualState_part, actualState_deg, row, actualRow] using child_block_event G c n v s b

theorem refinement_cover (σ : State V n) (v : V) :
    ∃ s : Universal.History (n + 2), v ∈ block (refinement σ) s :=
  ⟨refinement σ v, (mem_block _ _ _).mpr rfl⟩

theorem refinement_disjoint (σ : State V n) {s t : Universal.History (n + 2)} (hst : s ≠ t) :
    Disjoint (block (refinement σ) s) (block (refinement σ) t) := block_disjoint _ hst

theorem refinement_children_union (σ : State V n) (s : Universal.History (n + 1)) :
    block (refinement σ) (append s false) ∪ block (refinement σ) (append s true) =
      block σ.part s := by
  obtain ⟨G, c, rfl⟩ := attained σ
  rw [refinement_actualState]
  exact child_blocks_union G c (n + 1) s

def nextState (σ : State V n) (G : SimpleGraph V) (hG : degreeArray σ.part G = σ.deg) :
    State V (n + 1) where
  part := refinement σ
  deg := degreeArray (refinement σ) G
  realizable := ⟨G, rfl⟩
  history := by
    have hσ := reconstruction_state σ G (initial σ) hG (initial_compatible σ)
    have hp : refinement σ = actualHistory G (initial σ) (n + 2) := by
      conv_lhs => rw [← hσ, refinement_actualState]
    rw [hp]
    exact actualRow_historyEvent G (initial σ) (n + 1)

@[simp] theorem nextState_part (σ : State V n) (G : SimpleGraph V)
    (hG : degreeArray σ.part G = σ.deg) : (nextState σ G hG).part = refinement σ := rfl

@[simp] theorem nextState_deg (σ : State V n) (G : SimpleGraph V)
    (hG : degreeArray σ.part G = σ.deg) :
    (nextState σ G hG).deg = degreeArray (refinement σ) G := rfl

theorem nextState_eq_actual (σ : State V n) (G : SimpleGraph V) (c : V → Bool)
    (hG : degreeArray σ.part G = σ.deg) (hc : CompatibleInitial σ.part c) :
    nextState σ G hG = actualState G c (n + 1) := by
  have hσ := reconstruction_state σ G c hG hc
  have hp : refinement σ = actualHistory G c (n + 2) := by
    rw [← hσ, refinement_actualState]
  apply State.ext hp
  exact congrArg (fun π => degreeArray π G) hp

end MajorityDynamics.GraphProcess.FineState
