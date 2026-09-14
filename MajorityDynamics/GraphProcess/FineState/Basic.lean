import MajorityDynamics.GraphProcess.History.Main

/-! Literal graph-realizable fine states, with no dynamics stored as fields. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.FineState
open Universal History
variable {V : Type*} [Fintype V]

def row {k : ℕ} (d : V → Universal.History k → ℤ) (v : V) : Row k :=
  WithLp.toLp 2 (fun t => (d v t : ℝ))

omit [Fintype V] in
@[simp] theorem row_apply {k : ℕ} (d : V → Universal.History k → ℤ) (v : V)
    (t : Universal.History k) : row d v t = (d v t : ℝ) := rfl

def Realizable {k : ℕ} (π : V → Universal.History k)
    (d : V → Universal.History k → ℤ) : Prop := ∃ G : SimpleGraph V, degreeArray π G = d

structure State (V : Type*) [Fintype V] (n : ℕ) where
  part : V → Universal.History (n + 1)
  deg : V → Universal.History (n + 1) → ℤ
  realizable : Realizable part deg
  history : ∀ v, row deg v ∈ historyEvent (part v)

@[ext] theorem State.ext {n : ℕ} {σ τ : State V n}
    (hp : σ.part = τ.part) (hd : σ.deg = τ.deg) : σ = τ := by
  cases σ; cases τ; cases hp; cases hd; rfl

def CompatibleInitial {n : ℕ} (π : V → Universal.History (n + 1))
    (c : V → Bool) : Prop := ∀ v, c v = bits (n + 1) (π v) 0

def initial {n : ℕ} (σ : State V n) : V → Bool := fun v => bits (n + 1) (σ.part v) 0

theorem initial_compatible {n : ℕ} (σ : State V n) : CompatibleInitial σ.part (initial σ) :=
  fun _ => rfl

def actualState (G : SimpleGraph V) (c : V → Bool) (n : ℕ) : State V n where
  part := actualHistory G c (n + 1)
  deg := degreeArray (actualHistory G c (n + 1)) G
  realizable := ⟨G, rfl⟩
  history := actualRow_historyEvent G c n

@[simp] theorem actualState_part (G : SimpleGraph V) (c : V → Bool) (n : ℕ) :
    (actualState G c n).part = actualHistory G c (n + 1) := rfl
@[simp] theorem actualState_deg (G : SimpleGraph V) (c : V → Bool) (n : ℕ) :
    (actualState G c n).deg = degreeArray (actualHistory G c (n + 1)) G := rfl

end MajorityDynamics.GraphProcess.FineState
