import MajorityDynamics.Literature.FKMFormal.Defs

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-! Sanity checks of the definitions on tiny instances. -/

namespace MD

instance {n : ℕ} (x : Ω n) : Decidable (Good x) := by unfold Good; infer_instance

-- `edge` is symmetric and hits `inr` exactly off the diagonal.
example : edge (0 : Fin 3) 1 = edge 1 0 := by native_decide
example : edge (0 : Fin 3) 0 = Sum.inl 0 := by native_decide
example : edge (0 : Fin 3) 1 ≠ edge 0 2 := by native_decide

-- Path 0 - 1 - 2 with states (+,+,-): vertex 1 sees +1 - 1 = 0 and keeps its state,
-- vertex 2 adopts +1, vertex 0 keeps +1.
def pathX : Ω 3 := fun i =>
  i = edge 0 1 || i = edge 1 2 || i = Sum.inl 0 || i = Sum.inl 1

example : adj pathX 0 1 ∧ adj pathX 2 1 ∧ ¬ adj pathX 0 2 := by native_decide
example : nsum pathX (init pathX) 1 = 0 := by native_decide
example : S pathX 1 = ![true, true, true] := by native_decide
example : tot pathX = 1 ∧ Good pathX := by native_decide

-- Triangle with states (+,-,-): the majority `-1` wins in one round.
def triX : Ω 3 := fun i =>
  i = edge 0 1 || i = edge 1 2 || i = edge 0 2 || i = Sum.inl 0

example : S triX 1 = ![false, false, false] := by native_decide
example : tot triX = -1 ∧ Good triX := by native_decide

-- Empty graph, states (+,-): nothing moves, and `tot = 0` so `Good` fails (sign 0).
def emptyX : Ω 2 := fun i => i = Sum.inl 0

example : S emptyX 4 = ![true, false] ∧ tot emptyX = 0 ∧ ¬ Good emptyX := by native_decide

-- Product weights of a two-coordinate space.
example (a b : ℝ) : wt (![a, b] : Fin 2 → ℝ) ![true, false] = a * (1 - b) := by
  simp [wt, Fin.prod_univ_two]

end MD
