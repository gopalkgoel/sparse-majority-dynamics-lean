import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

set_option autoImplicit true
set_option linter.unusedSectionVars false

/-!
# Majority dynamics on `G(n,p)`: model and statement of Theorem 1.1

Fountoulakis–Kang–Makai, *Resolution of a conjecture on majority dynamics:
rapid stabilisation in dense random graphs* (arXiv:1910.05820), Theorem 1.1.

The sample space is `Fin n ⊕ Edge n → Bool`: coordinate `inl v` is the initial
state of vertex `v` (`true` = `+1`, `false` = `-1`, each uniform), coordinate
`inr e` tells whether the potential edge `e` is present (probability `p`).
All coordinates are independent (Bernoulli product measure `wt`).
-/

namespace MD

open Finset

/-- Potential edges of the complete graph on `Fin n`. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- Sample points: initial states and edge indicators. -/
abbrev Ω (n : ℕ) := Fin n ⊕ Edge n → Bool

/-- The coordinate carrying the edge `uw` (for `u ≠ w`); `inl u` if `u = w` (never an edge). -/
def edge {n : ℕ} (u w : Fin n) : Fin n ⊕ Edge n :=
  if h : u = w then Sum.inl u else Sum.inr ⟨s(u, w), by simpa [Sym2.mk_isDiag_iff] using h⟩

/-- `u` and `w` are adjacent in the graph encoded by `x`. -/
def adj {n : ℕ} (x : Ω n) (u w : Fin n) : Prop := u ≠ w ∧ x (edge u w) = true

instance {n : ℕ} (x : Ω n) (u w : Fin n) : Decidable (adj x u w) := by
  unfold adj; infer_instance

/-- `±1` value of a state. -/
def val (b : Bool) : ℤ := if b then 1 else -1

/-- Sum of the states of the neighbours of `u`. -/
def nsum {n : ℕ} (x : Ω n) (s : Fin n → Bool) (u : Fin n) : ℤ :=
  ∑ w, if adj x u w then val (s w) else 0

/-- One round of majority dynamics: adopt the majority state of the neighbours,
keep the current state in case of a tie. -/
def step {n : ℕ} (x : Ω n) (s : Fin n → Bool) (u : Fin n) : Bool :=
  if 0 < nsum x s u then true else if nsum x s u < 0 then false else s u

/-- Initial states encoded in the sample point. -/
def init {n : ℕ} (x : Ω n) (v : Fin n) : Bool := x (Sum.inl v)

/-- State after `t` rounds. -/
def S {n : ℕ} (x : Ω n) : ℕ → Fin n → Bool
  | 0 => init x
  | t + 1 => step x (S x t)

/-- `∑_{v} S₀(v)`. -/
def tot {n : ℕ} (x : Ω n) : ℤ := ∑ v, val (init x v)

/-- After four rounds every vertex has state `sgn (∑ S₀(v))`. Since `val` is `±1`, this forces
`∑ S₀(v) ≠ 0`: a tied initial vote counts as failure. -/
def Good {n : ℕ} (x : Ω n) : Prop := ∀ v, val (S x 4 v) = Int.sign (tot x)

/-- Success probabilities of the coordinates: `1/2` for states, `p` for edges. -/
noncomputable def q (n : ℕ) (p : ℝ) : Fin n ⊕ Edge n → ℝ := Sum.elim (fun _ => 1 / 2) (fun _ => p)

section Prob

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bernoulli product weight with success probabilities `q`. -/
noncomputable def wt (q : ι → ℝ) (x : ι → Bool) : ℝ := ∏ i, if x i then q i else 1 - q i

/-- Expectation under the product measure. -/
noncomputable def E (q : ι → ℝ) (F : (ι → Bool) → ℝ) : ℝ := ∑ x, wt q x * F x

open scoped Classical in
/-- Probability of an event. -/
noncomputable def Pr (q : ι → ℝ) (A : (ι → Bool) → Prop) : ℝ :=
  E q fun x => if A x then 1 else 0

end Prob

/-- **Theorem 1.1** (Fountoulakis–Kang–Makai). For every `0 < ε ≤ 1` there are `λ > 0` and
`n₀` such that for all `n > n₀` and all `λ n^{-1/2} ≤ p ≤ 1`, with probability at least
`1 - ε` over the random graph `G(n,p)` and the uniformly random initial states, after four
rounds of majority dynamics all vertices have state `sgn (∑_v S₀(v))`. -/
def Theorem11 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ lam : ℝ, 0 < lam ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
    ∀ p : ℝ, lam / Real.sqrt n ≤ p → p ≤ 1 → 1 - ε ≤ Pr (q n p) (Good (n := n))

end MD
