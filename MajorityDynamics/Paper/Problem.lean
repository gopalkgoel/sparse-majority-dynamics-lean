import MajorityDynamics.Probability.RandomGraph.Basic
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# The problem and the main theorem statement

This file gives concrete meanings to the objects in `thm:succinct_main_result`
of `latest/main.tex`. It states a proposition, not a proof of that proposition.

Vertices are `Fin N`; arbitrary finite vertex sets can later be transported
along a bijection. As in the paper's history encoding, `false` represents
opinion `+1` and `true` represents opinion `-1`. Day 1 is the initial coloring.
The random graph law is Mathlib's proved Erdős–Rényi construction.

The epsilon–N₀ quantifiers make the paper's uniform `o(1)` explicit: N₀ may
depend on θ, T, and ε, but not on p, τ, or the deterministic initial coloring.
-/

noncomputable section

open scoped BigOperators

namespace MajorityDynamics.Paper

abbrev Coloring (N : ℕ) := Fin N → Bool

/-- The integer opinion encoded by a bit: `false = +1`, `true = -1`. -/
def opinion (b : Bool) : ℤ := if b then -1 else 1

/-- Sum of the current opinions of the neighbors of a vertex. -/
def neighborSum {N : ℕ} (G : Graph N) (c : Coloring N) (v : Fin N) : ℤ := by
  classical
  exact ∑ w : Fin N, if G.Adj v w then opinion (c w) else 0

/-- Simultaneous majority update, retaining the current opinion at ties. -/
def nextColoring {N : ℕ} (G : Graph N) (c : Coloring N) : Coloring N :=
  fun v => if 0 < neighborSum G c v then false
    else if neighborSum G c v < 0 then true else c v

/-- The paper's day convention: day 1 is the initial coloring.
Day 0 is also defined to be the initial coloring, and is not used by the paper. -/
def coloringOnDay {N : ℕ} (G : Graph N) (c : Coloring N) (day : ℕ) : Coloring N :=
  (nextColoring G)^[day - 1] c

@[simp] theorem coloringOnDay_one {N : ℕ} (G : Graph N) (c : Coloring N) :
    coloringOnDay G c 1 = c := by
  simp [coloringOnDay]

theorem nextColoring_of_tie {N : ℕ} (G : Graph N) (c : Coloring N) (v : Fin N)
    (h : neighborSum G c v = 0) : nextColoring G c v = c v := by
  simp [nextColoring, h]

/-- Number of vertices holding opinion `+1`. -/
def plusCount {N : ℕ} (c : Coloring N) : ℕ :=
  (Finset.univ.filter fun v => c v = false).card

/-- The signed lead (#plus minus #minus), viewed as a real number. -/
def lead {N : ℕ} (c : Coloring N) : ℝ :=
  2 * (plusCount c : ℝ) - (N : ℝ)

/-- The last day of the expansion phase (`cor:lead`). -/
def expansionDay (θ : ℝ) : ℕ :=
  ⌊1 / (1 - θ)⌋₊ + 1

/-- The day of unanimity in `thm:succinct_main_result`:
`2 * floor (1 / (1 - θ)) + 3`. -/
def convergenceDay (θ : ℝ) : ℕ :=
  2 * expansionDay θ + 1

/-- The open density interval from the main theorem. A unit-interval parameter
makes the random graph law well-defined even outside the theorem's range. -/
def densityRange (θ T : ℝ) (N : ℕ) (p : unitInterval) : Prop :=
  T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) ∧ (p : ℝ) < T * (N : ℝ) ^ (-θ)

/-- The exact initial count, including both floors in the paper's statement.
Under the main theorem hypotheses τ is positive, so natural floors agree with
the paper's integer floors. -/
def initialBias (N : ℕ) (τ : ℝ) (c : Coloring N) : Prop :=
  plusCount c = N / 2 + ⌊τ * Real.sqrt (N : ℝ)⌋₊

/-- Success means every vertex is `+1` on the stated day. -/
def successEvent {N : ℕ} (θ : ℝ) (c : Coloring N) : Set (Graph N) :=
  {G | ∀ v, coloringOnDay G c (convergenceDay θ) v = false}

/-- `thm:succinct_main_result` on the canonical vertex set `Fin N`.
The failure-probability bound is equivalent to success probability at least
`1 - ε`, since `graphLaw` is a probability measure. This definition is the
target to prove; defining it does not prove it. -/
def MainTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
        densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
          graphLaw N p (successEvent θ c)ᶜ ≤ ENNReal.ofReal ε

end MajorityDynamics.Paper
