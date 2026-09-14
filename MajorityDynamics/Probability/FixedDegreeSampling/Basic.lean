import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.UniformOn
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! Exact labeled degree fibers and removal data for `lem:nice_deg_bulk`. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.Probability.FixedDegreeSampling
open scoped Classical ENNReal
variable {V : Type*} [Fintype V]

instance graphMeasurableSingleton : MeasurableSingletonClass (SimpleGraph V) :=
  ⟨fun G => by
    convert (measurableSet_singleton G.edgeSet).preimage SimpleGraph.measurable_edgeSet using 1
    ext H
    simp⟩

/-- The actual family of labeled simple graphs with the prescribed degrees. -/
def graphFamily (d : V → ℕ) : Set (SimpleGraph V) := {G | ∀ u, G.degree u = d u}

def graphCount (d : V → ℕ) : ℕ := (graphFamily d).ncard

/-- Zero on an empty fiber, a normalized uniform measure on a nonempty fiber. -/
def fixedDegreeLaw (d : V → ℕ) : Measure (SimpleGraph V) := uniformOn (graphFamily d)

abbrev Remaining (v : V) := {u : V // u ≠ v}

def graphAdmissible (d : V → ℕ) (v : V) (R : Finset V) : Prop :=
  v ∉ R ∧ R.card = d v ∧ ∀ u ∈ R, 1 ≤ d u

def residualDegree (d : V → ℕ) (v : V) (R : Finset V) (u : Remaining v) : ℕ :=
  d u - if u.val ∈ R then 1 else 0

def graphNeighborhoodFiber (d : V → ℕ) (v : V) (R : Finset V) :=
  {G : SimpleGraph V // G ∈ graphFamily d ∧ G.neighborFinset v = R}

/-- Exact finite-probability target for the opening removal step of C.4. -/
def GraphNeighborhoodProbabilityTheorem : Prop :=
  ∀ (d : V → ℕ) (v : V) (S : Finset V), graphAdmissible d v S →
    fixedDegreeLaw d {G | G.neighborFinset v = S} =
      (graphCount (residualDegree d v S) : ℝ≥0∞) / graphCount d

/-- Conditioning uses the actual independent-edge graph law, with proved positivity. -/
def GraphConditionalLawTheorem : Prop :=
  ∀ (d : V → ℕ), (graphFamily d).Nonempty →
    ∀ (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
      0 < SimpleGraph.binomialRandom V p (graphFamily d) ∧
      cond (SimpleGraph.binomialRandom V p) (graphFamily d) = fixedDegreeLaw d

end MajorityDynamics.Probability.FixedDegreeSampling
