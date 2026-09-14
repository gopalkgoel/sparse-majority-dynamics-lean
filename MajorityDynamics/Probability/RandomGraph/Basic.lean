import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Analysis.Real.Sqrt

/-!
# Shared random-graph vocabulary

Only the actual random-graph law and ordered-edge discrepancy predicate live here.
There are no majority updates, paper targets, or mathematical axioms. The existing
`MajorityDynamics.Paper` names are retained for source compatibility; their location
here makes the dependency direction explicit. Literature proofs can use these
unchanged definitions without importing any module under `Paper/`.
-/
noncomputable section
namespace MajorityDynamics.Paper

abbrev Graph (N : ℕ) := SimpleGraph (Fin N)

/-- The Erdős–Rényi probability measure; its normalization and independence
construction come from Mathlib, rather than an unproved assumption here. -/
def graphLaw (N : ℕ) (p : unitInterval) : MeasureTheory.Measure (Graph N) :=
  SimpleGraph.binomialRandom (Fin N) p

instance graphLaw_isProbabilityMeasure (N : ℕ) (p : unitInterval) :
    MeasureTheory.IsProbabilityMeasure (graphLaw N p) := by
  unfold graphLaw
  infer_instance

/-- Ordered adjacent pairs in `U × W`. Overlapping sets are allowed, so an
edge internal to `U = W` is counted twice, as in `def:jumbled`. -/
def orderedEdgeCount {N : ℕ} (G : Graph N) (U W : Finset (Fin N)) : ℕ := by
  classical
  exact ((U ×ˢ W).filter fun vw => G.Adj vw.1 vw.2).card

/-- The ordered-edge form of jumbledness in `def:jumbled`, including
pairs of overlapping vertex sets. -/
def Jumbled {N : ℕ} (G : Graph N) (p : unitInterval) (β : ℝ) : Prop :=
  ∀ U W : Finset (Fin N),
    |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * (U.card : ℝ) * (W.card : ℝ)| ≤
      β * Real.sqrt ((U.card : ℝ) * (W.card : ℝ))

end MajorityDynamics.Paper
