import MajorityDynamics.Probability.FixedDegreeSampling.Laws
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Literal quantities in LW17 Theorem 1.6 and LW20 Theorem 1.5 (bipartite case). -/
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology
namespace MajorityDynamics.Literature.EdgeProbabilities
open MajorityDynamics.Probability.FixedDegreeSampling

/-- The graph average degree `2m/n`. -/
def graphAverage (n m : ℕ) : ℝ := 2 * (m : ℝ) / n
/-- The graph density uses the exact `n-1` denominator. -/
def graphDensity (n m : ℕ) : ℝ := graphAverage n m / ((n : ℝ) - 1)

/-- The explicit main term in LW17 Theorem 1.6. -/
def graphApproximation (n m da db : ℕ) : ℝ :=
  let D := graphAverage n m
  (da : ℝ) * db / (D * ((n : ℝ) - 1)) *
    (1 - ((da : ℝ) - D) * ((db : ℝ) - D) / (D * ((n : ℝ) - 1 - D)))

/-- A valid additive corollary of the corrected full LW17 expansion on the entire
`d^α` degree domain: `O(D/n²)`. The smaller printed square-root error is not
valid on this domain. `LWAdapters.GraphError` derives this bound from all terms
of the corrected expansion; it suffices for the original paper window. -/
def graphErrorScale (n m : ℕ) : ℝ := graphAverage n m / (n : ℝ)^2

/-- Literal original source degree conditions, restricted to realizable degree families. -/
structure GraphConditions {V : Type*} [Fintype V]
    (n m : ℕ) (α : ℝ) (d : V → ℕ) : Prop where
  card_eq : Fintype.card V = n
  bounded : ∀ v, d v ≤ n - 1
  total : ∑ v, d v = 2 * m
  spread : ∀ v, |(d v : ℝ) - graphAverage n m| ≤ (graphAverage n m) ^ α
  realizable : (graphFamily d).Nonempty

/-- The bipartite side averages and density, with `ell` the left cardinality. -/
def leftAverage (ell m : ℕ) : ℝ := (m : ℝ) / ell
def rightAverage (n m : ℕ) : ℝ := (m : ℝ) / n
def bipartiteDensity (ell n m : ℕ) : ℝ := (m : ℝ) / ((ell : ℝ) * n)

/-- Source variance: empirical variance with divisor equal to the side cardinality. -/
def degreeVariance {V : Type*} [Fintype V] (d : V → ℕ) (average : ℝ) : ℝ :=
  (∑ v, ((d v : ℝ) - average) ^ 2) / Fintype.card V

/-- Full bracket in LW20 Theorem 1.5 with `delta_di=0`, excluding only its O term. -/
def bipartiteBracket {L R : Type*} [Fintype L] [Fintype R]
    (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ) (i : L) (j : R) : ℝ :=
  let s := leftAverage ell m
  let t := rightAverage n m
  1 - ((a i : ℝ) - s) * ((b j : ℝ) - t) / ((m : ℝ) - t * s) +
    ((a i : ℝ) - s) * degreeVariance b t / (t * s * ((ell : ℝ) - t)) +
    ((b j : ℝ) - t) * degreeVariance a s / (t * s * ((n : ℝ) - s))

/-- The prefactor outside the entire bracket. -/
def bipartitePrefactor (m ai bj : ℕ) : ℝ := (ai : ℝ) * bj / m

def bipartiteApproximation {L R : Type*} [Fintype L] [Fintype R]
    (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ) (i : L) (j : R) : ℝ :=
  bipartitePrefactor m (a i) (b j) * bipartiteBracket ell n m a b i j

/-- The O scale INSIDE the bracket; the source conclusion also multiplies by the prefactor. -/
def bipartiteErrorScale (ell n m : ℕ) (α : ℝ) : ℝ :=
  (min (leftAverage ell m) (rightAverage n m)) ^ (4 * α - 4) *
    (m : ℝ) / ((n : ℝ) * ell)

structure BipartiteConditions {L R : Type*} [Fintype L] [Fintype R]
    (ell n m : ℕ) (α : ℝ) (a : L → ℕ) (b : R → ℕ) : Prop where
  card_left : Fintype.card L = ell
  card_right : Fintype.card R = n
  bounded_left : ∀ i, a i ≤ n
  bounded_right : ∀ j, b j ≤ ell
  total_left : ∑ i, a i = m
  total_right : ∑ j, b j = m
  spread_left : ∀ i, |(a i : ℝ) - leftAverage ell m| ≤ (leftAverage ell m) ^ α
  spread_right : ∀ j, |(b j : ℝ) - rightAverage n m| ≤ (rightAverage n m) ^ α
  realizable : (bipartiteFamily a b).Nonempty

end MajorityDynamics.Literature.EdgeProbabilities
