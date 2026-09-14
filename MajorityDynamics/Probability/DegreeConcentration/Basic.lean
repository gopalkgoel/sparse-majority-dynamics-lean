import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Lemma A.10 (`lem:gamma_bound`): truncated degree-square concentration — contract

This module fixes the concrete probability models, the degree statistics, the
exact events, and the target propositions for Lemma A.10 of `latest/main.tex`.
Nothing here is an axiom; the proofs are in the sibling modules and assembled
in `Main.lean`.

## Models

* `graphLaw n p` is Mathlib's binomial random graph `G(n,p)` on `Fin n`,
  i.e. `SimpleGraph.binomialRandom (Fin n) p`; each of the `n.choose 2` possible
  edges is present independently with probability `p`.
* `bipartiteLaw ℓ n p` is the law `G(ℓ,n,p)`: the random set of cross edges
  `E ⊆ Fin ℓ × Fin n` with every pair `(i,j)` present independently with
  probability `p`. This is `setBer(univ, p)`, the same product-of-Bernoulli
  construction that Mathlib uses for `binomialRandom`. `bipartiteGraph E` is
  the simple graph on `Fin ℓ ⊕ Fin n` whose edges are exactly the cross edges
  of `E`; `Bipartite.lean` proves that it is injective, has no same-side edges,
  and that its vertex degrees are the side degrees `leftDegree`/`rightDegree`.

## Centers (all three kept distinct, as in the manuscript)

* the truncation center is `p * n` (graph) and `p * n`, `p * ℓ` (bipartite sides);
* the empirical center is the random mean `graphDegreeMean`, `leftDegreeMean`,
  `rightDegreeMean`;
* the actual binomial mean of a graph degree is `p * (n - 1)`, used only inside
  the proof (`Cut.lean`, `Graph.lean`).

## Events

* `graphBad C p` is `{∑ᵢ (dᵢ - d̄)² ≥ C p n²} ∩ {∀ i, |dᵢ - p n| ≤ p n}`.
* `bipartiteBad C p` is
  `({∑ᵢ (sᵢ - s̄)² ≥ C p ℓ n} ∪ {∑ⱼ (tⱼ - t̄)² ≥ C p ℓ n}) ∩ 𝒦_{ℓ,n}` with
  `𝒦_{ℓ,n} = {∀ i, |sᵢ - p n| ≤ p n} ∩ {∀ j, |tⱼ - p ℓ| ≤ p n}`; note the
  right-side tolerance is `p n`, not `p ℓ`, and the probability is the
  unconditional probability of the intersection.

## Targets

`GraphDegreeConcentrationTheorem`, `BipartiteDegreeConcentrationTheorem`, the
common-constant `DegreeConcentrationTheorem`, and the literal real-density
`RealDegreeConcentrationTheorem`. In all of them `C` and `n₀` are chosen after
`θ, T, K` only and before `n`, `p`, `ℓ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.DegreeConcentration

/-! ### The graph model -/

abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

/-- The binomial random graph `G(n,p)` on `Fin n` (Mathlib's construction). -/
def graphLaw (n : ℕ) (p : I) : Measure (Graph n) :=
  SimpleGraph.binomialRandom (Fin n) p

instance graphLaw_isProbabilityMeasure (n : ℕ) (p : I) :
    IsProbabilityMeasure (graphLaw n p) := by
  unfold graphLaw
  infer_instance

/-- The degree `d_i` of vertex `i` in `G`, as a real number. -/
def graphDegree {n : ℕ} (G : Graph n) (i : Fin n) : ℝ := by
  classical
  exact (G.degree i : ℝ)

/-- The empirical mean degree `d̄ = (1/n) ∑ᵢ dᵢ`. -/
def graphDegreeMean {n : ℕ} (G : Graph n) : ℝ :=
  (∑ i : Fin n, graphDegree G i) / (n : ℝ)

/-- The empirical degree-square sum `∑ᵢ (dᵢ - d̄)²`. -/
def graphSquareSum {n : ℕ} (G : Graph n) : ℝ :=
  ∑ i : Fin n, (graphDegree G i - graphDegreeMean G) ^ 2

/-- The graph truncation event `{∀ i, |dᵢ - p n| ≤ p n}`. -/
def graphTruncation (n : ℕ) (p : ℝ) : Set (Graph n) :=
  {G | ∀ i, |graphDegree G i - p * n| ≤ p * n}

/-- The event `{∑ᵢ (dᵢ - d̄)² ≥ C p n²}`. -/
def graphSpread (n : ℕ) (C p : ℝ) : Set (Graph n) :=
  {G | C * p * (n : ℝ) ^ 2 ≤ graphSquareSum G}

/-- The exact event of Lemma A.10(i). -/
def graphBad (n : ℕ) (C p : ℝ) : Set (Graph n) :=
  graphSpread n C p ∩ graphTruncation n p

/-! ### The bipartite model -/

/-- A realisation of `G(ℓ,n,p)`: the set of present cross edges. -/
abbrev CrossEdges (ℓ n : ℕ) := Set (Fin ℓ × Fin n)

/-- The bipartite random graph law `G(ℓ,n,p)`: every cross edge `(i,j)` is present
independently with probability `p`, and there are no other edges. -/
def bipartiteLaw (ℓ n : ℕ) (p : I) : Measure (CrossEdges ℓ n) :=
  setBer((Set.univ : Set (Fin ℓ × Fin n)), p)

instance bipartiteLaw_isProbabilityMeasure (ℓ n : ℕ) (p : I) :
    IsProbabilityMeasure (bipartiteLaw ℓ n p) := by
  unfold bipartiteLaw
  infer_instance

/-- The simple graph on `Fin ℓ ⊕ Fin n` whose edges are the cross edges of `E`. -/
def bipartiteGraph {ℓ n : ℕ} (E : CrossEdges ℓ n) : SimpleGraph (Fin ℓ ⊕ Fin n) :=
  SimpleGraph.fromEdgeSet ((fun x : Fin ℓ × Fin n ↦ s(Sum.inl x.1, Sum.inr x.2)) '' E)

/-- The law of the simple bipartite graph `G(ℓ,n,p)` on `Fin ℓ ⊕ Fin n`. -/
def bipartiteGraphLaw (ℓ n : ℕ) (p : I) : Measure (SimpleGraph (Fin ℓ ⊕ Fin n)) :=
  (bipartiteLaw ℓ n p).map bipartiteGraph

/-- The left degree `sᵢ = #{j : (i,j) ∈ E}`, as a real number. -/
def leftDegree {ℓ n : ℕ} (E : CrossEdges ℓ n) (i : Fin ℓ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).card : ℝ)

/-- The right degree `tⱼ = #{i : (i,j) ∈ E}`, as a real number. -/
def rightDegree {ℓ n : ℕ} (E : CrossEdges ℓ n) (j : Fin n) : ℝ := by
  classical
  exact ((Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).card : ℝ)

/-- The empirical left mean `s̄`. -/
def leftDegreeMean {ℓ n : ℕ} (E : CrossEdges ℓ n) : ℝ :=
  (∑ i : Fin ℓ, leftDegree E i) / (ℓ : ℝ)

/-- The empirical right mean `t̄`. -/
def rightDegreeMean {ℓ n : ℕ} (E : CrossEdges ℓ n) : ℝ :=
  (∑ j : Fin n, rightDegree E j) / (n : ℝ)

/-- `∑ᵢ (sᵢ - s̄)²`. -/
def leftSquareSum {ℓ n : ℕ} (E : CrossEdges ℓ n) : ℝ :=
  ∑ i : Fin ℓ, (leftDegree E i - leftDegreeMean E) ^ 2

/-- `∑ⱼ (tⱼ - t̄)²`. -/
def rightSquareSum {ℓ n : ℕ} (E : CrossEdges ℓ n) : ℝ :=
  ∑ j : Fin n, (rightDegree E j - rightDegreeMean E) ^ 2

/-- The joint truncation event `𝒦_{ℓ,n}`; both tolerances are `p n`. -/
def bipartiteTruncation (ℓ n : ℕ) (p : ℝ) : Set (CrossEdges ℓ n) :=
  {E | (∀ i, |leftDegree E i - p * n| ≤ p * n) ∧ ∀ j, |rightDegree E j - p * ℓ| ≤ p * n}

/-- The union of the two side failures at threshold `C p ℓ n`. -/
def bipartiteSpread (ℓ n : ℕ) (C p : ℝ) : Set (CrossEdges ℓ n) :=
  {E | C * p * ℓ * n ≤ leftSquareSum E ∨ C * p * ℓ * n ≤ rightSquareSum E}

/-- The exact event of Lemma A.10(ii). -/
def bipartiteBad (ℓ n : ℕ) (C p : ℝ) : Set (CrossEdges ℓ n) :=
  bipartiteSpread ℓ n C p ∩ bipartiteTruncation ℓ n p

open Classical in
/-- The event of Lemma A.10(ii) written for a simple graph on `Fin ℓ ⊕ Fin n` through its
vertex degrees. -/
def bipartiteGraphBad (ℓ n : ℕ) (C p : ℝ) : Set (SimpleGraph (Fin ℓ ⊕ Fin n)) :=
  {G | (C * p * ℓ * n ≤ ∑ i : Fin ℓ, ((G.degree (Sum.inl i) : ℝ) -
          (∑ i : Fin ℓ, (G.degree (Sum.inl i) : ℝ)) / ℓ) ^ 2 ∨
        C * p * ℓ * n ≤ ∑ j : Fin n, ((G.degree (Sum.inr j) : ℝ) -
          (∑ j : Fin n, (G.degree (Sum.inr j) : ℝ)) / n) ^ 2) ∧
      (∀ i : Fin ℓ, |(G.degree (Sum.inl i) : ℝ) - p * n| ≤ p * n) ∧
      ∀ j : Fin n, |(G.degree (Sum.inr j) : ℝ) - p * ℓ| ≤ p * n}

/-! ### Parameter ranges -/

/-- The open density interval `p ∈ (T⁻¹ n^{-θ}, T n^{-θ})`. -/
def densityRange (θ T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ)

/-- The bipartite size interval `ℓ ∈ [T⁻¹ n, T n]`, for an integer `ℓ`. -/
def sizeRange (T : ℝ) (n ℓ : ℕ) : Prop :=
  T⁻¹ * (n : ℝ) ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T * (n : ℝ)

/-- The failure probability `e^{-K n}` as an extended nonnegative real. -/
def failureBound (K : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-K * (n : ℝ)))

/-! ### Targets -/

/-- Lemma A.10(i): for every `θ ∈ (1/2,1)`, `T > 1`, `K > 0` there are `C > 0` and `n₀`
such that for all `n ≥ n₀` and admissible `p`,
`P[∑ᵢ (dᵢ - d̄)² ≥ C p n² ∧ ∀ i, |dᵢ - p n| ≤ p n] ≤ e^{-K n}` under `G(n,p)`. -/
def GraphDegreeConcentrationTheorem : Prop :=
  ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ p : I, densityRange θ T n p →
        graphLaw n p (graphBad n C p) ≤ failureBound K n

/-- Lemma A.10(ii): with the same quantifier order, for every integer `ℓ ∈ [T⁻¹ n, T n]`,
`P[(∑ᵢ (sᵢ - s̄)² ≥ C p ℓ n ∨ ∑ⱼ (tⱼ - t̄)² ≥ C p ℓ n) ∧ 𝒦_{ℓ,n}] ≤ e^{-K n}`
under `G(ℓ,n,p)`. -/
def BipartiteDegreeConcentrationTheorem : Prop :=
  ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ p : I, densityRange θ T n p →
        ∀ ℓ : ℕ, sizeRange T n ℓ →
          bipartiteLaw ℓ n p (bipartiteBad ℓ n C p) ≤ failureBound K n

/-- Lemma A.10 with one constant and one threshold covering both conclusions. -/
def DegreeConcentrationTheorem : Prop :=
  ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ p : I, densityRange θ T n p →
        graphLaw n p (graphBad n C p) ≤ failureBound K n ∧
        ∀ ℓ : ℕ, sizeRange T n ℓ →
          bipartiteLaw ℓ n p (bipartiteBad ℓ n C p) ≤ failureBound K n

/-- The literal real-density form: `p` is a real number in the stated open interval,
and the endpoint itself supplies `0 < p < 1` (needed to form the probability
parameter) from `n ≥ n₀`, rather than assuming it. -/
def RealDegreeConcentrationTheorem : Prop :=
  ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ p : ℝ, T⁻¹ * (n : ℝ) ^ (-θ) < p → p < T * (n : ℝ) ^ (-θ) →
        ∃ hp : 0 < p ∧ p < 1,
          graphLaw n ⟨p, hp.1.le, hp.2.le⟩ (graphBad n C p) ≤ failureBound K n ∧
          ∀ ℓ : ℕ, sizeRange T n ℓ →
            bipartiteLaw ℓ n ⟨p, hp.1.le, hp.2.le⟩ (bipartiteBad ℓ n C p) ≤ failureBound K n

/-- Lemma A.10(ii) stated for the simple bipartite graph law on `Fin ℓ ⊕ Fin n`, with the
event written through `SimpleGraph.degree`. -/
def BipartiteGraphDegreeConcentrationTheorem : Prop :=
  ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ p : I, densityRange θ T n p →
        ∀ ℓ : ℕ, sizeRange T n ℓ →
          bipartiteGraphLaw ℓ n p (bipartiteGraphBad ℓ n C p) ≤ failureBound K n

end MajorityDynamics.Probability.DegreeConcentration
