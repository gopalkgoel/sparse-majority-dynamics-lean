import MajorityDynamics.Probability.DegreeConcentration.Main

/-!
# Lemma A.10 endpoint checks

Exact type checks of the public endpoints, independently written expansions of the
statements (so that the actual laws, events, quantifier order and conclusions are visible
here, not only through the definitions of `Basic.lean`), and guarded axiom audits.
-/

open MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.DegreeConcentration

example : GraphDegreeConcentrationTheorem := graph_degree_concentration
example : BipartiteDegreeConcentrationTheorem := bipartite_degree_concentration
example : DegreeConcentrationTheorem := degree_concentration
example : BipartiteGraphDegreeConcentrationTheorem := bipartite_graph_degree_concentration
example : RealDegreeConcentrationTheorem := degree_concentration_real

open Classical in
/-- The common-constant statement, expanded: Mathlib's `G(n,p)` law and the cross-edge
product-Bernoulli law `G(ℓ,n,p)`, the empirical variances of the degree sequences, the exact
truncation events with center `p n` (graph), `p n` and `p ℓ` (bipartite sides) and tolerance
`p n` throughout, the union of the two side failures, and the bound `e^{-K n}`. -/
example :
    ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ p : I, T⁻¹ * (n : ℝ) ^ (-θ) < (p : ℝ) → (p : ℝ) < T * (n : ℝ) ^ (-θ) →
      SimpleGraph.binomialRandom (Fin n) p
        {G | C * p * (n : ℝ) ^ 2 ≤
              ∑ i, ((G.degree i : ℝ) - (∑ i, (G.degree i : ℝ)) / n) ^ 2 ∧
            ∀ i, |(G.degree i : ℝ) - p * n| ≤ p * n} ≤
          ENNReal.ofReal (Real.exp (-K * n)) ∧
      ∀ ℓ : ℕ, T⁻¹ * (n : ℝ) ≤ ℓ → (ℓ : ℝ) ≤ T * n →
        setBer((Set.univ : Set (Fin ℓ × Fin n)), p)
          {E | (C * p * ℓ * n ≤
                  ∑ i : Fin ℓ, (((Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).card : ℝ) -
                    (∑ i : Fin ℓ, ((Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).card : ℝ)) /
                      ℓ) ^ 2 ∨
                C * p * ℓ * n ≤
                  ∑ j : Fin n, (((Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).card : ℝ) -
                    (∑ j : Fin n, ((Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).card : ℝ)) /
                      n) ^ 2) ∧
              (∀ i : Fin ℓ,
                |((Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).card : ℝ) - p * n| ≤ p * n) ∧
              ∀ j : Fin n,
                |((Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).card : ℝ) - p * ℓ| ≤ p * n} ≤
          ENNReal.ofReal (Real.exp (-K * n)) := by
  intro θ T K hθ hθ1 hT hK
  obtain ⟨C, hC, n₀, h⟩ := degree_concentration θ T K hθ hθ1 hT hK
  refine ⟨C, hC, n₀, fun n hn p hp1 hp2 ↦ ?_⟩
  obtain ⟨hgraph, hbip⟩ := h n hn p ⟨hp1, hp2⟩
  exact ⟨hgraph, fun ℓ hℓ1 hℓ2 ↦ hbip ℓ ⟨hℓ1, hℓ2⟩⟩

open Classical in
/-- The bipartite conclusion for the simple-graph law on `Fin ℓ ⊕ Fin n`, expanded: the
pushforward of `G(ℓ,n,p)` under `E ↦ fromEdgeSet {s(inl i, inr j) : (i,j) ∈ E}`, with the
event written through `SimpleGraph.degree`. -/
example :
    ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ p : I, T⁻¹ * (n : ℝ) ^ (-θ) < (p : ℝ) → (p : ℝ) < T * (n : ℝ) ^ (-θ) →
      ∀ ℓ : ℕ, T⁻¹ * (n : ℝ) ≤ ℓ → (ℓ : ℝ) ≤ T * n →
        (setBer((Set.univ : Set (Fin ℓ × Fin n)), p)).map
            (fun E ↦ SimpleGraph.fromEdgeSet
              ((fun x : Fin ℓ × Fin n ↦ s(Sum.inl x.1, Sum.inr x.2)) '' E))
          {G | (C * p * ℓ * n ≤ ∑ i : Fin ℓ, ((G.degree (Sum.inl i) : ℝ) -
                  (∑ i : Fin ℓ, (G.degree (Sum.inl i) : ℝ)) / ℓ) ^ 2 ∨
                C * p * ℓ * n ≤ ∑ j : Fin n, ((G.degree (Sum.inr j) : ℝ) -
                  (∑ j : Fin n, (G.degree (Sum.inr j) : ℝ)) / n) ^ 2) ∧
              (∀ i : Fin ℓ, |(G.degree (Sum.inl i) : ℝ) - p * n| ≤ p * n) ∧
              ∀ j : Fin n, |(G.degree (Sum.inr j) : ℝ) - p * ℓ| ≤ p * n} ≤
          ENNReal.ofReal (Real.exp (-K * n)) := by
  intro θ T K hθ hθ1 hT hK
  obtain ⟨C, hC, n₀, h⟩ := bipartite_graph_degree_concentration θ T K hθ hθ1 hT hK
  exact ⟨C, hC, n₀, fun n hn p hp1 hp2 ℓ hℓ1 hℓ2 ↦ h n hn p ⟨hp1, hp2⟩ ℓ ⟨hℓ1, hℓ2⟩⟩

open Classical in
/-- The literal real-density statement, expanded; the endpoint itself proves `0 < p < 1`. -/
example :
    ∀ θ T K : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ p : ℝ, T⁻¹ * (n : ℝ) ^ (-θ) < p → p < T * (n : ℝ) ^ (-θ) →
      ∃ hp : 0 < p ∧ p < 1,
        SimpleGraph.binomialRandom (Fin n) ⟨p, hp.1.le, hp.2.le⟩
          {G | C * p * (n : ℝ) ^ 2 ≤
                ∑ i, ((G.degree i : ℝ) - (∑ i, (G.degree i : ℝ)) / n) ^ 2 ∧
              ∀ i, |(G.degree i : ℝ) - p * n| ≤ p * n} ≤
            ENNReal.ofReal (Real.exp (-K * n)) ∧
        ∀ ℓ : ℕ, T⁻¹ * (n : ℝ) ≤ ℓ → (ℓ : ℝ) ≤ T * n →
          setBer((Set.univ : Set (Fin ℓ × Fin n)), ⟨p, hp.1.le, hp.2.le⟩)
            {E | (C * p * ℓ * n ≤
                    ∑ i : Fin ℓ, (((Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).card : ℝ) -
                      (∑ i : Fin ℓ, ((Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).card : ℝ)) /
                        ℓ) ^ 2 ∨
                  C * p * ℓ * n ≤
                    ∑ j : Fin n, (((Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).card : ℝ) -
                      (∑ j : Fin n, ((Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).card : ℝ)) /
                        n) ^ 2) ∧
                (∀ i : Fin ℓ,
                  |((Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).card : ℝ) - p * n| ≤ p * n) ∧
                ∀ j : Fin n,
                  |((Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).card : ℝ) - p * ℓ| ≤ p * n} ≤
            ENNReal.ofReal (Real.exp (-K * n)) := by
  intro θ T K hθ hθ1 hT hK
  obtain ⟨C, hC, n₀, h⟩ := degree_concentration_real θ T K hθ hθ1 hT hK
  refine ⟨C, hC, n₀, fun n hn p hp1 hp2 ↦ ?_⟩
  obtain ⟨hp, hgraph, hbip⟩ := h n hn p hp1 hp2
  exact ⟨hp, hgraph, fun ℓ hℓ1 hℓ2 ↦ hbip ℓ ⟨hℓ1, hℓ2⟩⟩

end MajorityDynamics.Probability.DegreeConcentration

/-! ### Axiom audits

The only non-foundational dependency is the accepted scalar binomial Chernoff input. -/

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.degree_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.degree_concentration

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.graph_degree_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.graph_degree_concentration

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.bipartite_degree_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.bipartite_degree_concentration

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.bipartite_graph_degree_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.bipartite_graph_degree_concentration

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.degree_concentration_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.degree_concentration_real

/-! The reusable helpers: the truncated bound is the only user of the Chernoff input; the
site-model laws and independence, the random-cut covering, and the bipartite graph bridge are
foundational-only. -/

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.truncated_square_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.truncated_square_bound

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.truncated_exp_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.truncated_exp_moment

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.siteLaw_map_blockCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.siteLaw_map_blockCount

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.blockCount_iIndepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.blockCount_iIndepFun

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.exists_cut_of_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.exists_cut_of_spread

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.sum_sq_mean_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.sum_sq_mean_le

/-- info: 'MajorityDynamics.Probability.DegreeConcentration.bipartiteGraphLaw_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.DegreeConcentration.bipartiteGraphLaw_bad

