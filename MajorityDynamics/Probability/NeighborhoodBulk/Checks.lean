import MajorityDynamics.Probability.NeighborhoodBulk.Main
import MajorityDynamics.Probability.NeighborhoodBulk.AnalyticChecks

/-! Closed C.4 contracts, expanded probability/expectation checks and exact
transitive dependencies. The finite audits also check zero-capacity cases. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios

example : GraphNeighborhoodBulkTheorem := graph_neighborhood_bulk
example : BipartiteNeighborhoodBulkTheorem := bipartite_neighborhood_bulk
example : NeighborhoodBulkTheorem := neighborhood_bulk

example : ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ) →
        0 < p ∧ p < 1 ∧
        ∀ (m : ℤ) (d : Fin n → ℤ),
          (∀ i, 0 ≤ d i ∧ d i ≤ (n : ℤ) - 1) ∧ (∑ i, d i) = 2 * m ∧
          |(m : ℝ) - p * n * ((n : ℝ) - 1) / 2| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧
          (∀ i, |((d i : ℝ) - p * n) / Real.sqrt (p * n)| ≤ Real.log n) →
          (graphFamily (fun i => (d i).toNat)).Nonempty ∧
          ∀ (v : Fin n) (S : Finset (Fin n)),
            (n : ℝ) / T ≤ S.card → (n : ℝ) / T ≤ (n : ℝ) - S.card →
            ∀ t : ℤ, 0 ≤ t → t ≤ d v →
              let Q :=
                ((S.card - if v ∈ S then 1 else 0).choose t.toNat : ℝ) *
                  ((n - S.card - if v ∉ S then 1 else 0).choose (d v - t).toNat : ℝ) /
                  ((n - 1).choose (d v).toNat : ℝ) *
                ∫ R : Finset (Fin n) × Finset (Fin n),
                  Real.exp ((∑ i ∈ R.1 ∪ R.2,
                    (((d i : ℝ) - p * n) / Real.sqrt (p * n)) / Real.sqrt (p * n)) -
                    ∑ i ∈ Finset.univ \ insert v (R.1 ∪ R.2),
                      Real.sqrt (p * n) / n * (((d i : ℝ) - p * n) / Real.sqrt (p * n)))
                  ∂(uniformOn ((S.erase v).powersetCard t.toNat : Set (Finset (Fin n)))).prod
                    (uniformOn ((Finset.univ \ insert v S).powersetCard (d v - t).toNat : Set (Finset (Fin n))))
              let P := (uniformOn (graphFamily (fun i => (d i).toNat))).real
                {G | ((G.neighborFinset v ∩ S).card : ℤ) = t}
              Real.exp (-C * Real.log n ^ 4) * Q ≤ P ∧ P ≤ Real.exp (C * Real.log n ^ 4) * Q := by
  convert graph_neighborhood_bulk using 1
  unfold GraphNeighborhoodBulkTheorem GraphConclusion GraphInput DensityWindow MultiplicativeBound
    graphComparison graphWeight standardizedDegree subsetExpectation subsetPairLaw subsetLaw fixedDegreeLaw
  congr!

example : ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ) →
        0 < p ∧ p < 1 ∧
        ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
          (n : ℝ) / T ≤ ell ∧ (ell : ℝ) ≤ T * n ∧
          (∀ i, 0 ≤ a i ∧ a i ≤ (n : ℤ)) ∧ (∀ j, 0 ≤ b j ∧ b j ≤ ell) ∧
          (∑ i, a i) = m ∧ (∑ j, b j) = m ∧
          |(m : ℝ) - p * ell * n| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧
          (∀ i, |((a i : ℝ) - p * n) / Real.sqrt (p * n)| ≤ Real.log n) ∧
          (∀ j, |((b j : ℝ) - p * ell) / Real.sqrt (p * ell)| ≤ Real.log n) →
          (bipartiteFamily (fun i => (a i).toNat) (fun j => (b j).toNat)).Nonempty ∧
          ∀ (v : Fin ell.toNat) (S : Finset (Fin n)),
            (n : ℝ) / T ≤ S.card → (n : ℝ) / T ≤ (n : ℝ) - S.card →
            ∀ t : ℤ, 0 ≤ t → t ≤ a v →
              let Q := (S.card.choose t.toNat : ℝ) * ((n - S.card).choose (a v - t).toNat : ℝ) /
                (n.choose (a v).toNat : ℝ) *
                ∫ R : Finset (Fin n) × Finset (Fin n),
                  Real.exp ((∑ j ∈ R.1 ∪ R.2,
                    (((b j : ℝ) - p * ell) / Real.sqrt (p * ell)) / Real.sqrt (p * ell)) -
                    ∑ j ∈ Finset.univ \ (R.1 ∪ R.2),
                      Real.sqrt (p * ell) / ell * (((b j : ℝ) - p * ell) / Real.sqrt (p * ell)))
                  ∂(uniformOn (S.powersetCard t.toNat : Set (Finset (Fin n)))).prod
                    (uniformOn ((Finset.univ \ S).powersetCard (a v - t).toNat : Set (Finset (Fin n))))
              let P := (uniformOn (bipartiteFamily (fun i => (a i).toNat) (fun j => (b j).toNat))).real
                {E | ((leftNeighbors E v ∩ S).card : ℤ) = t}
              Real.exp (-C * Real.log n ^ 4) * Q ≤ P ∧ P ≤ Real.exp (C * Real.log n ^ 4) * Q := by
  convert bipartite_neighborhood_bulk using 1
  unfold BipartiteNeighborhoodBulkTheorem BipartiteConclusion BipartiteInput DensityWindow MultiplicativeBound
    bipartiteComparison bipartiteWeight standardizedDegree subsetExpectation subsetPairLaw subsetLaw bipartiteFixedDegreeLaw
  congr!

example : ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion C T n p ∧ BipartiteConclusion C T n p := neighborhood_bulk

end MajorityDynamics.Probability.NeighborhoodBulk

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.graph_atom_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.graph_atom_bounds

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartite_atom_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartite_atom_bounds

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.graph_neighborhood_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.graph_neighborhood_bulk

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartite_neighborhood_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartite_neighborhood_bulk

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.neighborhood_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.neighborhood_bulk

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.graph_event_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.graph_event_sum

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartite_event_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartite_event_sum
