import MajorityDynamics.Probability.NeighborhoodTail.FinChecks
import MajorityDynamics.Probability.NeighborhoodTail.CarrierMain

/-! Literal carrier contracts and exact transitive axiom guards. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios

theorem graph_carrier_expanded (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ (V : Type*) [Fintype V], n₀ ≤ Fintype.card V →
        ∀ p : ℝ, T⁻¹ * (Fintype.card V : ℝ) ^ (-θ) < p ∧
          p < T * (Fintype.card V : ℝ) ^ (-θ) →
          0 < p ∧ p < 1 ∧
  ∀ (m : ℤ) (d : V → ℕ),
    (∀ v, (d v : ℤ) ≤ (Fintype.card V : ℤ) - 1) →
    (∑ v, (d v : ℤ)) = 2 * m →
    |(m : ℝ) - p * Fintype.card V * ((Fintype.card V : ℝ) - 1) / 2| ≤
      T * (Fintype.card V : ℝ) ^ 2 * p / Real.sqrt (p * Fintype.card V) →
    (∀ v, |((d v : ℝ) - p * Fintype.card V) / Real.sqrt (p * Fintype.card V)| ≤
      Real.log (Fintype.card V)) →
    (graphFamily d).Nonempty ∧
      ∀ (v : V) (S : Finset V),
        (Fintype.card V : ℝ) / T ≤ S.card →
        (Fintype.card V : ℝ) / T ≤ (Fintype.card V : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ (d v : ℤ) →
          Real.log (Fintype.card V : ℝ) ^ 100 ≤
            |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
          (fixedDegreeLaw d).real {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} ≤
            Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2) :=
  graph_carrier_neighborhood_tail θ T hθlo hθhi hT

theorem bipartite_carrier_expanded (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ (L R : Type*) [Fintype L] [Fintype R], n₀ ≤ Fintype.card R →
        ∀ p : ℝ, T⁻¹ * (Fintype.card R : ℝ) ^ (-θ) < p ∧
          p < T * (Fintype.card R : ℝ) ^ (-θ) →
          0 < p ∧ p < 1 ∧
  ((Fintype.card R : ℝ) / T ≤ Fintype.card L →
  (Fintype.card L : ℝ) ≤ T * Fintype.card R →
  ∀ (m : ℤ) (a : L → ℕ) (b : R → ℕ),
    (∀ i, a i ≤ Fintype.card R) → (∀ j, b j ≤ Fintype.card L) →
    (∑ i, (a i : ℤ)) = m → (∑ j, (b j : ℤ)) = m →
    |(m : ℝ) - p * Fintype.card L * Fintype.card R| ≤
      T * (Fintype.card R : ℝ) ^ 2 * p / Real.sqrt (p * Fintype.card R) →
    (∀ i, |((a i : ℝ) - p * Fintype.card R) / Real.sqrt (p * Fintype.card R)| ≤
      Real.log (Fintype.card R)) →
    (∀ j, |((b j : ℝ) - p * Fintype.card L) / Real.sqrt (p * Fintype.card L)| ≤
      Real.log (Fintype.card R)) →
    (bipartiteFamily a b).Nonempty ∧
      ∀ (v : L) (S : Finset R),
        (Fintype.card R : ℝ) / T ≤ S.card →
        (Fintype.card R : ℝ) / T ≤ (Fintype.card R : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ a v →
          Real.log (Fintype.card R : ℝ) ^ 100 ≤
            |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
          (bipartiteFixedDegreeLaw a b).real
            {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} ≤
            Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2)) :=
  bipartite_carrier_neighborhood_tail θ T hθlo hθhi hT

end MajorityDynamics.Probability.NeighborhoodTail

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_neighborhood_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_neighborhood_tail

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_expanded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_expanded

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_carrier_neighborhood_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_carrier_neighborhood_tail

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_carrier_expanded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_carrier_expanded

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartite_neighborhood_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartite_neighborhood_tail

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartite_expanded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartite_expanded

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartite_carrier_neighborhood_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartite_carrier_neighborhood_tail

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartite_carrier_expanded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartite_carrier_expanded

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.neighborhood_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.neighborhood_tail

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.carrier_neighborhood_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.carrier_neighborhood_tail

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.subsetExpectation_eq_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.subsetExpectation_eq_nested

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graphWeight_eq_tilt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graphWeight_eq_tilt

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartiteWeight_eq_tilt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartiteWeight_eq_tilt

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graphComparison_eq_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graphComparison_eq_factor

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartiteComparison_eq_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartiteComparison_eq_factor

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.degreeWindow_of_standardized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.degreeWindow_of_standardized

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_neighborFinset_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_neighborFinset_relabel

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_neighborhood_card_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_neighborhood_card_relabel

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_neighborhood_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_neighborhood_relabel

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartite_neighborhood_card_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartite_neighborhood_card_relabel

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartite_neighborhood_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartite_neighborhood_relabel

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graphCarrierConclusion_of_fin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graphCarrierConclusion_of_fin

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartiteCarrierConclusion_of_fin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartiteCarrierConclusion_of_fin

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.GraphConclusion.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.GraphConclusion.mono

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.BipartiteConclusion.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.BipartiteConclusion.mono

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_zero_target

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_full_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_full_target

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.graph_conclusion_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.graph_conclusion_normalized

/--
info: 'MajorityDynamics.Probability.NeighborhoodTail.bipartite_conclusion_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.bipartite_conclusion_normalized

