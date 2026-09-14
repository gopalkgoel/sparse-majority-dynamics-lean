import MajorityDynamics.Probability.NeighborhoodBulk.Adapters
import MajorityDynamics.Literature.DegreeEnumeration.Checks

/-! Audits of the finite-model layer, imported by the closed C.4 `Checks` target. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling

example {V : Type*} [Fintype V] (A B : Finset V) (k l : ℕ) (f : Finset V → ℝ) :
    (∫ R, f (R.1 ∪ R.2) ∂(uniformOn (A.powersetCard k : Set (Finset V))).prod
      (uniformOn (B.powersetCard l : Set (Finset V)))) =
    (∑ R₁ ∈ A.powersetCard k, ∑ R₂ ∈ B.powersetCard l, f (R₁ ∪ R₂)) /
      ((A.card.choose k : ℝ) * (B.card.choose l : ℝ)) :=
  subsetExpectation_eq_average A B k l f

example {n : ℕ} (p : ℝ) (d : Fin n → ℤ) (v : Fin n) (R : Finset (Fin n)) :
    graphWeight p d v R =
      (∑ i ∈ R, (((d i : ℝ) - p * n) / Real.sqrt (p * n)) / Real.sqrt (p * n)) -
      ∑ i ∈ Finset.univ \ insert v R,
        Real.sqrt (p * n) / n * (((d i : ℝ) - p * n) / Real.sqrt (p * n)) := rfl

example {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ) (R : Finset (Fin n)) :
    bipartiteWeight p ell b R =
      (∑ j ∈ R, (((b j : ℝ) - p * ell) / Real.sqrt (p * ell)) / Real.sqrt (p * ell)) -
      ∑ j ∈ Finset.univ \ R,
        Real.sqrt (p * ell) / ell * (((b j : ℝ) - p * ell) / Real.sqrt (p * ell)) := rfl

example {n : ℕ} (d : Fin n → ℤ) (v : Fin n) (S : Finset (Fin n))
    (t : ℤ) (ht : 0 ≤ t) (htd : t ≤ d v)
    (h : (S.erase v).card < t.toNat ∨
      (Finset.univ \ insert v S).card < (d v - t).toNat) (p : ℝ) :
    fixedDegreeLaw (fun i => (d i).toNat)
      {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} = 0 ∧
      graphComparison p d v S t = 0 :=
  ⟨graph_event_zero d v S t ht htd h, graphComparison_zero p d v S t h⟩

example {ell : ℤ} {n : ℕ} (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ)
    (v : Fin ell.toNat) (S : Finset (Fin n)) (t : ℤ) (ht : 0 ≤ t) (htd : t ≤ a v)
    (h : S.card < t.toNat ∨ n - S.card < (a v - t).toNat) (p : ℝ) :
    bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)
      {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} = 0 ∧
      bipartiteComparison p ell b (a v) S t = 0 :=
  ⟨bipartite_event_zero a b v S t ht htd h, bipartiteComparison_zero p ell b (a v) S t h⟩

end MajorityDynamics.Probability.NeighborhoodBulk

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.subsetExpectation_eq_average' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.subsetExpectation_eq_average

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.subsetPairLaw_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.subsetPairLaw_independent

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.graph_event_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.graph_event_zero

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartite_event_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartite_event_zero

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartite_event_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartite_event_adapter
