import MajorityDynamics.Probability.NeighborhoodTail.Main

/-! Expanded original integer-data contracts, including the actual uniform laws.
The examples make all assumptions and the position of uniform constants visible. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk
open MajorityDynamics.Combinatorics.DegreeRatios

theorem graph_expanded : ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
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
              Real.log (n : ℝ) ^ 100 ≤ |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
              (uniformOn (graphFamily (fun i => (d i).toNat))).real
                {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} ≤
                Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2) :=
  graph_neighborhood_tail

theorem bipartite_expanded : ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
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
              Real.log (n : ℝ) ^ 100 ≤ |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
              (uniformOn (bipartiteFamily (fun i => (a i).toNat) (fun j => (b j).toNat))).real
                {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} ≤
                Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2) :=
  bipartite_neighborhood_tail

example : NeighborhoodTailTheorem := neighborhood_tail

/-- Endpoint t=0 is included literally, without an interior-target restriction. -/
theorem graph_zero_target {c T p : ℝ} {n : ℕ} (h : GraphConclusion c T n p)
    (m : ℤ) (d : Fin n → ℤ) (hd : GraphInput T n p m d)
    (v : Fin n) (S : Finset (Fin n)) (hS : (n : ℝ) / T ≤ S.card)
    (hSc : (n : ℝ) / T ≤ (n : ℝ) - S.card)
    (hτ : Real.log (n : ℝ) ^ 100 ≤ |(0 - p * S.card) / Real.sqrt (p * S.card)|) :
    (fixedDegreeLaw (fun i => (d i).toNat)).real
      {G | ((G.neighborFinset v ∩ S).card : ℤ) = 0} ≤
      Real.exp (-c * ((0 - p * S.card) / Real.sqrt (p * S.card)) ^ 2) := by
  simpa only [Int.cast_zero] using
    (h m d hd).2 v S hS hSc 0 le_rfl (hd.1 v).1 (by simpa only [Int.cast_zero] using hτ)

/-- Endpoint t=d_v uses the same target center and the actual law. -/
theorem graph_full_target {c T p : ℝ} {n : ℕ} (h : GraphConclusion c T n p)
    (m : ℤ) (d : Fin n → ℤ) (hd : GraphInput T n p m d)
    (v : Fin n) (S : Finset (Fin n)) (hS : (n : ℝ) / T ≤ S.card)
    (hSc : (n : ℝ) / T ≤ (n : ℝ) - S.card)
    (hτ : Real.log (n : ℝ) ^ 100 ≤ |((d v : ℝ) - p * S.card) / Real.sqrt (p * S.card)|) :
    (fixedDegreeLaw (fun i => (d i).toNat)).real
      {G | ((G.neighborFinset v ∩ S).card : ℤ) = d v} ≤
      Real.exp (-c * (((d v : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2) := by
  exact (h m d hd).2 v S hS hSc (d v) (hd.1 v).1 le_rfl hτ

theorem graph_conclusion_normalized {c T p : ℝ} {n : ℕ} (h : GraphConclusion c T n p)
    (m : ℤ) (d : Fin n → ℤ) (hd : GraphInput T n p m d) :
    IsProbabilityMeasure (fixedDegreeLaw (fun i => (d i).toNat)) :=
  fixedDegreeLaw_normalized _ (h m d hd).1

theorem bipartite_conclusion_normalized {c T p : ℝ} {n : ℕ}
    (h : BipartiteConclusion c T n p)
    (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ)
    (hd : BipartiteInput T n p ell m a b) :
    IsProbabilityMeasure (bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)) :=
  bipartiteFixedDegreeLaw_normalized _ _ (h ell m a b hd).1

end MajorityDynamics.Probability.NeighborhoodTail
