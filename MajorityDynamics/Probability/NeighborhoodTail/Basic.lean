import MajorityDynamics.Probability.NeighborhoodBulk.Basic

/-! Original-input interfaces for Theorem C.2. The law is the actual uniform
fixed-degree law, and the standardized target retains the original subset size. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk
open MajorityDynamics.Combinatorics.DegreeRatios

def GraphConclusion (c T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
    (graphFamily (fun i => (d i).toNat)).Nonempty ∧
      ∀ (v : Fin n) (S : Finset (Fin n)),
        (n : ℝ) / T ≤ S.card → (n : ℝ) / T ≤ (n : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ d v →
          Real.log (n : ℝ) ^ 100 ≤ |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
          (fixedDegreeLaw (fun i => (d i).toNat)).real
            {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} ≤
            Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2)

def BipartiteConclusion (c T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
    BipartiteInput T n p ell m a b →
    (bipartiteFamily (fun i => (a i).toNat) (fun j => (b j).toNat)).Nonempty ∧
      ∀ (v : Fin ell.toNat) (S : Finset (Fin n)),
        (n : ℝ) / T ≤ S.card → (n : ℝ) / T ≤ (n : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ a v →
          Real.log (n : ℝ) ^ 100 ≤ |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
          (bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)).real
            {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} ≤
            Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2)

def GraphNeighborhoodTailTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion c T n p

def BipartiteNeighborhoodTailTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ BipartiteConclusion c T n p

def NeighborhoodTailTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion c T n p ∧ BipartiteConclusion c T n p

end MajorityDynamics.Probability.NeighborhoodTail
