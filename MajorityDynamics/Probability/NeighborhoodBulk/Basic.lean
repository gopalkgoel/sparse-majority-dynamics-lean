import MajorityDynamics.Probability.NeighborhoodBulk.SubsetLaws
import MajorityDynamics.Probability.FixedDegreeSampling.Laws
import MajorityDynamics.Combinatorics.DegreeRatios.Basic

/-! Literal integer-data targets of `lem:nice_deg_bulk`. The predicates below
contain no graphicality or enumeration-applicability premise. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling MajorityDynamics.Combinatorics.DegreeRatios

def standardizedDegree (p size : ℝ) (d : ℤ) : ℝ :=
  ((d : ℝ) - p * size) / Real.sqrt (p * size)

def graphWeight {n : ℕ} (p : ℝ) (d : Fin n → ℤ) (v : Fin n) (R : Finset (Fin n)) : ℝ :=
  (∑ i ∈ R, standardizedDegree p n (d i) / Real.sqrt (p * n)) -
    ∑ i ∈ Finset.univ \ (insert v R),
      Real.sqrt (p * n) / n * standardizedDegree p n (d i)

def bipartiteWeight {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ)
    (R : Finset (Fin n)) : ℝ :=
  (∑ j ∈ R, standardizedDegree p ell (b j) / Real.sqrt (p * ell)) -
    ∑ j ∈ Finset.univ \ R,
      Real.sqrt (p * ell) / ell * standardizedDegree p ell (b j)

def graphComparison {n : ℕ} (p : ℝ) (d : Fin n → ℤ) (v : Fin n)
    (S : Finset (Fin n)) (t : ℤ) : ℝ :=
  ((S.card - if v ∈ S then 1 else 0).choose t.toNat : ℝ) *
      ((n - S.card - if v ∉ S then 1 else 0).choose (d v - t).toNat : ℝ) /
      ((n - 1).choose (d v).toNat : ℝ) *
    subsetExpectation (S.erase v) (Finset.univ \ insert v S)
      t.toNat (d v - t).toNat (fun R => Real.exp (graphWeight p d v R))

def bipartiteComparison {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ)
    (dv : ℤ) (S : Finset (Fin n)) (t : ℤ) : ℝ :=
  (S.card.choose t.toNat : ℝ) * ((n - S.card).choose (dv - t).toNat : ℝ) /
      (n.choose dv.toNat : ℝ) *
    subsetExpectation S (Finset.univ \ S) t.toNat (dv - t).toNat
      (fun R => Real.exp (bipartiteWeight p ell b R))

def GraphInput (T : ℝ) (n : ℕ) (p : ℝ) (m : ℤ) (d : Fin n → ℤ) : Prop :=
  (∀ i, 0 ≤ d i ∧ d i ≤ (n : ℤ) - 1) ∧ (∑ i, d i) = 2 * m ∧
    |(m : ℝ) - p * n * ((n : ℝ) - 1) / 2| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧
    ∀ i, |standardizedDegree p n (d i)| ≤ Real.log n

def BipartiteInput (T : ℝ) (n : ℕ) (p : ℝ) (ell m : ℤ)
    (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ) : Prop :=
  (n : ℝ) / T ≤ ell ∧ (ell : ℝ) ≤ T * n ∧
    (∀ i, 0 ≤ a i ∧ a i ≤ (n : ℤ)) ∧ (∀ j, 0 ≤ b j ∧ b j ≤ ell) ∧
    (∑ i, a i) = m ∧ (∑ j, b j) = m ∧
    |(m : ℝ) - p * ell * n| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧
    (∀ i, |standardizedDegree p n (a i)| ≤ Real.log n) ∧
    ∀ j, |standardizedDegree p ell (b j)| ≤ Real.log n

def MultiplicativeBound (C : ℝ) (n : ℕ) (P Q : ℝ) : Prop :=
  Real.exp (-C * Real.log n ^ 4) * Q ≤ P ∧
    P ≤ Real.exp (C * Real.log n ^ 4) * Q

def GraphConclusion (C T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
    (graphFamily (fun i => (d i).toNat)).Nonempty ∧
      ∀ (v : Fin n) (S : Finset (Fin n)),
        (n : ℝ) / T ≤ S.card → (n : ℝ) / T ≤ (n : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ d v →
          MultiplicativeBound C n
            ((fixedDegreeLaw (fun i => (d i).toNat)).real
              {G | ((G.neighborFinset v ∩ S).card : ℤ) = t})
            (graphComparison p d v S t)

def BipartiteConclusion (C T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
    BipartiteInput T n p ell m a b →
    (bipartiteFamily (fun i => (a i).toNat) (fun j => (b j).toNat)).Nonempty ∧
      ∀ (v : Fin ell.toNat) (S : Finset (Fin n)),
        (n : ℝ) / T ≤ S.card → (n : ℝ) / T ≤ (n : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ a v →
          MultiplicativeBound C n
            ((bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)).real
              {E | ((leftNeighbors E v ∩ S).card : ℤ) = t})
            (bipartiteComparison p ell b (a v) S t)

def GraphNeighborhoodBulkTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion C T n p

def BipartiteNeighborhoodBulkTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ BipartiteConclusion C T n p

def NeighborhoodBulkTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion C T n p ∧ BipartiteConclusion C T n p

end MajorityDynamics.Probability.NeighborhoodBulk
