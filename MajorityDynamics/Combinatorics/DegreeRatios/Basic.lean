import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast

/-! # The literal integer-input contract of Lemma C.3

The manuscript label is `lem:nice_deg_technical`. All subtraction on lower
indices is performed in ℤ before conversion to ℕ. The conclusions explicitly
require validity of those conversions and positivity of every coefficient.
The bipartite quotient has the opposite removal orientation to the ordinary
binomial quotient occurring in the graph expression.
-/

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

def edgeCapacity (n : ℕ) : ℕ := n * (n - 1) / 2

def graphRatio (n : ℕ) (m d : ℤ) : ℝ :=
  (((edgeCapacity (n - 1)).choose (m - d).toNat : ℝ) /
    (((n - 1) * (n - 2)).choose (2 * m - 2 * d).toNat : ℝ)) /
  (((edgeCapacity n).choose m.toNat : ℝ) /
    ((n * (n - 1)).choose (2 * m).toNat : ℝ))

def bipartiteRatio (n : ℕ) (ell m d : ℤ) : ℝ :=
  (((ell * (n : ℤ)).toNat).choose m.toNat : ℝ) /
    ((((ell - 1) * (n : ℤ)).toNat).choose (m - d).toNat : ℝ)

def DensityWindow (θ T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ)

def DegreeWindow (n : ℕ) (p : ℝ) (d : ℤ) : Prop :=
  |(d : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n

def GraphWindow (T : ℝ) (n : ℕ) (p : ℝ) (m d : ℤ) : Prop :=
  |(m : ℝ) - p * n * ((n : ℝ) - 1) / 2| ≤
    T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧ DegreeWindow n p d

def BipartiteWindow (T : ℝ) (n : ℕ) (p : ℝ) (ell m d : ℤ) : Prop :=
  T⁻¹ * n ≤ (ell : ℝ) ∧ (ell : ℝ) ≤ T * n ∧
  |(m : ℝ) - p * ell * n| ≤
    T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧ DegreeWindow n p d

def GraphDomain (n : ℕ) (m d : ℤ) : Prop :=
  0 ≤ d ∧ d ≤ m ∧ 0 ≤ m ∧
  m ≤ (edgeCapacity n : ℤ) ∧
  m - d ≤ (edgeCapacity (n - 1) : ℤ) ∧
  0 ≤ 2 * m ∧ 2 * m ≤ (n * (n - 1) : ℕ) ∧
  0 ≤ 2 * m - 2 * d ∧
  2 * m - 2 * d ≤ ((n - 1) * (n - 2) : ℕ) ∧
  0 < ((edgeCapacity n).choose m.toNat : ℝ) ∧
  0 < ((edgeCapacity (n - 1)).choose (m - d).toNat : ℝ) ∧
  0 < ((n * (n - 1)).choose (2 * m).toNat : ℝ) ∧
  0 < (((n - 1) * (n - 2)).choose (2 * m - 2 * d).toNat : ℝ)

def BipartiteDomain (n : ℕ) (ell m d : ℤ) : Prop :=
  1 ≤ ell ∧ 0 ≤ d ∧ d ≤ m ∧ 0 ≤ m ∧
  m ≤ ell * n ∧ m - d ≤ (ell - 1) * n ∧
  0 < (((ell * (n : ℤ)).toNat).choose m.toNat : ℝ) ∧
  0 < ((((ell - 1) * (n : ℤ)).toNat).choose (m - d).toNat : ℝ)

def GraphEstimate (C : ℝ) (n : ℕ) (p : ℝ) (m d : ℤ) : Prop :=
  GraphDomain n m d ∧ 0 < graphRatio n m d ∧
    |Real.log (graphRatio n m d) + (d : ℝ) * Real.log p - p * n| ≤ C * Real.log n

def BipartiteEstimate (C : ℝ) (n : ℕ) (p : ℝ) (ell m d : ℤ) : Prop :=
  BipartiteDomain n ell m d ∧ 0 < bipartiteRatio n ell m d ∧
    |Real.log (bipartiteRatio n ell m d) + (d : ℝ) * Real.log p - p * n| ≤
      C * Real.log n

def GraphDegreeRatioTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        ∀ m d : ℤ, GraphWindow T n p m d → GraphEstimate C n p m d

def BipartiteDegreeRatioTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        ∀ ell m d : ℤ, BipartiteWindow T n p ell m d → BipartiteEstimate C n p ell m d

def DegreeRatiosTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
        (∀ m d : ℤ, GraphWindow T n p m d → GraphEstimate C n p m d) ∧
        (∀ ell m d : ℤ, BipartiteWindow T n p ell m d → BipartiteEstimate C n p ell m d)

end MajorityDynamics.Combinatorics.DegreeRatios
