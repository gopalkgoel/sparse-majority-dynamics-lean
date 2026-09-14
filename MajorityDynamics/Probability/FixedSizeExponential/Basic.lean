import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.UniformOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fixed-size subsets and the target of Lemma C.5

This module contains the concrete finite probability model for
`lem:nice_deg_cute` in `latest/main.tex`.  A sample is a bit vector
`Fin n → Bool`; `bitSet` transports it to an actual finite subset of `Fin n`,
and `fixedSizeEvent n s` is the finite event of vectors whose transported
subset has cardinality `s`.  The uniform law is `uniformOn` this event.

The target below keeps the real density and literal integer-size quantifiers
from the manuscript.  In particular, it does not assume that `p` is already a
subtype of `(0,1)` or that the prescribed size is already in `[0,n]`.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.FixedSizeExponential

/-- A real success probability, used internally for the literal real-density
statement. -/
abbrev SuccessProbability := Set.Ioo (0 : ℝ) 1

/-- Put a real probability into Mathlib's closed unit interval. -/
def closedProbability (q : SuccessProbability) : unitInterval :=
  ⟨q, q.property.1.le, q.property.2.le⟩

/-- Bit vectors are the requested concrete representation of prescribed-size
subsets. -/
abbrev Bit (n : ℕ) := Fin n → Bool

/-- The subset represented by a bit vector. -/
def bitSet {n : ℕ} (ξ : Bit n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ξ i = true)

/-- The number of selected coordinates in a bit vector. -/
def bitCount {n : ℕ} (ξ : Bit n) : ℕ := (bitSet ξ).card

/-- The finite event of bit vectors selecting exactly `s` coordinates. -/
def fixedSizeEvent (n s : ℕ) : Finset (Bit n) :=
  Finset.univ.filter (fun ξ => bitCount ξ = s)

/-- The ambient event as a measurable set. -/
def fixedSizeEventSet (n s : ℕ) : Set (Bit n) := fixedSizeEvent n s

/-- The actual uniform prescribed-size law.  It is a probability measure once
`0 ≤ s ≤ n`; outside that range it is the zero conditional-counting measure,
which makes the definition total without weakening the theorem. -/
def fixedSizeMeasure (n s : ℕ) : Measure (Bit n) :=
  ProbabilityTheory.uniformOn (fixedSizeEventSet n s)

/-- Expectation under the concrete uniform prescribed-size law. -/
def fixedSizeExpectation (n s : ℕ) (f : Bit n → ℝ) : ℝ :=
  ∫ ξ, f ξ ∂fixedSizeMeasure n s

/-- The normalized finite average which represents the same law. -/
def fixedSizeAverage (n s : ℕ) (f : Bit n → ℝ) : ℝ :=
  (n.choose s : ℝ)⁻¹ * ∑ ξ ∈ fixedSizeEvent n s, f ξ

/-- The linear statistic used in the MGF statement. -/
def bitLinear {n : ℕ} (a : Fin n → ℝ) (ξ : Bit n) : ℝ :=
  ∑ i, if ξ i = true then a i else 0

/-- The independent Bernoulli product law on bit vectors. -/
def bitProductMeasure (n : ℕ) (q : SuccessProbability) : Measure (Bit n) :=
  Measure.pi (fun _ : Fin n =>
    ProbabilityTheory.bernoulliMeasure true false (closedProbability q))

instance (n : ℕ) (q : SuccessProbability) : IsProbabilityMeasure (bitProductMeasure n q) := by
  unfold bitProductMeasure
  infer_instance

/-- The literal density interval in the manuscript. -/
def SparseDensity (θ T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ)

/-- The literal integer-size interval in the manuscript. -/
def PrescribedSizeRange (T p : ℝ) (n s : ℕ) : Prop :=
  T⁻¹ * p * n ≤ (s : ℝ) ∧ (s : ℝ) ≤ T * p * n

/-- The small-weight hypothesis in `lem:nice_deg_cute`. -/
def FixedSizeWeightBound (T : ℝ) (n : ℕ) (p : ℝ) (a : Fin n → ℝ) : Prop :=
  ∀ i, |a i| ≤ T * Real.log (n : ℝ) / Real.sqrt (p * n)

/--
The exact closed target for Lemma C.5 (`lem:nice_deg_cute`).  Constants are
chosen before `n`, `p`, the signed weights, and the integer size.  The target
also exposes the eventual validity facts `0 < p < 1` and `0 < s < n`, and the
exact mean identity alongside the exponential-moment estimate.  The uniform
law is the concrete `fixedSizeMeasure`, not an independent Bernoulli product
law.
-/
def FixedSizeExponentialTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ p : ℝ, SparseDensity θ T n p →
      ∀ a : Fin n → ℝ, FixedSizeWeightBound T n p a →
      ∀ s : ℕ, PrescribedSizeRange T p n s →
        0 < p ∧ p < 1 ∧ 0 < s ∧ s < n ∧
        (fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
            C₁ * Real.sqrt (p * n) *
              Real.exp (fixedSizeExpectation n s (bitLinear a) + C₂ * (Real.log n) ^ 2) ∧
          fixedSizeExpectation n s (bitLinear a) =
            (s : ℝ) / n * ∑ i, a i)

end MajorityDynamics.Probability.FixedSizeExponential

