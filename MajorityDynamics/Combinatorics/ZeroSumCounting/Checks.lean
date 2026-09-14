import MajorityDynamics.Combinatorics.ZeroSumCounting.Main

/-!
# Lemma A.11 endpoint checks

Exact type check of the public endpoint, an independently written expansion of the
statement (the counted set written out as a filtered box with the real radius condition and
the integer sum condition, so that the actual quantifiers and conclusion are visible here),
the membership characterisation, and guarded axiom audits.
-/

open scoped BigOperators

namespace MajorityDynamics.Combinatorics.ZeroSumCounting

example : ZeroSumCountingTheorem := zero_sum_counting

/-- The membership specification of the counted set, restated. -/
example (n : ℕ) (ρ : ℝ) (y : Fin n → ℤ) :
    y ∈ zeroSumVectors n ρ ↔ (∀ i, |(y i : ℝ)| ≤ ρ) ∧ ∑ i, y i = 0 :=
  mem_zeroSumVectors

/-- The endpoint, expanded: for `θ ∈ (1/2,1)`, `T > 1`, `C > 0`, there are `K > 0` and `n₀`
such that for all `n ≥ n₀` and real `p ∈ (T⁻¹ n^{-θ}, T n^{-θ})`,
`exp(-K n) (√(np))^n ≤ #{y : Fin n → ℤ | ∀ i, |yᵢ| ≤ C √(np), ∑ᵢ yᵢ = 0}`,
where the set is written as the filter of the bounding box `∏ᵢ Icc (-⌊C√(np)⌋₊) ⌊C√(np)⌋₊`
by the real radius condition and the exact sum condition. -/
example :
    ∀ θ T C : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < C →
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ p : ℝ, T⁻¹ * (n : ℝ) ^ (-θ) < p → p < T * (n : ℝ) ^ (-θ) →
      Real.exp (-K * (n : ℝ)) * Real.sqrt ((n : ℝ) * p) ^ n ≤
        (((Fintype.piFinset fun _ : Fin n ↦
            Finset.Icc (-(⌊C * Real.sqrt ((n : ℝ) * p)⌋₊ : ℤ)) ⌊C * Real.sqrt ((n : ℝ) * p)⌋₊).filter
          fun y : Fin n → ℤ ↦
            (∀ i, |(y i : ℝ)| ≤ C * Real.sqrt ((n : ℝ) * p)) ∧ ∑ i, y i = 0).card : ℝ) :=
  zero_sum_counting

/-- The same conclusion with the set written as a subtype-free predicate count: every vector
counted satisfies exactly the two displayed conditions, and every such vector is counted. -/
example (n : ℕ) (ρ : ℝ) :
    ∀ y : Fin n → ℤ, y ∈ zeroSumVectors n ρ ↔ ((∀ i, |(y i : ℝ)| ≤ ρ) ∧ ∑ i, y i = 0) :=
  fun _ ↦ mem_zeroSumVectors

end MajorityDynamics.Combinatorics.ZeroSumCounting

/-! ### Axiom audits: standard foundations only. -/

/-- info: 'MajorityDynamics.Combinatorics.ZeroSumCounting.zero_sum_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Combinatorics.ZeroSumCounting.zero_sum_counting

/-- info: 'MajorityDynamics.Combinatorics.ZeroSumCounting.zero_sum_counting_fixed_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Combinatorics.ZeroSumCounting.zero_sum_counting_fixed_radius

/-- info: 'MajorityDynamics.Combinatorics.ZeroSumCounting.card_boxZeroSum_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Combinatorics.ZeroSumCounting.card_boxZeroSum_ge

/-- info: 'MajorityDynamics.Combinatorics.ZeroSumCounting.mem_zeroSumVectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Combinatorics.ZeroSumCounting.mem_zeroSumVectors
