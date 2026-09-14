import MajorityDynamics.Combinatorics.DegreeRatios.Main

namespace MajorityDynamics.Combinatorics.DegreeRatios

example : GraphDegreeRatioTheorem := graph_degree_ratio
example : BipartiteDegreeRatioTheorem := bipartite_degree_ratio
example : DegreeRatiosTheorem := degree_ratios

example :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
          ∀ m d : ℤ, GraphWindow T n p m d →
            Real.exp (-C * Real.log n) * p ^ (-d) * Real.exp (p * n) ≤ graphRatio n m d ∧
              graphRatio n m d ≤ Real.exp (C * Real.log n) * p ^ (-d) * Real.exp (p * n) :=
  graph_multiplicative

example :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
          ∀ ell m d : ℤ, BipartiteWindow T n p ell m d →
            Real.exp (-C * Real.log n) * p ^ (-d) * Real.exp (p * n) ≤ bipartiteRatio n ell m d ∧
              bipartiteRatio n ell m d ≤ Real.exp (C * Real.log n) * p ^ (-d) * Real.exp (p * n) :=
  bipartite_multiplicative

/-- Independently expanded integer windows, validity, positivity, and errors. -/
example :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ,
          (T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ)) →
          (∀ m d : ℤ,
            (|(m : ℝ) - p * n * ((n : ℝ) - 1) / 2| ≤
              T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧
              |(d : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n) →
            (0 ≤ d ∧ d ≤ m ∧ 0 ≤ m ∧
              m ≤ (edgeCapacity n : ℤ) ∧ m - d ≤ (edgeCapacity (n - 1) : ℤ) ∧
              0 ≤ 2 * m ∧ 2 * m ≤ (n * (n - 1) : ℕ) ∧
              0 ≤ 2 * m - 2 * d ∧ 2 * m - 2 * d ≤ ((n - 1) * (n - 2) : ℕ) ∧
              0 < ((edgeCapacity n).choose m.toNat : ℝ) ∧
              0 < ((edgeCapacity (n - 1)).choose (m - d).toNat : ℝ) ∧
              0 < ((n * (n - 1)).choose (2 * m).toNat : ℝ) ∧
              0 < (((n - 1) * (n - 2)).choose (2 * m - 2 * d).toNat : ℝ)) ∧
            0 < graphRatio n m d ∧
            |Real.log (graphRatio n m d) + (d : ℝ) * Real.log p - p * n| ≤ C * Real.log n) ∧
          (∀ ell m d : ℤ,
            (T⁻¹ * n ≤ (ell : ℝ) ∧ (ell : ℝ) ≤ T * n ∧
              |(m : ℝ) - p * ell * n| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ∧
              |(d : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n) →
            (1 ≤ ell ∧ 0 ≤ d ∧ d ≤ m ∧ 0 ≤ m ∧
              m ≤ ell * n ∧ m - d ≤ (ell - 1) * n ∧
              0 < (((ell * (n : ℤ)).toNat).choose m.toNat : ℝ) ∧
              0 < ((((ell - 1) * (n : ℤ)).toNat).choose (m - d).toNat : ℝ)) ∧
            0 < bipartiteRatio n ell m d ∧
            |Real.log (bipartiteRatio n ell m d) + (d : ℝ) * Real.log p - p * n| ≤
              C * Real.log n) := degree_ratios

/-- info: 'MajorityDynamics.Combinatorics.DegreeRatios.graph_degree_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_degree_ratio

/-- info: 'MajorityDynamics.Combinatorics.DegreeRatios.bipartite_degree_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bipartite_degree_ratio

/-- info: 'MajorityDynamics.Combinatorics.DegreeRatios.degree_ratios' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degree_ratios

/-- info: 'MajorityDynamics.Combinatorics.DegreeRatios.graph_multiplicative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_multiplicative

/-- info: 'MajorityDynamics.Combinatorics.DegreeRatios.bipartite_multiplicative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bipartite_multiplicative

end MajorityDynamics.Combinatorics.DegreeRatios
