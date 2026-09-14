import MajorityDynamics.Paper.Final.Transport

noncomputable section
open MajorityDynamics.Paper MajorityDynamics.Probability.RandomOpinionsReduction

example : MainTheorem → MainFiniteTheorem := main_finite_of_main
example : MainTheorem → MainFiniteRealTheorem := main_finite_real_of_main

example : MainFiniteRealTheorem =
    (∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Type) [Fintype V], Fintype.card V = N →
        ∀ (p τ : ℝ) (c : V → Bool),
          T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-θ) →
          T⁻¹ ≤ τ → τ ≤ T →
          (Finset.univ.filter fun v => c v = false).card =
            Fintype.card V / 2 + ⌊τ * Real.sqrt (Fintype.card V : ℝ)⌋₊ →
          ∃ hp : 0 < p ∧ p < 1,
            SimpleGraph.binomialRandom V ⟨p, hp.1.le, hp.2.le⟩
              {G | ∀ v, coloringOnDayV G c (2 * (⌊1 / (1-θ)⌋₊ + 1) + 1) v = false}ᶜ ≤
                ENNReal.ofReal ε) := by
  classical
  rfl

/-- info: 'MajorityDynamics.Paper.main_finite_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.main_finite_of_main

/-- info: 'MajorityDynamics.Paper.main_finite_real_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.main_finite_real_of_main
