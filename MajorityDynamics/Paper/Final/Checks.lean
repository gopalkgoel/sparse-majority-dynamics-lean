import MajorityDynamics.Paper.Final.Main
import MajorityDynamics.Paper.Final.TransportChecks
import MajorityDynamics.Probability.RandomOpinionsReduction.Checks

/-! Exact target checks for completion under the agreed literature policy.
The guards record the exact transitive dependencies of the closed proofs.
The foundations-only gate remains separate and unchanged. -/
open MajorityDynamics.Paper MajorityDynamics.Probability.RandomOpinionsReduction

example : MainTheorem := main
example : MainFiniteTheorem := main_finite
example : MainFiniteRealTheorem := main_finite_real
example : RandomOpinionsTheorem := random_opinions
example : RandomOpinionsFiniteRealTheorem := random_opinions_finite_real

-- Literal original fixed-coloring probability statement, without auxiliary assumptions.
example : (∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p : unitInterval) (τ : ℝ) (c : Fin N → Bool),
      (T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) ∧ (p : ℝ) < T*(N : ℝ)^(-θ)) →
      T⁻¹ ≤ τ → τ ≤ T →
      (Finset.univ.filter (fun v => c v = false)).card = N/2 + ⌊τ*Real.sqrt N⌋₊ →
      SimpleGraph.binomialRandom (Fin N) p
        {G | ∀ v, coloringOnDay G c (2*(⌊1/(1-θ)⌋₊+1)+1) v = false}ᶜ ≤
          ENNReal.ofReal ε) := main

/-- info: 'MajorityDynamics.Paper.Expansion.expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.Expansion.expansion

/-- info: 'MajorityDynamics.Paper.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.main

/-- info: 'MajorityDynamics.Paper.main_finite_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.main_finite_real

/-- info: 'MajorityDynamics.Paper.random_opinions_finite_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.random_opinions_finite_real
