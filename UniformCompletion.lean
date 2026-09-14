import MajorityDynamics.Paper.UniformMain

/-! Strict completion gate for the full uniform theorem, including p = 1.
The literal type exposes every quantifier, the actual graph law, exact initial
count, update convention and day. Only standard foundational axioms are allowed. -/
open MajorityDynamics MajorityDynamics.Paper

example : UniformMainTheorem := uniform_main

example : ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (p : unitInterval) (τ : ℝ) (c : Fin N → Bool),
        T⁻¹*(N:ℝ)^(-θ) ≤ (p:ℝ) →
        T⁻¹ ≤ τ → τ ≤ T →
        (Finset.univ.filter fun v => c v = false).card = N/2+⌊τ*Real.sqrt N⌋₊ →
        SimpleGraph.binomialRandom (Fin N) p
          {G | ¬∀ v, (nextColoring G)^[2*⌊1/(1-θ)⌋₊+2] c v = false} ≤
            ENNReal.ofReal ε := by
  intro θ T hθlo hθhi hT ε hε
  obtain ⟨N₀,hmain⟩ := uniform_main θ T hθlo hθhi hT ε hε
  refine ⟨N₀,?_⟩
  intro N hN p τ c hp hτ hτT hc
  have hday : uniformConvergenceDay θ-1 = 2*⌊1/(1-θ)⌋₊+2 := by
    unfold uniformConvergenceDay expansionDay
    omega
  simpa only [graphLaw,uniformSuccessEvent,coloringOnDay,hday,Set.compl_ofPred]
    using hmain N hN p τ c hp hτ hτT hc

/-- info: 'MajorityDynamics.Paper.uniform_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.uniform_main
