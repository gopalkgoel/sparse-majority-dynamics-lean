import MajorityDynamics.Paper.Expansion.Main

noncomputable section
namespace MajorityDynamics.Paper.Expansion

/-- Expanded original corollary 5.9 frontier: no pending internal input and
no additional premise of any kind. -/
example : ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
      densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
      graphLaw N p {G | ¬ ((N:ℝ)/Real.sqrt ((p:ℝ)*N)*Real.log N ≤
        lead (coloringOnDay G c (expansionDay θ)))} ≤ ENNReal.ofReal ε := expansion

end MajorityDynamics.Paper.Expansion

/-- info: 'MajorityDynamics.Paper.Expansion.expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.Expansion.expansion
