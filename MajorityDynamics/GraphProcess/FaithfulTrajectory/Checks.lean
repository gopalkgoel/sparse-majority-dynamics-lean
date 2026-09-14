import MajorityDynamics.GraphProcess.FaithfulTrajectory.Main
import MajorityDynamics.Paper.Expansion.Reduction

noncomputable section
open MeasureTheory
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution FineState CoarseKernel

/-- Literal uniformity and actual graph event for the closed faithful prefix. -/
example {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (n : ℕ) (hn : (n:ℝ) < 1/(1-θ)) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Paper.Coloring N),
      Paper.densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → Paper.initialBias N τ c →
      Paper.graphLaw N p {G | ∃ j ≤ n, ¬ Faithful N p U δ τ (referenceDataReal θ U N p)
        (rho p (actualState G c j))} ≤ ENNReal.ofReal ε :=
  faithful_prefix hθlo hθhi hT n hn

/-- The remaining intermediate input is explicit, and the conclusion is the
literal original expansion frontier rather than a modified target. -/
example (hcritical : CriticalDay.CriticalDayTheorem.{0}) :
    ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Paper.Coloring N),
      Paper.densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → Paper.initialBias N τ c →
      Paper.graphLaw N p {G | ¬ ((N:ℝ)/Real.sqrt ((p:ℝ)*N)*Real.log N ≤
        Paper.lead (Paper.coloringOnDay G c (Paper.expansionDay θ)))} ≤ ENNReal.ofReal ε :=
  Paper.Expansion.expansion_of_critical hcritical

/-- Both literal parts of 5.8 with constants before epsilon. -/
example {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ ζ : ℝ, 0 < ζ ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Paper.Coloring N),
      Paper.densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → Paper.initialBias N τ c →
      Paper.graphLaw N p {G |
        (∃ j ≤ ⌈1/(1-θ)⌉₊-1, ¬ Faithful N p U δ τ (referenceDataReal θ U N p)
          (rho p (actualState G c j))) ∨
        ((((⌈1/(1-θ)⌉₊-1:ℕ):ℝ)+1 = 1/(1-θ)) ∧
          ¬CriticalGain N (ζ/2) (rho p (actualState G c ((⌈1/(1-θ)⌉₊-1)+1))))}
        ≤ ENNReal.ofReal ε := faithful_trajectory hθlo hθhi hT

end MajorityDynamics.GraphProcess.FaithfulTrajectory

 /-- info: 'MajorityDynamics.GraphProcess.FaithfulTrajectory.faithful_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulTrajectory.faithful_prefix

 /-- info: 'MajorityDynamics.GraphProcess.FaithfulTrajectory.trajectory_of_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulTrajectory.trajectory_of_critical

 /-- info: 'MajorityDynamics.Paper.Expansion.expansion_of_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.Expansion.expansion_of_critical


/-- info: 'MajorityDynamics.GraphProcess.FaithfulTrajectory.faithful_trajectory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulTrajectory.faithful_trajectory
