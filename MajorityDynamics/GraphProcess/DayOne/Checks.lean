import MajorityDynamics.GraphProcess.DayOne.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.GraphProcess.DayOne
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedEvolution

example : DayOneTheorem := day_one
example :
∀ θ : ℝ, 1/2 < θ → θ < 1 → ∀ T : ℝ, 1 < T →
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
  ∃ hp : 0 < p ∧ p < 1,
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ (V : Type*) [Fintype V], Fintype.card V = N →
    ∀ c : V → Bool,
      (Finset.univ.filter fun v => c v = false).card = N/2 + ⌊τ*Real.sqrt N⌋₊ →
    (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real
      {G | ¬Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
        (CoarseKernel.actualCoarse p G c 0)} ≤ ε ∧
    1-ε ≤ (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real
      {G | Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
        (CoarseKernel.actualCoarse p G c 0)} := day_one

end MajorityDynamics.GraphProcess.DayOne

/-- info: 'MajorityDynamics.GraphProcess.DayOne.day_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.DayOne.day_one

/-- info: 'MajorityDynamics.GraphProcess.DayOne.initial_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.DayOne.initial_faithful
