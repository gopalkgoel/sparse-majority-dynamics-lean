import MajorityDynamics.GraphProcess.FaithfulStep.Main

noncomputable section
namespace MajorityDynamics.GraphProcess.FaithfulStep
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedTilt
open Idealized.PerturbedEvolution

example : FaithfulInclusionTheorem := faithful_inclusion

example :
∀ θ : ℝ, 1/2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ)+1 < 1/(1-θ) →
  ∀ T δ : ℝ, 1 < T → 0 < δ →
  ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧
  ∃ φ₁ : ℝ, 0 < φ₁ ∧ φ₁ < 1/2 ∧
  ∀ C : ℝ, 0 ≤ C → ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
  ∃ hp : 0 < p ∧ p < 1,
    Process.Specification N ⟨p,hp⟩ (responseHorizon θ) (processExponent θ T)
      (referenceDataReal θ T N p) ∧
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ (V : Type*) [Fintype V], Fintype.card V = N →
    ∀ y : Local.CoarseData V n,
      Faithful N p T δ τ (referenceDataReal θ T N p) y →
      EvolutionConclusion N ⟨p,hp⟩ (referenceDataReal θ T N p) y τ T₁ δ₁ φ₁ ∧
      ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
      ∀ z : Local.CoarseData V (n+1), LocalTransition.LocalSuccess y q p C z →
      Faithful N p (2*T₁) (min δ₁ ((1-θ)/8)) τ (referenceDataReal θ T N p) z := faithful_inclusion

end MajorityDynamics.GraphProcess.FaithfulStep

/-- info: 'MajorityDynamics.GraphProcess.FaithfulStep.faithful_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulStep.faithful_inclusion

/-- info: 'MajorityDynamics.GraphProcess.FaithfulStep.local_success_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulStep.local_success_faithful
