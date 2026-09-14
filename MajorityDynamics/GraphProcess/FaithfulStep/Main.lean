import MajorityDynamics.GraphProcess.FaithfulStep.Basic
import MajorityDynamics.GraphProcess.FaithfulStep.Rates

noncomputable section
open Filter Topology
namespace MajorityDynamics.GraphProcess.FaithfulStep
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedTilt
open Idealized.PerturbedEvolution

/-- Full Proposition 5.6. The constants are those of the complete 5.4 theorem;
the inclusion holds for every fixed local-theorem constant C. -/
def FaithfulInclusionTheorem : Prop :=
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
      Faithful N p (2*T₁) (min δ₁ ((1-θ)/8)) τ (referenceDataReal θ T N p) z

theorem faithful_inclusion : FaithfulInclusionTheorem := by
  intro θ hθlo hθhi n hk T δ hT hδ
  obtain ⟨T₁,hT₁,δ₁,hδ₁,φ₁,hφ₁,hφ₁hi,N₁,hN₁,hevol⟩ :=
    perturbed_evolution θ hθlo hθhi n hk T δ hT hδ
  refine ⟨T₁,hT₁,δ₁,hδ₁,φ₁,hφ₁,hφ₁hi,?_⟩
  intro C hC
  have hT₁0 : 0 < T₁ := by linarith
  obtain ⟨N₂,hN₂⟩ := Filter.eventually_atTop.mp
    (eventually_local_errors hθlo hθhi hT hT₁0 hC
      (min_le_right δ₁ ((1-θ)/8)))
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro N hN p hlo hhi
  obtain ⟨hp,ha,hy⟩ := hevol N ((le_max_left _ _).trans hN) p hlo hhi
  refine ⟨hp,ha,?_⟩
  intro τ hτlo hτhi V inst hcard y hf
  have hev := hy τ hτlo hτhi V hcard y hf
  refine ⟨hev,?_⟩
  intro q hq z hz
  have hsc := hN₂ N ((le_max_right _ _).trans hN) ⟨p,hp⟩ ⟨hlo,hhi⟩ n
  exact local_success_faithful (hN₁.trans ((le_max_left _ _).trans hN)) hcard hp.1.le
    hT₁0.le (min_le_left _ _) hsc.1 hsc.2 (hev.template q hq) hz

end MajorityDynamics.GraphProcess.FaithfulStep
