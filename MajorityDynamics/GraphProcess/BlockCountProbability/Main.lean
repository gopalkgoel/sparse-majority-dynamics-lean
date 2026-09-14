import MajorityDynamics.GraphProcess.BlockCountProbability.Components
import MajorityDynamics.GraphProcess.BlockCountProbability.Finite
import MajorityDynamics.GraphProcess.BlockCountProbability.Product

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.BlockCountProbability
open Universal
universe u

/-- B.3 Step 1 (`eq:m-lower`) on the actual random graph. Constants and the
threshold precede every varying datum; only the original three hypotheses
remain. -/
theorem count_event_lower {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N)) →
      Real.exp (-C*N) ≤ (SimpleGraph.binomialRandom V p).real
        (GraphicalArray.fixedCountFamily y.part y.edge) := by
  obtain ⟨C, hC, N₀, h₀⟩ := uniform_component_lower n hθlo hθhi hT
  refine ⟨C*factorCount n, mul_pos hC (by exact_mod_cast factorCount_pos n), N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  obtain ⟨hi, hc⟩ := h₀ N hN V hcard p hlo hhi y hsizes hcounts
  rw [exact_factorization p y]
  exact product_lower n N C _ _ hi (fun z => hc z.val.1 z.val.2 (ne_of_lt z.property))

end MajorityDynamics.GraphProcess.BlockCountProbability
