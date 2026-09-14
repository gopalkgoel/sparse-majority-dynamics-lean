import MajorityDynamics.Probability.RandomOpinionsReduction.Transport

/-! # Corollary 1.2, conditional on the exact fixed-lead theorem

`random_opinions_of_main`, `random_opinions_real_of_main`, and
`random_opinions_finite_of_main` are proved in the imported modules.
This final adapter combines arbitrary finite vertices with real densities.
-/
noncomputable section
open Filter
namespace MajorityDynamics.Probability.RandomOpinionsReduction

def RandomOpinionsFiniteRealTheorem : Prop :=
  ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Type) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
        ∃ hp : 0 < p ∧ p < 1,
          jointLawV V ⟨p, hp.1.le, hp.2.le⟩ (consensusEventV V θ)ᶜ ≤ ENNReal.ofReal ε

theorem random_opinions_finite_real_of_main (main : Paper.MainTheorem) :
    RandomOpinionsFiniteRealTheorem := by
  intro θ T hlo hhi hT ε hε
  obtain ⟨M,hM⟩ := random_opinions_finite_of_main main θ T hlo hhi hT ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (eventually_density_in_unitInterval θ T (by linarith) (by linarith))
  refine ⟨max M K, ?_⟩
  intro N hN V _ hV p hp₀ hp₁
  have hp := hK N ((le_max_right _ _).trans hN) p hp₀ hp₁
  exact ⟨hp, hM N ((le_max_left _ _).trans hN) V hV ⟨p, hp.1.le, hp.2.le⟩ ⟨hp₀, hp₁⟩⟩

end MajorityDynamics.Probability.RandomOpinionsReduction
