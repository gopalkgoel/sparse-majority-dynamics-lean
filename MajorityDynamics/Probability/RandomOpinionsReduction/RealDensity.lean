import MajorityDynamics.Probability.RandomOpinionsReduction.Reduction

noncomputable section
open Filter
open scoped Topology
namespace MajorityDynamics.Probability.RandomOpinionsReduction

theorem eventually_density_in_unitInterval (θ T : ℝ) (hθ : 0 < θ) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-θ) → 0 < p ∧ p < 1 := by
  have ht : Tendsto (fun N : ℕ => T*(N : ℝ)^(-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul T
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop (0 : ℕ)]
    with N hu hN p hlo hhi
  exact ⟨(mul_pos (inv_pos.mpr hT) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)).trans hlo,
    hhi.trans hu⟩

def RandomOpinionsRealTheorem : Prop :=
  ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∃ hp : 0 < p ∧ p < 1,
        jointLaw N ⟨p, hp.1.le, hp.2.le⟩ (consensusEvent N θ)ᶜ ≤ ENNReal.ofReal ε

theorem random_opinions_real_of_main (main : Paper.MainTheorem) : RandomOpinionsRealTheorem := by
  intro θ T hlo hhi hT ε hε
  obtain ⟨M, hM⟩ := random_opinions_of_main main θ T hlo hhi hT ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_density_in_unitInterval θ T (by linarith) (by linarith))
  refine ⟨max M K, ?_⟩
  intro N hN p hp₀ hp₁
  have hp := hK N ((le_max_right _ _).trans hN) p hp₀ hp₁
  exact ⟨hp, hM N ((le_max_left _ _).trans hN) ⟨p, hp.1.le, hp.2.le⟩ ⟨hp₀, hp₁⟩⟩

end MajorityDynamics.Probability.RandomOpinionsReduction
