import MajorityDynamics.GraphProcess.LocalTransition.Algebra
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

noncomputable section
namespace MajorityDynamics.GraphProcess.LocalTransition

theorem uniform_numerical_regime_sparse {θ T : ℝ}
    (_hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      2 ≤ N ∧ 0 < p ∧ 0 ≤ Real.log (N : ℝ) ∧
        2 ≤ (p*N)^((1:ℝ)/14) := by
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT
    (L := (2:ℝ)^(14:ℝ)) (by positivity) (U := 1) zero_lt_one
    (M := 2) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN p hlo hhi
  obtain ⟨hN0,hp,hN2,hx,_⟩ := h₀ N hN p hlo hhi
  refine ⟨by exact_mod_cast hN2, hp, Real.log_nonneg (by linarith), ?_⟩
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^(14:ℝ)) hx
    (by norm_num : (0:ℝ) ≤ 1/14)
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  norm_num at hh
  exact hh

end MajorityDynamics.GraphProcess.LocalTransition
