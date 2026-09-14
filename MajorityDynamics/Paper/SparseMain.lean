import MajorityDynamics.Paper.UniformExpansion
import MajorityDynamics.Paper.UniformAssembly

noncomputable section
namespace MajorityDynamics.Paper.UniformInternal

lemma sparse_main : SparseMainTheorem :=
  uniform_main_of_expansion uniform_expansion

/-- The endpoints of the density interval are included by enlarging the fixed
comparison constant, without changing the bias interval or convergence day. -/
lemma sparse_main_closed_density :
    ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
          T⁻¹*(N:ℝ)^(-θ) ≤ (p:ℝ) → (p:ℝ) ≤ T*(N:ℝ)^(-(1/2:ℝ)) →
          T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
          graphLaw N p (uniformSuccessEvent θ c)ᶜ ≤ ENNReal.ofReal ε := by
  intro θ T hθlo hθhi hT ε hε
  have hT0 : 0 < T := by linarith
  have hTT : T < 2*T := by linarith
  have hi : (2*T)⁻¹ < T⁻¹ := (inv_lt_inv₀ (by positivity) hT0).mpr hTT
  obtain ⟨N₀,hmain⟩ := sparse_main θ (2*T) hθlo hθhi (by linarith) ε hε
  refine ⟨max N₀ 1,?_⟩
  intro N hN p τ c hlo hhi hτ hτT hc
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply hmain N (by omega) p τ c ?_ (hi.le.trans hτ) (hτT.trans hTT.le) hc
  exact ⟨(mul_lt_mul_of_pos_right hi (Real.rpow_pos_of_pos hn _)).trans_le hlo,
    hhi.trans_lt (mul_lt_mul_of_pos_right hTT (Real.rpow_pos_of_pos hn _))⟩

end MajorityDynamics.Paper.UniformInternal
