import MajorityDynamics.Idealized.PerturbedEvolution.Basic
import MajorityDynamics.Idealized.PerturbedEvolution.TemplateEdgesUniform

/-! Both exact template estimates, with one common constant and exponent. -/
noncomputable section
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

theorem template_spec (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
        TemplateConclusion N p a (naturalSizes η) (realEdges e) q τ K (tiltRate θ δ n) := by
  obtain ⟨Ks, hKs, Ns, hNs, hs⟩ := template_sizes_spec θ T δ hθlo hθhi hT hδ n ell hell hk
  obtain ⟨Ke, hKe, Ne, _, he⟩ := template_edges_spec θ T δ hθlo hθhi hT hδ n ell hell hk
  refine ⟨max Ks Ke, hKs.trans_le (le_max_left _ _), max Ns Ne,
    hNs.trans (le_max_left _ _), ?_⟩
  intro N hN p hp a ha τ hτ hτT η e hf q hq
  have hsizes := hs N ((le_max_left _ _).trans hN) p hp a ha τ hτ hτT η e hf q hq
  have hedges := he N ((le_max_right _ _).trans hN) p hp a ha τ hτ hτT η e hf q hq
  refine ⟨fun u => (hsizes u).trans ?_, fun u v => (hedges u v).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Ks Ke) (sizeScale_nonneg _ _ _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have hp0 := p.property.1
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right Ks Ke) (betaScale_nonneg _ _ _))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _)) hp0.le

end MajorityDynamics.Idealized.PerturbedEvolution
