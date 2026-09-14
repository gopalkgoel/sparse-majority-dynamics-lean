import MajorityDynamics.GraphProcess.RowGamma.History
import MajorityDynamics.GraphProcess.RowGamma.Assembly

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
universe u

/-- Complete original-input direct B.4 row regularity, including actual
normalization and the Gamma-intersect-kappa denominator. Every larger constant
works at the same threshold. No graph enumeration is used. -/
theorem uniform_complete {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ C ≥ rowConstant T φ, Conclusion y q C p A N := by
  obtain ⟨N₁,h₁⟩ := uniform_history_gamma
    (A := max A 1+1+2*(RowExactTotals.totalExponent n : ℝ)) n hθlo hθhi hT hφ
  obtain ⟨N₂,h₂⟩ := RowExactTotals.uniform_exact_total_lower_bound n hθlo hθhi hT hφ
  obtain ⟨N₃,h₃⟩ := RowExactTotals.uniform_binomial_regularity
    (A := max A 1+1) n hθlo hθhi hT hφ
  obtain ⟨N₄,h₄⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨max 2 (max N₁ (max N₂ (max N₃ N₄))), ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha C hC
  have hg := h₁ N (by omega) V hcard p hlo hhi y q ha C hC
  have he := h₂ N (by omega) V hcard p hlo hhi y q ha
  have hk := (h₃ N (by omega) V hcard p hlo hhi y q ha).2
  have hr := h₄ N (by omega) p hlo hhi
  have hh : 0 < (RowArray.law y.part q).real (RowArray.history y.part) := by
    have hx := RowConcentration.history_pos y q hφ ha.conditioning
    exact ENNReal.toReal_pos hx.ne' (measure_ne_top _ _)
  exact conclusion_of_bounds y q (by omega) hr.2.1 hr.2.2.2.2
    (RowConcentration.conditioned_probability y q hφ ha.conditioning) hh he hg hk

/-- Explicit quantifier order: one Gamma constant is selected before every
requested positive decay exponent, and before all varying original data. -/
theorem exists_uniform_constant {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ C ≥ C₀, Conclusion y q C p A N := by
  exact ⟨rowConstant T φ,rowConstant_ge_one hφ,
    fun A _ => uniform_complete (A := A) n hθlo hθhi hT hφ⟩

end MajorityDynamics.GraphProcess.RowGamma
