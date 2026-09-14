import MajorityDynamics.GraphProcess.RowExactTotals.ExactTotals

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal
universe u

/-- The original R1/R2/R3 event keeps every prescribed error scale after
conditioning on the literal ordered totals, with every polynomial decay rate. -/
theorem uniform_conditioned_concentration {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      (cond (cond (RowArray.law y.part q) (RowArray.history y.part))
        (RowArray.exactTotals y.part y.edge)).real
          {d | ¬ RowConcentration.Good y p q d} ≤ (N : ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := uniform_exact_total_lower_bound n hθlo hθhi hT hφ
  obtain ⟨N₂,h₂⟩ := RowConcentration.uniform_concentration
    (A := A+2*(totalExponent n : ℝ)) n hθlo hθhi hT hφ
  obtain ⟨N₃,h₃⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have he := h₁ N (by omega) V hcard p hlo hhi y q ha
  have hc := h₂ N (by omega) V hcard p hlo hhi y q
    (fun s => by simpa only [← hcard, div_eq_mul_inv, mul_comm] using ha.sizes s)
    (fun s t => by simpa only [← hcard] using ha.tilt s t) ha.conditioning
  have hr := h₃ N (by omega) p hlo hhi
  have := RowConcentration.conditioned_probability y q hφ ha.conditioning
  exact conditioned_failure_power (RowConcentration.conditionedLaw y q)
    (RowArray.exactTotals y.part y.edge) {d | ¬ RowConcentration.Good y p q d}
    (Set.to_countable _).measurableSet hr.1 hr.2.1 hr.2.2.2.2 (Nat.cast_nonneg _) he hc

/-- Full original Appendix B.6, simultaneously before and after exact-total
conditioning. Both failures are bounded by every fixed real power. -/
theorem uniform_binomial_regularity {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      let μ := cond (RowArray.law y.part q) (RowArray.history y.part)
      μ.real {d | ¬ RowArray.Regular p d} ≤ (N : ℝ)^(-A) ∧
      (cond μ (RowArray.exactTotals y.part y.edge)).real
        {d | ¬ RowArray.Regular p d} ≤ (N : ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := uniform_history_regularity (A := A) n hθlo hθhi hT hφ
  obtain ⟨N₂,h₂⟩ := uniform_history_regularity (A := A+2*(totalExponent n : ℝ))
    n hθlo hθhi hT hφ
  obtain ⟨N₃,h₃⟩ := uniform_exact_total_lower_bound n hθlo hθhi hT hφ
  obtain ⟨N₄,h₄⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨max N₁ (max N₂ (max N₃ N₄)), ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hh := h₁ N (by omega) V hcard p hlo hhi y q ha
  have hc := h₂ N (by omega) V hcard p hlo hhi y q ha
  have he := h₃ N (by omega) V hcard p hlo hhi y q ha
  have hr := h₄ N (by omega) p hlo hhi
  have := RowConcentration.conditioned_probability y q hφ ha.conditioning
  exact ⟨hh,conditioned_failure_power (RowConcentration.conditionedLaw y q)
    (RowArray.exactTotals y.part y.edge) {d | ¬ RowArray.Regular p d}
    (Set.to_countable _).measurableSet hr.1 hr.2.1 hr.2.2.2.2 (Nat.cast_nonneg _) he hc⟩

end MajorityDynamics.GraphProcess.RowExactTotals
