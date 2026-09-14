import MajorityDynamics.GraphProcess.RowExactTotals.BlockBounds
import MajorityDynamics.GraphProcess.RowExactTotals.Factorization
import MajorityDynamics.GraphProcess.RowExactTotals.Conditioning

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal Probability.ConditionedBinomialFourier
universe u

/-- Full original Appendix B.5: the actual ordered-total event has the paper's
explicit polynomial lower bound, uniformly over locally admissible data. -/
theorem uniform_exact_total_lower_bound {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ((N : ℝ)^2*p)^(-(totalExponent n : ℝ)) ≤
        (cond (RowArray.law y.part q) (RowArray.history y.part)).real
          (RowArray.exactTotals y.part y.edge) := by
  obtain ⟨N₁,h₁⟩ := uniform_block_lower θ hθlo hθhi n T hT φ
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hb := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q ha
  have hr := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hx : 0 < (N : ℝ)^2*p := mul_pos (sq_pos_of_pos hr.1) hr.2.1
  rw [exactTotals_real_factorization y q
    (RowConcentration.row_history_pos y q hφ ha.conditioning), ← product_power n hx]
  exact Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg hx.le _) (fun s _ => (hb s).2.2)

/-- B.5 additionally certifies both actual conditional probability measures,
positivity of the exact-total event, and literal simultaneous conditioning. -/
theorem uniform_exact_totals {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      let μ := cond (RowArray.law y.part q) (RowArray.history y.part)
      let E := RowArray.exactTotals y.part y.edge
      IsProbabilityMeasure μ ∧ ((N : ℝ)^2*p)^(-(totalExponent n : ℝ)) ≤ μ.real E ∧
      0 < μ E ∧ IsProbabilityMeasure (cond μ E) ∧
      cond μ E = cond (RowArray.law y.part q) (RowArray.history y.part ∩ E) := by
  obtain ⟨N₁,h₁⟩ := uniform_exact_total_lower_bound n hθlo hθhi hT hφ
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hb := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q ha
  have hr := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hx : 0 < (N : ℝ)^2*p := mul_pos (sq_pos_of_pos hr.1) hr.2.1
  have hpos := (Real.rpow_pos_of_pos hx (-(totalExponent n : ℝ))).trans_le hb
  let μ := cond (RowArray.law y.part q) (RowArray.history y.part)
  have : IsProbabilityMeasure μ := RowConcentration.conditioned_probability y q hφ ha.conditioning
  have he : 0 < μ (RowArray.exactTotals y.part y.edge) :=
    pos_iff_ne_zero.mpr (ENNReal.toReal_ne_zero.mp hpos.ne').1
  exact ⟨inferInstance,hb,he,cond_isProbabilityMeasure he.ne',iterated_history_totals y q⟩

end MajorityDynamics.GraphProcess.RowExactTotals
