import MajorityDynamics.GraphProcess.RowGamma.Shared
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics
import MajorityDynamics.GraphProcess.GammaNumerator.Sparse
import MajorityDynamics.GraphProcess.RowExactTotals.SparseConcentration
import MajorityDynamics.GraphProcess.RowConcentration.Sparse

/-! Original Gamma estimates with constants uniform over the sparse range. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
universe u

theorem uniform_second_moment_sparse {θ T φ : ℝ} (n : ℕ)
    (_hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ v t,
      Integrable (fun d : RowArray.Ambient y.part =>
        ((RowArray.values d v t : ℝ)-p*y.sizes t)^2/(p*N))
        (RowConcentration.conditionedLaw y q) ∧
      (∫ d, ((RowArray.values d v t : ℝ)-p*y.sizes t)^2/(p*N)
        ∂RowConcentration.conditionedLaw y q) ≤ secondMomentConstant T φ := by
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L := (2*T)^2) (by positivity) (U := 1) zero_lt_one (M := 2*T) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA v t
  have h := h₀ N hN p hlo hhi
  subst N
  exact finite_second_moment y q hT hφ h.2.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1
    (fun s => by simpa [div_eq_mul_inv, mul_comm] using hLA.sizes s)
    hLA.tilt hLA.conditioning v t

theorem uniform_history_gamma_sparse {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ C ≥ rowConstant T φ,
      (RowConcentration.conditionedLaw y q).real
        {d | ¬ RowArray.Gamma y.part (RowArray.totals d) C p d} ≤ (N : ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := uniform_second_moment_sparse n hθlo hθhi hT hφ
  obtain ⟨N₂,h₂⟩ := RowConcentration.uniform_degree_tail_sparse (A := A+1) n hθlo hθhi hT hφ
  obtain ⟨N₃,h₃⟩ := Numerics.eventually_clipped_tail
    ((Fintype.card (History (n+1)) : ℝ)^2) (A+1) (sq_nonneg _)
  obtain ⟨N₄,h₄⟩ := RowConcentration.eventually_tolerance_le_sparse hθlo hθhi hT
  refine ⟨max 2 (max N₁ (max N₂ (max N₃ N₄))), ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha C hC
  have hm := h₁ N (by omega) V hcard p hlo hhi y q ha
  have hd := h₂ N (by omega) V hcard p hlo hhi y q
    (fun s => by simpa only [← hcard, div_eq_mul_inv, mul_comm] using ha.sizes s)
    (fun s t => by simpa only [← hcard] using ha.tilt s t) ha.conditioning
  have ht := h₃ N (by omega)
  have hr := h₄ N (by omega) p hlo hhi
  have hcardpos : 0 < Fintype.card V := by rw [hcard]; omega
  have hlog : 1 ≤ Real.log (Fintype.card V) := by rw [hcard]; exact hr.2.2.1
  have hint : ∀ v t, Integrable (normalizedSquare p y.part v t)
      (RowConcentration.conditionedLaw y q) := by
    intro v t
    change Integrable (fun d => ((RowArray.values d v t : ℝ)-p*y.sizes t)^2 /
      (p*Fintype.card V)) (RowConcentration.conditionedLaw y q)
    rw [hcard]
    exact (hm v t).1
  have hexp : ∀ v t, (∫ d, normalizedSquare p y.part v t d
      ∂RowConcentration.conditionedLaw y q) ≤ secondMomentConstant T φ := by
    intro v t
    simpa only [normalizedSquare, Local.CoarseData.sizes, hcard] using (hm v t).2
  have hg := gamma_failure y q hφ ha.conditioning hr.1
    (secondMomentConstant_nonneg hφ) hcardpos hlog hint hexp
  rw [hcard] at hg
  let := RowConcentration.conditioned_probability y q hφ ha.conditioning
  apply (actual_gamma_failure_mono y.part hC _).trans
  change (RowConcentration.conditionedLaw y q).real
    {d | ¬ RowArray.Gamma y.part (RowArray.totals d) (secondMomentConstant T φ+1) p d} ≤ _
  exact hg.trans ((add_le_add hd ht).trans (by
    simpa only [two_mul] using Numerics.absorb_two (show 2 ≤ N by omega) A))

theorem uniform_complete_sparse {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ C ≥ rowConstant T φ, Conclusion y q C p A N := by
  obtain ⟨N₁,h₁⟩ := uniform_history_gamma_sparse
    (A := max A 1+1+2*(RowExactTotals.totalExponent n : ℝ)) n hθlo hθhi hT hφ
  obtain ⟨N₂,h₂⟩ := RowExactTotals.uniform_exact_total_lower_bound_sparse n hθlo hθhi hT hφ
  obtain ⟨N₃,h₃⟩ := RowExactTotals.uniform_binomial_regularity_sparse
    (A := max A 1+1) n hθlo hθhi hT hφ
  obtain ⟨N₄,h₄⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
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
theorem exists_uniform_constant_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ C ≥ C₀, Conclusion y q C p A N := by
  exact ⟨rowConstant T φ,rowConstant_ge_one hφ,
    fun A _ => uniform_complete_sparse (A := A) n hθlo hθhi hT hφ⟩

theorem uniform_shared_constant_sparse {θ T φ K : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∃ hp : 0 < p ∧ p < 1,
      Conclusion y q C p A N ∧
      (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real {G |
        ¬ RowArray.Gamma y.part (RowArray.totals (RowArray.graphArray y.part G)) C p
          (RowArray.graphArray y.part G) ∧ RowArray.Regular p (RowArray.graphArray y.part G)} ≤
          Real.exp (-K*N) ∧
      (((SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).map
        (RowArray.graphArray y.part)).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d ∧ d ∈ RowArray.history y.part ∧
          RowArray.Regular p d ∧ d ∈ RowArray.exactTotals y.part y.edge}) ≤ Real.exp (-K*N) := by
  classical
  obtain ⟨Cg,hCg,Ng,hg⟩ := GammaNumerator.uniform_numerator_real_sparse n hθlo hθhi hT hK
  refine ⟨max (rowConstant T φ) Cg,(rowConstant_ge_one hφ).trans (le_max_left _ _),?_⟩
  intro A _
  obtain ⟨Nr,hr⟩ := uniform_complete_sparse (A := A) n hθlo hθhi hT hφ
  refine ⟨max Ng Nr,?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  obtain ⟨hp,hgraph⟩ := hg N (by omega) V hcard p hlo hhi
  have hgg := hgraph y.part (fun s => by
    simpa only [← hcard, Local.CoarseData.sizes, div_eq_mul_inv, mul_comm] using ha.sizes s)
  refine ⟨hp,hr N (by omega) V hcard p hlo hhi y q ha _ (le_max_left _ _),?_,?_⟩
  · apply le_trans (measureReal_mono (show
        {G | ¬ RowArray.Gamma y.part (RowArray.totals (RowArray.graphArray y.part G))
          (max (rowConstant T φ) Cg) p (RowArray.graphArray y.part G) ∧
          RowArray.Regular p (RowArray.graphArray y.part G)} ⊆
        {G | ¬ RowArray.Gamma y.part (RowArray.totals (RowArray.graphArray y.part G))
          Cg p (RowArray.graphArray y.part G) ∧ RowArray.Regular p (RowArray.graphArray y.part G)}
        from fun _ hd => ⟨fun hc => hd.1 (gamma_mono (le_max_right _ _) hc),hd.2⟩)) hgg.1
  · apply le_trans (measureReal_mono (show
        {d | ¬ RowArray.Gamma y.part y.edge (max (rowConstant T φ) Cg) p d ∧
          d ∈ RowArray.history y.part ∧ RowArray.Regular p d ∧
          d ∈ RowArray.exactTotals y.part y.edge} ⊆
        {d | ¬ RowArray.Gamma y.part y.edge Cg p d ∧ d ∈ RowArray.history y.part ∧
          RowArray.Regular p d ∧ d ∈ RowArray.exactTotals y.part y.edge}
        from fun _ hd => ⟨fun hc => hd.1 (gamma_mono (le_max_right _ _) hc),hd.2⟩)) (hgg.2.2 y.edge)

end MajorityDynamics.GraphProcess.RowGamma

