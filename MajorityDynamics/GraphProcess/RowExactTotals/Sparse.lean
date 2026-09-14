import MajorityDynamics.GraphProcess.RowExactTotals.ExactTotals
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Sparse
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Actual history-conditioned exact-total atoms on the sparse range. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal Idealized.RowLimits Probability.ConditionedBinomialFourier
universe u

theorem eventually_absorb_constant_sparse {θ T c : ℝ}
    (_hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      0 < (N : ℝ)^2*p ∧ ∀ a : ℝ,
        ((N : ℝ)^2*p)^(-(a+1)) ≤ c*((N : ℝ)^2*p)^(-a) := by
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L := c⁻¹) (inv_pos.mpr hc) (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨N₀, ?_⟩
  intro N hN p hlo hhi
  obtain ⟨hNr,hp,hN1,hmean,_⟩ := h₀ N hN p hlo hhi
  have hx : 0 < (N : ℝ)^2*p := by positivity
  refine ⟨hx, fun a => absorb_constant hx hc ?_⟩
  have hh := mul_le_mul_of_nonneg_left hN1 (mul_pos hp hNr).le
  nlinarith

theorem uniform_block_local_clt_sparse (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (n : ℕ) (T : ℝ) (hT : 1 < T) (φ : ℝ) (s : History (n+1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V],
      Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      IsProbabilityMeasure (Local.rowCondition y.sizes q s) ∧
      IsProbabilityMeasure (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)) ∧
      c*((N : ℝ)^2*p)^(-(Fintype.card (History (n+1)) : ℝ)/2) ≤
        (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)).real
          {x | ∀ t, (∑ j, (x j t : ℤ)) = y.edge s t} := by
  have hT0 : 0 < T := by linarith
  have h2T : 1 < 2*T := by linarith
  obtain ⟨c,hc,N₁,h₁⟩ := Probability.ConditionedBinomialLocalCLT.uniform_local_clt_sparse
    θ hθlo hθhi (Fintype.card (Fin (n+1) → Bool)) (by exact Fintype.card_pos)
    n (historyIntegerMatrix s) (historyIntegerMatrix_orthogonal s) (historyStrict s) (2*T) h2T
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 2*T) (by positivity)
  refine ⟨c,hc,max N₁ N₂,?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hr := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hpLo : (2*T)⁻¹*(N : ℝ)^(-θ) < p := by
    exact (mul_le_mul_of_nonneg_right (inv_anti₀ hT0 (by linarith))
      (Real.rpow_nonneg hr.1.le _)).trans_lt hlo
  have hpHi : p < (2*T) * (N : ℝ)^(-(1/2 : ℝ)) := by
    exact hhi.trans_le (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr.1.le _))
  have hg := admissible_clt_geometry y q hT ha (by simpa [hcard] using hr.2.2.1)
    hr.2.1 hr.2.2.2.2 s
  rw [hcard] at hg
  obtain ⟨hρ,hcopy,hprob⟩ := h₁ N ((le_max_left _ _).trans hN) p hpLo hpHi
    (Local.trials y.sizes s) (q s) (y.sizes s) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1
    hg.2.2.2.2.1 hg.2.2.2.2.2
  rw [← rowCondition_eq_clt] at hρ hcopy hprob
  refine ⟨hρ,hcopy,?_⟩
  have hz (t : History (n+1)) : (y.edge s t : ℝ) =
      (y.sizes s : ℝ)*mean (Local.rowCondition y.sizes q s) t := by
    simpa only [Local.CoarseData.realEdges, Local.rowMean_eq_integral, mean] using
      (ha.solves s t).symm
  simpa only [History, Fintype.card_fin] using hprob (y.edge s) hz

theorem uniform_block_lower_sparse (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (n : ℕ) (T : ℝ) (hT : 1 < T) (φ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V],
      Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ s : History (n+1),
      IsProbabilityMeasure (Local.rowCondition y.sizes q s) ∧
      IsProbabilityMeasure (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)) ∧
      ((N : ℝ)^2*p)^(-((Fintype.card (History (n+1)) : ℝ)/2+1)) ≤
        (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)).real
          {x | ∀ t, (∑ j, (x j t : ℤ)) = y.edge s t} := by
  classical
  have hb (s : History (n+1)) : ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      IsProbabilityMeasure (Local.rowCondition y.sizes q s) ∧
      IsProbabilityMeasure (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)) ∧
      ((N : ℝ)^2*p)^(-((Fintype.card (History (n+1)) : ℝ)/2+1)) ≤
        (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)).real
          {x | ∀ t, (∑ j, (x j t : ℤ)) = y.edge s t} := by
    obtain ⟨c,hc,N₁,h₁⟩ := uniform_block_local_clt_sparse θ hθlo hθhi n T hT φ s
    obtain ⟨N₂,h₂⟩ := eventually_absorb_constant_sparse hθlo hθhi hT hc
    refine ⟨max N₁ N₂, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    have hclt := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q ha
    have habs := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
    refine ⟨hclt.1,hclt.2.1,?_⟩
    apply (habs.2 ((Fintype.card (History (n+1)) : ℝ)/2)).trans
    simpa only [neg_div] using hclt.2.2
  choose N₀ h₀ using hb
  refine ⟨Finset.univ.sup N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha s
  exact h₀ s N ((Finset.le_sup (f := N₀) (Finset.mem_univ s)).trans hN)
    V hcard p hlo hhi y q ha

theorem uniform_exact_total_lower_bound_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ((N : ℝ)^2*p)^(-(totalExponent n : ℝ)) ≤
        (cond (RowArray.law y.part q) (RowArray.history y.part)).real
          (RowArray.exactTotals y.part y.edge) := by
  obtain ⟨N₁,h₁⟩ := uniform_block_lower_sparse θ hθlo hθhi n T hT φ
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
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
theorem uniform_exact_totals_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      let μ := cond (RowArray.law y.part q) (RowArray.history y.part)
      let E := RowArray.exactTotals y.part y.edge
      IsProbabilityMeasure μ ∧ ((N : ℝ)^2*p)^(-(totalExponent n : ℝ)) ≤ μ.real E ∧
      0 < μ E ∧ IsProbabilityMeasure (cond μ E) ∧
      cond μ E = cond (RowArray.law y.part q) (RowArray.history y.part ∩ E) := by
  obtain ⟨N₁,h₁⟩ := uniform_exact_total_lower_bound_sparse n hθlo hθhi hT hφ
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
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
