import MajorityDynamics.GraphProcess.RowExactTotals.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Increasing the literal Gamma constant enlarges its good event. -/
theorem gamma_mono {π : V → History (n+1)}
    {m : History (n+1) → History (n+1) → ℤ} {C D p : ℝ}
    (hCD : C ≤ D) {d : RowArray.Ambient π} (hd : RowArray.Gamma π m C p d) :
    RowArray.Gamma π m D p d := fun s t => (hd s t).trans hCD

theorem gamma_event_mono (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) {C D p : ℝ} (hCD : C ≤ D) :
    {d | RowArray.Gamma π m C p d} ⊆ {d | RowArray.Gamma π m D p d} :=
  fun _ hd => gamma_mono hCD hd

theorem gamma_failure_mono (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) {C D p : ℝ} (hCD : C ≤ D)
    (μ : Measure (RowArray.Ambient π)) [IsFiniteMeasure μ] :
    μ.real {d | ¬ RowArray.Gamma π m D p d} ≤
      μ.real {d | ¬ RowArray.Gamma π m C p d} :=
  measureReal_mono (fun _ hd hc => hd (gamma_mono hCD hc))

theorem actual_gamma_failure_mono (π : V → History (n+1))
    {C D p : ℝ} (hCD : C ≤ D)
    (μ : Measure (RowArray.Ambient π)) [IsFiniteMeasure μ] :
    μ.real {d | ¬ RowArray.Gamma π (RowArray.totals d) D p d} ≤
      μ.real {d | ¬ RowArray.Gamma π (RowArray.totals d) C p d} :=
  measureReal_mono (fun _ hd hc => hd (gamma_mono hCD hc))

/-- On the exact-total event the original empirical and prescribed centers coincide. -/
theorem conditioned_gamma_eq (y : Local.CoarseData V n) (C p : ℝ)
    (μ : Measure (RowArray.Ambient y.part)) :
    (cond μ (RowArray.exactTotals y.part y.edge)).real
      {d | ¬ RowArray.Gamma y.part y.edge C p d} =
    (cond μ (RowArray.exactTotals y.part y.edge)).real
      {d | ¬ RowArray.Gamma y.part (RowArray.totals d) C p d} := by
  rw [RowExactTotals.conditioned_real_eq_div μ _ _ (Set.to_countable _).measurableSet,
    RowExactTotals.conditioned_real_eq_div μ _ _ (Set.to_countable _).measurableSet]
  congr 2
  ext d
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨he,hg⟩
  · exact ⟨he, by simpa only [show RowArray.totals d = y.edge from he] using hg⟩
  · exact ⟨he, by simpa only [show RowArray.totals d = y.edge from he] using hg⟩

/-- The third law is exactly simultaneous original history, kappa, and totals. -/
theorem triple_conditioning (y : Local.CoarseData V n) (q : Local.Tilt n) (p : ℝ) :
    cond (cond (RowConcentration.conditionedLaw y q)
      (RowArray.exactTotals y.part y.edge)) {d | RowArray.Regular p d} =
    cond (RowArray.law y.part q)
      (RowArray.history y.part ∩ {d | RowArray.Regular p d} ∩
        RowArray.exactTotals y.part y.edge) := by
  rw [RowExactTotals.iterated_history_totals y q,
    cond_cond_eq_cond_inter (Set.to_countable _).measurableSet
      (Set.to_countable _).measurableSet]
  congr 1
  ext d
  simp only [Set.mem_inter_iff]
  tauto

/-- A complement bound gives a real lower bound for the original good event. -/
theorem good_mass_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    {ε : ℝ} (h : μ.real Eᶜ ≤ ε) : 1-ε ≤ μ.real E := by
  rw [probReal_compl_eq_one_sub hE] at h
  linarith

/-- Conditioning on an event of mass at least one half loses at most a factor two. -/
theorem conditioned_failure_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E F : Set Ω) (hF : MeasurableSet F)
    (hE : (1:ℝ)/2 ≤ μ.real E) :
    (cond μ E).real F ≤ 2*μ.real F := by
  calc
    _ ≤ μ.real F / μ.real E := RowExactTotals.conditioned_real_le_div μ E F hF
    _ ≤ μ.real F / ((1:ℝ)/2) :=
      div_le_div_of_nonneg_left measureReal_nonneg (by norm_num) hE
    _ = _ := by ring

theorem gamma_regular_failure_le (y : Local.CoarseData V n) (C p : ℝ)
    (μ : Measure (RowArray.Ambient y.part)) [IsFiniteMeasure μ] :
    μ.real {d | ¬ (RowArray.Gamma y.part y.edge C p d ∧ RowArray.Regular p d)} ≤
      μ.real {d | ¬ RowArray.Gamma y.part y.edge C p d} +
      μ.real {d | ¬ RowArray.Regular p d} := by
  have he : {d | ¬ (RowArray.Gamma y.part y.edge C p d ∧ RowArray.Regular p d)} =
      {d | ¬ RowArray.Gamma y.part y.edge C p d} ∪ {d | ¬ RowArray.Regular p d} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [he]
  exact measureReal_union_le _ _

end MajorityDynamics.GraphProcess.RowGamma
