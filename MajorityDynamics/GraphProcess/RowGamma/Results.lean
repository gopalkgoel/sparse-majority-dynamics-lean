import MajorityDynamics.GraphProcess.RowGamma.Conditioning

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Closed actual-law output of direct row Gamma concentration. The same constant
appears before and after the original conditioning events. -/
structure Conclusion (y : Local.CoarseData V n) (q : Local.Tilt n)
    (C p A : ℝ) (N : ℕ) : Prop where
  history_probability : IsProbabilityMeasure (RowConcentration.conditionedLaw y q)
  history_positive : 0 < (RowArray.law y.part q).real (RowArray.history y.part)
  totals_lower : ((N : ℝ)^2*p)^(-(RowExactTotals.totalExponent n : ℝ)) ≤
    (RowConcentration.conditionedLaw y q).real (RowArray.exactTotals y.part y.edge)
  totals_positive : 0 < (RowConcentration.conditionedLaw y q).real
    (RowArray.exactTotals y.part y.edge)
  totals_probability : IsProbabilityMeasure
    (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge))
  regular_lower : (1:ℝ)/2 ≤
    (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge)).real
      {d | RowArray.Regular p d}
  triple_probability : IsProbabilityMeasure
    (cond (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge))
      {d | RowArray.Regular p d})
  triple_identity :
    cond (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge))
      {d | RowArray.Regular p d} = cond (RowArray.law y.part q)
        (RowArray.history y.part ∩ {d | RowArray.Regular p d} ∩ RowArray.exactTotals y.part y.edge)
  history_failure : (RowConcentration.conditionedLaw y q).real
    {d | ¬ RowArray.Gamma y.part (RowArray.totals d) C p d} ≤ (N : ℝ)^(-A)
  totals_failure :
    (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge)).real
      {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ (N : ℝ)^(-A)
  triple_failure :
    (cond (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge))
      {d | RowArray.Regular p d}).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ (N : ℝ)^(-A)
  joint_failure :
    (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge)).real
      {d | ¬ (RowArray.Gamma y.part y.edge C p d ∧ RowArray.Regular p d)} ≤ (N : ℝ)^(-A)
  joint_lower : (1:ℝ)/2 ≤
    (cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge)).real
      {d | RowArray.Gamma y.part y.edge C p d ∧ RowArray.Regular p d}

/-- The same threshold works for every larger Gamma constant. -/
theorem Conclusion.mono {y : Local.CoarseData V n} {q : Local.Tilt n}
    {C D p A : ℝ} {N : ℕ} (h : Conclusion y q C p A N) (hCD : C ≤ D) :
    Conclusion y q D p A N := by
  let := h.history_probability
  let := h.totals_probability
  let := h.triple_probability
  refine { history_probability := h.history_probability
           history_positive := h.history_positive
           totals_lower := h.totals_lower
           totals_positive := h.totals_positive
           totals_probability := h.totals_probability
           regular_lower := h.regular_lower
           triple_probability := h.triple_probability
           triple_identity := h.triple_identity
           history_failure := (actual_gamma_failure_mono y.part hCD _).trans h.history_failure
           totals_failure := (gamma_failure_mono y.part y.edge hCD _).trans h.totals_failure
           triple_failure := (gamma_failure_mono y.part y.edge hCD _).trans h.triple_failure
           joint_failure := ?_
           joint_lower := ?_ }
  · apply le_trans (measureReal_mono (show
        {d | ¬ (RowArray.Gamma y.part y.edge D p d ∧ RowArray.Regular p d)} ⊆
        {d | ¬ (RowArray.Gamma y.part y.edge C p d ∧ RowArray.Regular p d)} from
          fun _ hd hc => hd ⟨gamma_mono hCD hc.1,hc.2⟩)) h.joint_failure
  · exact h.joint_lower.trans (measureReal_mono (fun _ hc => ⟨gamma_mono hCD hc.1,hc.2⟩))

end MajorityDynamics.GraphProcess.RowGamma
