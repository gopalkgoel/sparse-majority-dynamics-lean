import MajorityDynamics.GraphProcess.FiberTransference.Laws
import MajorityDynamics.GraphProcess.EnumerationComparison.Basic
import MajorityDynamics.GraphProcess.RowGamma.Results

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Exact Bayes assembly for the actual graph fiber. The strong comparison is
required only on the original totals/regularity/Gamma support. -/
theorem actual_transfer (p : unitInterval) (y : Local.CoarseData V n)
    (q : Local.Tilt n) {CΓ A logC ε : ℝ} {N : ℕ}
    (hactual : AdmissibleFiber.ActualLaws p y)
    (hrow : RowGamma.Conclusion y q CΓ p A N)
    (hgamma : (cond (GraphicalArray.law y.part y.edge)
      (GraphicalArray.historyRegular p y.part)).real
        {d | ¬ RowArray.Gamma y.part y.edge CΓ p d} ≤ ε)
    (hstrong : ∀ F : Set (RowArray.Ambient y.part),
      (∀ d ∈ F, RowArray.totals d = y.edge ∧ RowArray.Regular p d ∧
        RowArray.Gamma y.part y.edge CΓ p d) →
      EnumerationComparison.Sandwich logC
        ((GraphicalArray.law y.part y.edge).real F)
        ((cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real F))
    (E : Set (RowArray.Ambient y.part)) :
    (CoarseKernel.Lambda p y).real {σ | σ.deg ∉ RowArray.values '' E} ≤
      ε + 2*(Real.exp logC)^2*
        (cond (RowConcentration.conditionedLaw y q)
          (RowArray.exactTotals y.part y.edge)).real Eᶜ := by
  let μ := GraphicalArray.law y.part y.edge
  let ν := cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)
  let H := GraphicalArray.historyRegular p y.part
  let I := RowArray.history y.part
  let J := {d : RowArray.Ambient y.part |
    RowArray.Gamma y.part y.edge CΓ p d ∧ RowArray.totals d = y.edge}
  let G := {d : RowArray.Ambient y.part |
    RowArray.Gamma y.part y.edge CΓ p d ∧ RowArray.Regular p d}
  let : IsProbabilityMeasure μ := GraphicalArray.law_probability y
  let : IsProbabilityMeasure ν := BlockPairLaws.conditioned_probability y q
  have horder : cond ν I = cond (RowConcentration.conditionedLaw y q)
      (RowArray.exactTotals y.part y.edge) := row_condition_order y q
  have hνprob : IsProbabilityMeasure (cond ν I) := horder ▸ hrow.totals_probability
  have hI : 0 < ν.real I := by
    have huniv := @measure_univ _ _ (cond ν I) hνprob
    have hh := RowExactTotals.conditioned_real_eq_div ν I Set.univ MeasurableSet.univ
    have hreal : (cond ν I).real Set.univ = 1 := by
      rw [Measure.real, huniv, ENNReal.toReal_one]
    rw [hreal, Set.inter_univ] at hh
    by_contra hn
    have hz : ν.real I = 0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
    simp [hz] at hh
  have hνtot : ∀ᵐ d ∂ν, RowArray.totals d = y.edge :=
    ae_cond_mem (Set.to_countable _).measurableSet
  have heq : ν.real (H ∩ J) = ν.real (I ∩ G) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hνtot] with d hd
    apply propext
    change ((d ∈ I ∧ RowArray.Regular p d) ∧
      (RowArray.Gamma y.part y.edge CΓ p d ∧ RowArray.totals d = y.edge)) ↔
      (d ∈ I ∧ (RowArray.Gamma y.part y.edge CΓ p d ∧ RowArray.Regular p d))
    tauto
  have hhalf : ν.real I / 2 ≤ ν.real (H ∩ J) := by
    have hh := hrow.joint_lower
    rw [← horder, RowExactTotals.conditioned_real_eq_div ν I G
      (Set.to_countable _).measurableSet] at hh
    rw [heq]
    have := (le_div_iff₀ hI).mp hh
    linarith
  have hs : EnumerationComparison.Sandwich logC (μ.real (H ∩ J))
      (ν.real (H ∩ J)) := hstrong _ (by
    intro d hd
    exact ⟨hd.2.2,hd.1.2,hd.2.1⟩)
  have hlower : ν.real (H ∩ J) ≤ Real.exp logC * μ.real (H ∩ J) := by
    have hm := mul_le_mul_of_nonneg_left hs.1 (Real.exp_nonneg logC)
    rw [← mul_assoc, ← Real.exp_add] at hm
    simpa only [add_neg_cancel,Real.exp_zero,one_mul] using hm
  have hupper : μ.real (H ∩ (Eᶜ ∩ J)) ≤ Real.exp logC * ν.real (I ∩ Eᶜ) := by
    have hh := (hstrong (H ∩ (Eᶜ ∩ J)) (by
      intro d hd
      exact ⟨hd.2.2.2,hd.1.2,hd.2.2.1⟩)).2
    exact hh.trans (mul_le_mul_of_nonneg_left
      (measureReal_mono (fun _ hd => ⟨hd.1.1,hd.2.1⟩)) (Real.exp_nonneg _))
  have hμtot : ∀ᵐ d ∂μ, RowArray.totals d = y.edge := by
    have hh : ∀ᵐ d ∂μ, d ∈ RowArray.exactTotals y.part y.edge ∩
        {d | GraphicalArray.Graphical d} :=
      (mem_ae_iff_prob_eq_one (Set.to_countable _).measurableSet).mpr
        (GraphicalArray.law_support y)
    filter_upwards [hh] with d hd
    exact hd.1
  have hbad : (cond μ H).real Jᶜ ≤ ε := by
    have he : (cond μ H).real Jᶜ = (cond μ H).real
        {d | ¬ RowArray.Gamma y.part y.edge CΓ p d} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [cond_absolutelyContinuous.ae_le hμtot] with d hd
      apply propext
      change (¬ (RowArray.Gamma y.part y.edge CΓ p d ∧ RowArray.totals d = y.edge)) ↔
        ¬ RowArray.Gamma y.part y.edge CΓ p d
      simp only [hd,and_true]
    rw [he]
    exact hgamma
  rw [lambda_complement p y hactual E]
  have hh := bayes_transfer μ ν H I J Eᶜ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet (Real.exp_pos logC) hI hhalf hlower hupper hbad
  simpa only [horder] using hh

end MajorityDynamics.GraphProcess.FiberTransference

/-- info: 'MajorityDynamics.GraphProcess.FiberTransference.actual_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FiberTransference.actual_transfer
