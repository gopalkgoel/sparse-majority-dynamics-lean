import MajorityDynamics.GraphProcess.RowConcentration.Expectations

/-! The exact joint failure event and elementary finite probability assembly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowConcentration
variable {V : Type*} [Fintype V] {n : ℕ}

theorem failure_union_le (y : Local.CoarseData V n) (p : ℝ) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) :
    (conditionedLaw y q).real {d | ¬ Good y p q d} ≤
      (conditionedLaw y q).real {d | ¬ R1 y p d} +
      (conditionedLaw y q).real {d | ¬ R2 y q d} +
      (conditionedLaw y q).real {d | ¬ R3 y p q d} := by
  let := conditioned_probability y q hφ hc
  have he : {d | ¬ Good y p q d} =
      ({d | ¬ R1 y p d} ∪ {d | ¬ R2 y q d}) ∪ {d | ¬ R3 y p q d} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_union, Good]
    tauto
  rw [he]
  exact (measureReal_union_le _ _).trans
    (add_le_add (measureReal_union_le _ _) le_rfl)

theorem polynomial_absorption {N A C : ℝ} (hN : 0 < N) (hC : C ≤ N) :
    C * N ^ (-(A + 1)) ≤ N ^ (-A) := by
  calc
    _ ≤ N * N ^ (-(A + 1)) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN.le _)
    _ = N ^ (1 : ℝ) * N ^ (-(A + 1)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring

end MajorityDynamics.GraphProcess.RowConcentration
