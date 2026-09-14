import MajorityDynamics.GraphProcess.RowConcentration.Expectations
import MajorityDynamics.GraphProcess.RowConcentration.Bounded

/-! Concentration of the original child cardinality around the exact template. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

theorem size_tail (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ r : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) (hr : 0 ≤ r)
    (s : History (n + 1)) (b : Bool) :
    (conditionedLaw y q).real {d | r < |((RowArray.childSet d s b).card : ℝ) -
      Local.templateSizes y.sizes q (append s b)|} ≤
      2 * Real.exp (-2 * r^2 / Fintype.card V) := by
  let := conditioned_probability y q hφ hc
  have h := Bounded.sum_integral_tail (independent_childIndicator y q hφ hc s b)
    (fun _ => (measurable_of_countable _).aemeasurable) (B := 1) (by norm_num)
    (fun v => Filter.Eventually.of_forall fun d => childIndicator_bounds s b v d)
    Finset.univ hr
  simp only [Finset.card_univ, one_pow, mul_one,
    sum_childIndicator, expected_child_card y q hφ hc s b] at h
  refine le_trans ?_ h
  apply measureReal_mono _ (by finiteness)
  intro d hd
  exact le_of_lt (show r < _ from hd)

theorem size_tail_at_scale (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hN : 0 < Fintype.card V) (hlog : 0 ≤ Real.log (Fintype.card V))
    (s : History (n + 1)) (b : Bool) :
    (conditionedLaw y q).real {d | Real.sqrt (Fintype.card V) * Real.log (Fintype.card V) <
      |((RowArray.childSet d s b).card : ℝ) - Local.templateSizes y.sizes q (append s b)|} ≤
      2 * Real.exp (-2 * (Real.log (Fintype.card V))^2) := by
  have h := size_tail y q hφ hc (mul_nonneg (Real.sqrt_nonneg (Fintype.card V)) hlog) s b
  have hNr : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have heq : -2 * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))^2 /
      (Fintype.card V : ℝ) = -2 * (Real.log (Fintype.card V))^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    field_simp
  rwa [heq] at h

theorem R2_failure (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hN : 0 < Fintype.card V) (hlog : 0 ≤ Real.log (Fintype.card V)) :
    (conditionedLaw y q).real {d | ¬ R2 y q d} ≤
      ((Fintype.card (History (n + 1)) : ℝ) * 2) *
        (2 * Real.exp (-2 * (Real.log (Fintype.card V))^2)) := by
  let := conditioned_probability y q hφ hc
  have heq : {d | ¬ R2 y q d} = ⋃ i : History (n + 1) × Bool,
      {d | Real.sqrt (Fintype.card V) * Real.log (Fintype.card V) <
        |((RowArray.childSet d i.1 i.2).card : ℝ) -
          Local.templateSizes y.sizes q (append i.1 i.2)|} := by
    ext d
    simp only [R2, not_forall, not_le, Set.mem_iUnion, Set.mem_ofPred_eq, Prod.exists]
  rw [heq]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc
    _ ≤ ∑ _i : History (n + 1) × Bool,
        2 * Real.exp (-2 * (Real.log (Fintype.card V))^2) :=
      Finset.sum_le_sum fun i _ => size_tail_at_scale y q hφ hc hN hlog i.1 i.2
    _ = _ := by simp

end MajorityDynamics.GraphProcess.RowConcentration
