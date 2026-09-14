import MajorityDynamics.GraphProcess.RowConcentration.Expectations
import MajorityDynamics.GraphProcess.RowConcentration.Bounded
import MajorityDynamics.GraphProcess.RowConcentration.MassBasic

/-! Concentration of original child degree masses, with the clamping bias proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

theorem independent_clippedVariable (y : Local.CoarseData V n) (p : ℝ)
    (q : Local.Tilt n) {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    iIndepFun (clippedVariable y p s b t) (conditionedLaw y q) := by
  exact (independent_childVariable y q hφ hc s b t).comp
    (fun _ x => min x (2 * p * Fintype.card V))
    (fun _ => measurable_id.min measurable_const)

theorem mass_expectation_bias (y : Local.CoarseData V n) {p : ℝ} (hp : 0 ≤ p)
    (q : Local.Tilt n) {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    |Local.templateHalfEdges y.sizes q (append s b) t -
      ∫ d, clippedMass y p s b t d ∂conditionedLaw y q| ≤
        (Fintype.card V : ℝ)^2 * (conditionedLaw y q).real {d | ¬ R1 y p d} := by
  let := conditioned_probability y q hφ hc
  rw [← expected_child_mass y q hφ hc s b t]
  apply Truncation.expectation_bias
  · intro d hd
    exact (clippedMass_eq_of_R1 y hp htol d (not_not.mp hd) s b t).symm
  · exact mass_change_bound y hp s b t

theorem clipped_mass_tail (y : Local.CoarseData V n) {p : ℝ} (hp : 0 ≤ p)
    (q : Local.Tilt n) {φ r : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hr : 0 ≤ r) (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    (conditionedLaw y q).real {d | r < |clippedMass y p s b t d -
      ∫ a, clippedMass y p s b t a ∂conditionedLaw y q|} ≤
        2 * Real.exp (-2 * r^2 / ((Fintype.card V : ℝ) * (2 * p * Fintype.card V)^2)) := by
  let := conditioned_probability y q hφ hc
  have h := Bounded.sum_integral_tail (independent_clippedVariable y p q hφ hc s b t)
    (fun _ => (measurable_of_countable _).aemeasurable)
    (B := 2 * p * Fintype.card V) (by positivity)
    (fun v => Filter.Eventually.of_forall fun d => clippedVariable_bounds y hp s b t v d)
    Finset.univ hr
  simp only [Finset.card_univ] at h
  refine le_trans ?_ h
  apply measureReal_mono _ (by finiteness)
  intro d hd
  exact le_of_lt (show r < _ from hd)

theorem mass_tail (y : Local.CoarseData V n) {p : ℝ} (hp : 0 ≤ p)
    (q : Local.Tilt n) {φ r : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hr : 0 ≤ r)
    (htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V)
    (hbias : (Fintype.card V : ℝ)^2 * (conditionedLaw y q).real {d | ¬ R1 y p d} ≤ r / 2)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    (conditionedLaw y q).real {d | r < |(RowArray.childMass d s b t : ℝ) -
      Local.templateHalfEdges y.sizes q (append s b) t|} ≤
      (conditionedLaw y q).real {d | ¬ R1 y p d} +
        2 * Real.exp (-2 * (r / 2)^2 /
          ((Fintype.card V : ℝ) * (2 * p * Fintype.card V)^2)) := by
  let := conditioned_probability y q hφ hc
  have hb := (mass_expectation_bias y hp q hφ hc htol s b t).trans hbias
  rw [← expected_child_mass y q hφ hc s b t] at hb ⊢
  refine (Truncation.centered_tail (conditionedLaw y q)
    (fun d => (RowArray.childMass d s b t : ℝ)) (clippedMass y p s b t)
    {d | ¬ R1 y p d} r ?_ hb).trans ?_
  · intro d hd
    exact (clippedMass_eq_of_R1 y hp htol d (not_not.mp hd) s b t).symm
  · exact add_le_add le_rfl (clipped_mass_tail y hp q hφ hc (r := r / 2) (by positivity) s b t)

theorem mass_tail_at_scale (y : Local.CoarseData V n) {p : ℝ} (hp : 0 < p)
    (q : Local.Tilt n) {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hN : 0 < Fintype.card V) (hlog : 0 ≤ Real.log (Fintype.card V))
    (htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V)
    (hbias : (Fintype.card V : ℝ)^2 * (conditionedLaw y q).real {d | ¬ R1 y p d} ≤
      ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
        Real.log (Fintype.card V)) / 2)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    (conditionedLaw y q).real {d |
      (Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) * Real.log (Fintype.card V) <
        |(RowArray.childMass d s b t : ℝ) -
          Local.templateHalfEdges y.sizes q (append s b) t|} ≤
      (conditionedLaw y q).real {d | ¬ R1 y p d} +
        2 * Real.exp (-(Real.log (Fintype.card V))^2 / 8) := by
  have hNr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  have h := mass_tail y hp.le q hφ hc
    (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hp.le) (Real.sqrt_nonneg _)) hlog)
    htol hbias s b t
  have hs := Real.sq_sqrt hNr.le
  have hspos : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.mpr hNr
  have heq : -2 * (((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
        Real.log (Fintype.card V)) / 2)^2 /
      ((Fintype.card V : ℝ) * (2 * p * Fintype.card V)^2) =
        -(Real.log (Fintype.card V))^2 / 8 := by
    field_simp
    nlinarith [hs]
  rwa [heq] at h

theorem R3_failure (y : Local.CoarseData V n) {p : ℝ} (hp : 0 < p)
    (q : Local.Tilt n) {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hN : 0 < Fintype.card V) (hlog : 0 ≤ Real.log (Fintype.card V))
    (htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V)
    (hbias : (Fintype.card V : ℝ)^2 * (conditionedLaw y q).real {d | ¬ R1 y p d} ≤
      ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
        Real.log (Fintype.card V)) / 2) :
    (conditionedLaw y q).real {d | ¬ R3 y p q d} ≤
      ((Fintype.card (History (n + 1)) : ℝ)^2 * 2) *
        ((conditionedLaw y q).real {d | ¬ R1 y p d} +
          2 * Real.exp (-(Real.log (Fintype.card V))^2 / 8)) := by
  let := conditioned_probability y q hφ hc
  have heq : {d | ¬ R3 y p q d} = ⋃ i : (History (n + 1) × History (n + 1)) × Bool,
      {d | (Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
        Real.log (Fintype.card V) < |(RowArray.childMass d i.1.1 i.2 i.1.2 : ℝ) -
          Local.templateHalfEdges y.sizes q (append i.1.1 i.2) i.1.2|} := by
    ext d
    simp only [R3, not_forall, not_le, Set.mem_iUnion, Set.mem_ofPred_eq, Prod.exists]
  rw [heq]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc
    _ ≤ ∑ _i : (History (n + 1) × History (n + 1)) × Bool,
        ((conditionedLaw y q).real {d | ¬ R1 y p d} +
          2 * Real.exp (-(Real.log (Fintype.card V))^2 / 8)) :=
      Finset.sum_le_sum fun i _ => mass_tail_at_scale y hp q hφ hc hN hlog htol hbias
        i.1.1 i.2 i.1.2
    _ = _ := by simp [pow_two, mul_add]

end MajorityDynamics.GraphProcess.RowConcentration
