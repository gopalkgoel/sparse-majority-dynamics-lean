import MajorityDynamics.GraphProcess.RowConcentration.Basic
import MajorityDynamics.GraphProcess.RowConcentration.Truncation

/-! The actual degree-times-child variables and their deterministic clamping. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

def clippedVariable (y : Local.CoarseData V n) (p : ℝ)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1))
    (v : V) (d : RowArray.Ambient y.part) : ℝ :=
  min (childVariable s b t v d) (2 * p * Fintype.card V)

def clippedMass (y : Local.CoarseData V n) (p : ℝ)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1))
    (d : RowArray.Ambient y.part) : ℝ := ∑ v, clippedVariable y p s b t v d

theorem clippedVariable_bounds (y : Local.CoarseData V n) {p : ℝ} (hp : 0 ≤ p)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1))
    (v : V) (d : RowArray.Ambient y.part) :
    0 ≤ clippedVariable y p s b t v d ∧
      clippedVariable y p s b t v d ≤ 2 * p * Fintype.card V := by
  exact ⟨le_min (childVariable_bounds s b t v d).1 (by positivity), min_le_right _ _⟩

theorem clippedVariable_eq_of_R1 (y : Local.CoarseData V n) {p : ℝ} (hp : 0 ≤ p)
    (htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V)
    (d : RowArray.Ambient y.part) (hd : R1 y p d)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) (v : V) :
    clippedVariable y p s b t v d = childVariable s b t v d := by
  apply min_eq_left
  have hs : (y.sizes t : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (show y.sizes t ≤ Fintype.card V by
      rw [Local.CoarseData.sizes, ← History.block_card_partSizes]
      exact Finset.card_le_univ _)
  have hd' := (abs_le.mp (hd v t)).2
  have hps := mul_le_mul_of_nonneg_left hs hp
  unfold childVariable
  split_ifs
  · linarith
  · positivity

theorem clippedMass_eq_of_R1 (y : Local.CoarseData V n) {p : ℝ} (hp : 0 ≤ p)
    (htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V)
    (d : RowArray.Ambient y.part) (hd : R1 y p d)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    clippedMass y p s b t d = (RowArray.childMass d s b t : ℝ) := by
  unfold clippedMass
  simp_rw [clippedVariable_eq_of_R1 y hp htol d hd]
  exact sum_childVariable s b t d

theorem mass_change_bound (y : Local.CoarseData V n) {p : ℝ} (hp : 0 ≤ p)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1))
    (d : RowArray.Ambient y.part) :
    |(RowArray.childMass d s b t : ℝ) - clippedMass y p s b t d| ≤
      (Fintype.card V : ℝ)^2 := by
  rw [← sum_childVariable s b t d, clippedMass, ← Finset.sum_sub_distrib]
  have hb (v : V) : 0 ≤ childVariable s b t v d - clippedVariable y p s b t v d ∧
      childVariable s b t v d - clippedVariable y p s b t v d ≤ Fintype.card V := by
    have hc := clippedVariable_bounds y hp s b t v d
    have hv := childVariable_bounds s b t v d
    have hm : clippedVariable y p s b t v d ≤ childVariable s b t v d := min_le_left _ _
    constructor <;> linarith
  rw [abs_of_nonneg (Finset.sum_nonneg fun v _ => (hb v).1)]
  calc
    _ ≤ ∑ _v : V, (Fintype.card V : ℝ) := Finset.sum_le_sum fun v _ => (hb v).2
    _ = _ := by simp [pow_two]

end MajorityDynamics.GraphProcess.RowConcentration
