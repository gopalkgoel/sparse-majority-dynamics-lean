import MajorityDynamics.Idealized.RowLimits.ApproximationLocal
import MajorityDynamics.Idealized.RowLimits.ComparisonTargets
import MajorityDynamics.Idealized.RowLimits.Uniform

/-! A common event index for assembling the history and two child estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis
variable {n : ℕ}

def targetEvent (s : History (n + 1)) (b : Option Bool) (u : ℝ) : Set (Row (n + 1)) :=
  match b with
  | none => historyEvent s
  | some b => shiftedChildEvent s b u

def targetParameters (σ : Row (n + 1)) (b : Option Bool) (u : ℝ) :
    GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) (eventRows n b) :=
  match b with
  | none => historyParameters σ
  | some b => childParameters σ b u

@[simp] theorem eventMatrix_none (s : History (n + 1)) :
    eventMatrix s none = historyMatrix s := by
  ext j t
  exact historyIntegerMatrix_cast s j t

@[simp] theorem eventMatrix_some (s : History (n + 1)) (b : Bool) :
    eventMatrix s (some b) = childMatrix s b := by
  ext j t
  rfl

theorem target_mass_eq (s : History (n + 1)) (σ : Row (n + 1)) (b : Option Bool) (u : ℝ) :
    gaussianMass σ (targetEvent s b u) =
      GaussianRegularity.mass (eventMatrix s b) (targetParameters σ b u) := by
  cases b with
  | none => simpa only [targetEvent, targetParameters, eventMatrix_none] using
      gaussianMass_history_eq s σ
  | some b => simpa only [targetEvent, targetParameters, eventMatrix_some] using
      gaussianMass_child_eq s σ b u

theorem target_first_eq (s : History (n + 1)) (σ : Row (n + 1))
    (b : Option Bool) (u : ℝ) (t : History (n + 1)) :
    gaussianFirst σ (targetEvent s b u) t =
      GaussianRegularity.firstMoment (eventMatrix s b) t (targetParameters σ b u) := by
  cases b with
  | none => simpa only [targetEvent, targetParameters, eventMatrix_none] using
      gaussianFirst_history_eq s σ t
  | some b => simpa only [targetEvent, targetParameters, eventMatrix_some] using
      gaussianFirst_child_eq s σ b u t

theorem target_second_eq (s : History (n + 1)) (σ : Row (n + 1))
    (b : Option Bool) (u : ℝ) (t t' : History (n + 1)) :
    gaussianSecond σ (targetEvent s b u) t t' =
      GaussianRegularity.secondMoment (eventMatrix s b) t t' (targetParameters σ b u) := by
  cases b with
  | none => simpa only [targetEvent, targetParameters, eventMatrix_none] using
      gaussianSecond_history_eq s σ t t'
  | some b => simpa only [targetEvent, targetParameters, eventMatrix_some] using
      gaussianSecond_child_eq s σ b u t t'

@[simp] theorem actualNormalizedParameters_none (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (σ : Row (n + 1)) :
    actualNormalizedParameters N p sizes s σ none =
      normalizedParameters N p sizes s σ (historyMatrix s) := by
  simp only [actualNormalizedParameters, eventMatrix_none, normalizedParameters]

@[simp] theorem actualNormalizedParameters_some (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (σ : Row (n + 1)) (b : Bool) :
    actualNormalizedParameters N p sizes s σ (some b) =
      normalizedParameters N p sizes s σ (childMatrix s b) := by
  simp only [actualNormalizedParameters, eventMatrix_some, normalizedParameters]

theorem rowParameterBox_eq_gaussianBox (n r : ℕ) (T R : ℝ) :
    rowParameterBox n r T R = gaussianBox n r R T := rfl

theorem gaussianMass_le_one (σ : Row (n + 1)) (A : Set (Row (n + 1))) :
    |gaussianMass σ A| ≤ 1 := by
  rw [gaussianMass, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr
    (prob_le_one)

end MajorityDynamics.Idealized.RowLimits
