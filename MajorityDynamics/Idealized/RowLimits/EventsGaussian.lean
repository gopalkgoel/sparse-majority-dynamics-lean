import MajorityDynamics.Idealized.RowLimits.Events

/-! Transport E.2 weak inequalities to the literal Gaussian history events. -/
noncomputable section
open Set MeasureTheory
open MajorityDynamics.Universal
open MajorityDynamics.Analysis
namespace MajorityDynamics.Idealized.RowLimits
variable {n : ℕ}

def historyParameters (σ : Row (n + 1)) :
    GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) n :=
  ((σ, WithLp.toLp 2 (ν n)), 0)

def childParameters (σ : Row (n + 1)) (b : Bool) (u : ℝ) :
    GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) (n + 1) :=
  ((σ, WithLp.toLp 2 (ν n)), childThreshold b u)

@[simp] theorem historyParameters_law (σ : Row (n + 1)) :
    GaussianRegularity.law (historyParameters σ) = rowLaw (ν n) σ := rfl
@[simp] theorem childParameters_law (σ : Row (n + 1)) (b : Bool) (u : ℝ) :
    GaussianRegularity.law (childParameters σ b u) = rowLaw (ν n) σ := rfl

theorem history_restrict_eq (s : History (n + 1)) (σ : Row (n + 1)) :
    (rowLaw (ν n) σ).restrict (historyEvent s) =
      (GaussianRegularity.law (historyParameters σ)).restrict
        (GaussianRegularity.event (historyMatrix s) 0) :=
  Measure.restrict_congr_set (historyEvent_ae_eq_weak s (ν n) (ν_positive n) σ)

theorem child_restrict_eq (s : History (n + 1)) (σ : Row (n + 1)) (b : Bool) (u : ℝ) :
    (rowLaw (ν n) σ).restrict (shiftedChildEvent s b u) =
      (GaussianRegularity.law (childParameters σ b u)).restrict
        (GaussianRegularity.event (childMatrix s b) (childThreshold b u)) :=
  Measure.restrict_congr_set (shiftedChildEvent_ae_eq_weak s b u (ν n) (ν_positive n) σ)

theorem gaussianMass_history_eq (s : History (n + 1)) (σ : Row (n + 1)) :
    gaussianMass σ (historyEvent s) = GaussianRegularity.mass (historyMatrix s) (historyParameters σ) :=
  congrArg ENNReal.toReal (measure_congr (historyEvent_ae_eq_weak s (ν n) (ν_positive n) σ))

theorem gaussianMass_child_eq (s : History (n + 1)) (σ : Row (n + 1)) (b : Bool) (u : ℝ) :
    gaussianMass σ (shiftedChildEvent s b u) =
      GaussianRegularity.mass (childMatrix s b) (childParameters σ b u) :=
  congrArg ENNReal.toReal (measure_congr (shiftedChildEvent_ae_eq_weak s b u (ν n) (ν_positive n) σ))

theorem gaussianFirst_history_eq (s : History (n + 1)) (σ : Row (n + 1)) (t : History (n + 1)) :
    gaussianFirst σ (historyEvent s) t =
      GaussianRegularity.firstMoment (historyMatrix s) t (historyParameters σ) := by
  unfold gaussianFirst GaussianRegularity.firstMoment
  rw [history_restrict_eq]
  rfl

theorem gaussianFirst_child_eq (s : History (n + 1)) (σ : Row (n + 1)) (b : Bool) (u : ℝ)
    (t : History (n + 1)) : gaussianFirst σ (shiftedChildEvent s b u) t =
      GaussianRegularity.firstMoment (childMatrix s b) t (childParameters σ b u) := by
  unfold gaussianFirst GaussianRegularity.firstMoment
  rw [child_restrict_eq]
  rfl

theorem gaussianSecond_history_eq (s : History (n + 1)) (σ : Row (n + 1))
    (t t' : History (n + 1)) : gaussianSecond σ (historyEvent s) t t' =
      GaussianRegularity.secondMoment (historyMatrix s) t t' (historyParameters σ) := by
  unfold gaussianSecond GaussianRegularity.secondMoment
  rw [history_restrict_eq]
  rfl

theorem gaussianSecond_child_eq (s : History (n + 1)) (σ : Row (n + 1)) (b : Bool) (u : ℝ)
    (t t' : History (n + 1)) : gaussianSecond σ (shiftedChildEvent s b u) t t' =
      GaussianRegularity.secondMoment (childMatrix s b) t t' (childParameters σ b u) := by
  unfold gaussianSecond GaussianRegularity.secondMoment
  rw [child_restrict_eq]
  rfl

theorem gaussianMean_history_eq (s : History (n + 1)) (σ : Row (n + 1)) (t : History (n + 1)) :
    gaussianMean σ (historyEvent s) t =
      GaussianRegularity.conditionalFirst (historyMatrix s) t (historyParameters σ) := by
  rw [gaussianMean, gaussianFirst_history_eq, gaussianMass_history_eq]
  rfl

theorem gaussianMean_child_eq (s : History (n + 1)) (σ : Row (n + 1)) (b : Bool) (u : ℝ)
    (t : History (n + 1)) : gaussianMean σ (shiftedChildEvent s b u) t =
      GaussianRegularity.conditionalFirst (childMatrix s b) t (childParameters σ b u) := by
  rw [gaussianMean, gaussianFirst_child_eq, gaussianMass_child_eq]
  rfl

theorem gaussianCovariance_history_eq (s : History (n + 1)) (σ : Row (n + 1))
    (t t' : History (n + 1)) : gaussianCovariance σ (historyEvent s) t t' =
      GaussianRegularity.conditionalCovariance (historyMatrix s) t t' (historyParameters σ) := by
  rw [gaussianCovariance, gaussianSecond_history_eq, gaussianMass_history_eq,
    gaussianMean_history_eq, gaussianMean_history_eq]
  rfl

end MajorityDynamics.Idealized.RowLimits
