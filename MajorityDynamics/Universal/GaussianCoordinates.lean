import MajorityDynamics.Universal.GaussianRows
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! # Independent normal coordinates of the concrete row law -/

noncomputable section

open MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

variable {n : ℕ}

/-- Each coordinate has the paper's mean and variance; the second normal parameter is variance. -/
theorem rowLaw_coordinate (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t)
    (γ : Row (n + 1)) (t : History (n + 1)) :
    MeasurePreserving (fun x : Row (n + 1) => x t) (rowLaw ν γ)
      (gaussianReal (γ t) (ν t).toNNReal) := by
  simpa [rowLaw, ConditionalGaussian.gaussianLaw, covariance] using
    (measurePreserving_eval_multivariateGaussian
      (μ := γ) (covariance_posDef ν hν).posSemidef (i := t))

/-- The diagonal covariance really gives jointly independent coordinates. -/
theorem rowLaw_independent_coordinates (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    iIndepFun (fun t (x : Row (n + 1)) => x t) (rowLaw ν γ) := by
  have hg : HasGaussianLaw (fun x : Row (n + 1) => fun t => x t) (rowLaw ν γ) := by
    exact HasGaussianLaw.map_of_measurable
      (EuclideanSpace.equiv (History (n + 1)) ℝ).toContinuousLinearMap
      IsGaussian.hasGaussianLaw_id (by fun_prop)
  apply hg.iIndepFun_of_covariance_eq_zero
  intro i j hij
  change ProbabilityTheory.covariance (fun x : Row (n + 1) => x i) (fun x => x j)
    (multivariateGaussian γ (covariance ν)) = 0
  rw [covariance_eval_multivariateGaussian (covariance_posDef ν hν).posSemidef]
  simp [covariance, Matrix.diagonal, hij]

/-- The entire Gaussian row family is realized by independent sampling of rows. -/
def arrayLaw (ν : History (n + 1) → ℝ) (γ : History (n + 1) → Row (n + 1)) :
    Measure (History (n + 1) → Row (n + 1)) := Measure.pi (fun s => rowLaw ν (γ s))

theorem arrayLaw_row (ν : History (n + 1) → ℝ) (γ : History (n + 1) → Row (n + 1))
    (s : History (n + 1)) :
    MeasurePreserving (fun W => W s) (arrayLaw ν γ) (rowLaw ν (γ s)) :=
  measurePreserving_eval _ s

theorem arrayLaw_independent_rows (ν : History (n + 1) → ℝ)
    (γ : History (n + 1) → Row (n + 1)) :
    iIndepFun (fun s W => W s) (arrayLaw ν γ) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem arrayLaw_coordinate (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t)
    (γ : History (n + 1) → Row (n + 1)) (s t : History (n + 1)) :
    MeasurePreserving (fun W => W s t) (arrayLaw ν γ)
      (gaussianReal (γ s t) (ν t).toNNReal) :=
  (rowLaw_coordinate ν hν (γ s) t).comp (arrayLaw_row ν γ s)

end MajorityDynamics.Universal
