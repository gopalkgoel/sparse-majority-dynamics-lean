import MajorityDynamics.Universal.Geometry
import MajorityDynamics.Analysis.ConditionalGaussian.Core
import MajorityDynamics.Analysis.ConditionalGaussian.OpenConditioning

/-!
# The history-specific conditional Gaussian

The strong bijection and positive centered covariance are applications of the
completed Appendix D.2/A.5 proofs to the actual diagonal Gaussian law.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

variable {n : ℕ}

theorem gaussian_history_core (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) :
    ConditionalGaussian.CoreResult (covariance ν) (historyCone s) := by
  apply ConditionalGaussian.core _ _ _ (covariance_posDef ν hν) _
    (historyCone_nonempty s) (historyCone_isOpen s) (historyCone_convex s)
  exact Nat.succ_le_of_lt (Fintype.card_pos (α := Fin (n + 1) → Bool))

/-- `prop:cond-mean-bijection`, with the literal Gaussian conditional mean. -/
theorem conditionalMean_bijection (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) :
    ∃ f : StrongBijection (historyCone s), f.toFun = meanMap s ν :=
  (gaussian_history_core s ν hν).strong_bijection

def meanBijection (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) : StrongBijection (historyCone s) :=
  (conditionalMean_bijection s ν hν).choose

@[simp] theorem meanBijection_toFun (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) : (meanBijection s ν hν).toFun = meanMap s ν :=
  (conditionalMean_bijection s ν hν).choose_spec

theorem child_gaussian_regular (s : History (n + 1)) (b : Bool)
    (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    ConditionalGaussian.RegularOn
      (ConditionalGaussian.condition (rowLaw ν γ) (childCone s b)) (childCone s b) :=
  ConditionalGaussian.gaussian_conditional_regular _ (covariance_posDef ν hν) _
    (childCone_nonempty s b) (childCone_isOpen s b) γ

theorem child_gaussian_mean_mem (s : History (n + 1)) (b : Bool)
    (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    ConditionalGaussian.mean
      (ConditionalGaussian.condition (rowLaw ν γ) (childCone s b)) ∈ childCone s b :=
  (ConditionalGaussian.open_conditioning _ (covariance_posDef ν hν) _
    (childCone_nonempty s b) (childCone_isOpen s b) (childCone_convex s b) γ).2.1

theorem history_mass_pos (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) : 0 < rowLaw ν γ (historyCone s) :=
  (gaussian_history_core s ν hν).mass_pos γ

theorem child_mass_pos (s : History (n + 1)) (b : Bool) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) : 0 < rowLaw ν γ (childCone s b) :=
  ConditionalGaussian.gaussianLaw_mass_pos _ (covariance_posDef ν hν) γ _
    (childCone_isOpen s b) (childCone_nonempty s b)

instance rowLaw_isProbabilityMeasure (ν : History (n + 1) → ℝ) (γ : Row (n + 1)) :
    IsProbabilityMeasure (rowLaw ν γ) :=
  inferInstanceAs (IsProbabilityMeasure (multivariateGaussian γ (covariance ν)))

instance rowLaw_isGaussian (ν : History (n + 1) → ℝ) (γ : Row (n + 1)) :
    IsGaussian (rowLaw ν γ) :=
  inferInstanceAs (IsGaussian (multivariateGaussian γ (covariance ν)))

/-- `lem:cond-cov-pd`, before specializing to the recursively constructed arrays. -/
theorem conditional_covariance_posDef (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    (ConditionalGaussian.covMatrix
      (ConditionalGaussian.condition (rowLaw ν γ) (historyCone s))).PosDef :=
  (gaussian_history_core s ν hν).covariance_posDef γ

@[simp] theorem meanMap_one (s : History 1) (ν : History 1 → ℝ) (γ : Row 1) :
    meanMap s ν γ = γ := by
  simp [meanMap, ConditionalGaussian.conditionalMean, ConditionalGaussian.conditionalLaw,
    ConditionalGaussian.condition, ConditionalGaussian.mean, ConditionalGaussian.gaussianLaw]

end MajorityDynamics.Universal
