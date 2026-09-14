import MajorityDynamics.Universal.Symmetry
import MajorityDynamics.Universal.GaussianCoordinates

/-!
# Closed first-half §4 theorem, stated in the paper's original events

`n` is zero based: `ν n`, `μ n`, and `γ n` are the paper's day `k = n + 1`
arrays. `historyEvent` and `childEvent` retain the paper's rule for ties.
`main` has no internal hypotheses and no literature-axiom dependency.
`Section4.lean` extends this preserved contract with the proved response
recursion (`ε`, `β`), coherence, sign identities, and nondegeneracy.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

def dayLaw (n : ℕ) (s : History (n + 1)) := rowLaw (ν n) (γ n s)
def dayArrayLaw (n : ℕ) := arrayLaw (ν n) (γ n)
def historyLaw (n : ℕ) (s : History (n + 1)) :=
  ConditionalGaussian.condition (dayLaw n s) (historyEvent s)
def childLaw (n : ℕ) (s : History (n + 1)) (b : Bool) :=
  ConditionalGaussian.condition (dayLaw n s) (childEvent s b)

theorem historyLaw_regular (n : ℕ) (s : History (n + 1)) :
    ConditionalGaussian.RegularOn (historyLaw n s) (historyCone s) := by
  rw [historyLaw, dayLaw, history_condition_eq s (ν n) (ν_positive n)]
  exact ConditionalGaussian.gaussian_conditional_regular _
    (covariance_posDef _ (ν_positive n)) _ (historyCone_nonempty s) (historyCone_isOpen s) _

theorem childLaw_regular (n : ℕ) (s : History (n + 1)) (b : Bool) :
    ConditionalGaussian.RegularOn (childLaw n s b) (childCone s b) := by
  rw [childLaw, dayLaw, child_condition_eq s b (ν n) (ν_positive n)]
  exact child_gaussian_regular s b (ν n) (ν_positive n) (γ n s)

theorem history_mean_coordinate (n : ℕ) (s t : History (n + 1)) :
    (∫ x, x t ∂historyLaw n s) = ν n t * μ n s t := by
  have hreg := historyLaw_regular n s
  let := hreg.probability
  have he : ConditionalGaussian.mean (historyLaw n s) t = ∫ x, x t ∂historyLaw n s :=
    eval_integral_piLp (fun j => (hreg.memLp_two.eval_piLp j).integrable (by norm_num)) t
  rw [← he, historyLaw, dayLaw, history_condition_eq s (ν n) (ν_positive n)]
  exact congrArg (fun x : Row (n + 1) => x t) (γ_defining n s)

theorem ν_recursion_events (n : ℕ) (s : History (n + 1)) (b : Bool) :
    ν (n + 1) (append s b) = ν n s * (historyLaw n s).real (childEvent s b) := by
  rw [ν_recursion, branchProbability_eq_event_condition s (ν n) (ν_positive n)]
  rfl

theorem μ_recursion_events (n : ℕ) (s t : History (n + 1)) (b c : Bool) :
    μ (n + 1) (append s b) (append t c) =
      (∫ x, x t ∂childLaw n s b) / ν n t +
      (∫ x, x s ∂childLaw n t c) / ν n s - μ n s t := by
  rw [μ_recursion, branchMean_coordinate s (ν n) (ν_positive n),
    branchMean_coordinate t (ν n) (ν_positive n)]
  rfl

def conditionalCovariance (n : ℕ) (s : History (n + 1)) :=
  ConditionalGaussian.covMatrix (historyLaw n s)

/-- The covariance is centered, with exactly the entries displayed in the paper. -/
theorem conditionalCovariance_entry (n : ℕ) (s t u : History (n + 1)) :
    conditionalCovariance n s t u =
      (∫ x, x t * x u ∂historyLaw n s) -
        (∫ x, x t ∂historyLaw n s) * (∫ x, x u ∂historyLaw n s) := by
  have hreg := historyLaw_regular n s
  let := hreg.probability
  exact covariance_eq_sub (hreg.memLp_two.eval_piLp t) (hreg.memLp_two.eval_piLp u)

/-- `lem:cond-cov-pd` for the constructed day-`k` Gaussian model and original event. -/
theorem universal_conditional_covariance_posDef (n : ℕ) (s : History (n + 1)) :
    (conditionalCovariance n s).PosDef := by
  rw [conditionalCovariance, historyLaw, dayLaw, history_condition_eq s (ν n) (ν_positive n)]
  exact conditional_covariance_posDef s (ν n) (ν_positive n) (γ n s)

/-- The whole first-half §4 contract is about the constructed arrays and actual laws. -/
structure UniversalRecursionTheorem : Prop where
  initial_ν : ∀ s, ν 0 s = 1 / 2
  initial_μ : ∀ s t, μ 0 s t = 0
  initial_γ : ∀ s, γ 0 s = 0
  positive : ∀ n s, 0 < ν n s
  total : ∀ n, ∑ s, ν n s = 1
  symmetric : ∀ n s t, μ n s t = μ n t s
  cone : ∀ n s, WithLp.toLp 2 (fun t => ν n t * μ n s t) ∈ historyCone s
  history_mass : ∀ n s, 0 < dayLaw n s (historyEvent s)
  child_mass : ∀ n s b, 0 < dayLaw n s (childEvent s b)
  history_probability : ∀ n s, IsProbabilityMeasure (historyLaw n s)
  history_moments : ∀ n s, MemLp id 2 (historyLaw n s)
  child_probability : ∀ n s b, IsProbabilityMeasure (childLaw n s b)
  child_moments : ∀ n s b, MemLp id 2 (childLaw n s b)
  mean_identity : ∀ n s t, (∫ x, x t ∂historyLaw n s) = ν n t * μ n s t
  proportions : ∀ n s b,
    ν (n + 1) (append s b) = ν n s * (historyLaw n s).real (childEvent s b)
  corrections : ∀ n s t b c, μ (n + 1) (append s b) (append t c) =
    (∫ x, x t ∂childLaw n s b) / ν n t + (∫ x, x s ∂childLaw n t c) / ν n s - μ n s t
  ν_flip : ∀ n s, ν n (flip s) = ν n s
  μ_flip : ∀ n s t, μ n (flip s) (flip t) = μ n s t
  γ_flip : ∀ n s t, γ n (flip s) (flip t) = γ n s t
  signed_balance : ∀ n r, ∑ t, character r t * ν n t = 0
  covariance_posDef : ∀ n s, (conditionalCovariance n s).PosDef

/-- Closed assembly: all internal prerequisites have been proved and supplied. -/
theorem main : UniversalRecursionTheorem where
  initial_ν := ν_zero
  initial_μ := μ_zero
  initial_γ := γ_zero
  positive := ν_positive
  total := ν_total
  symmetric := μ_symmetric
  cone := weightedRow_mem
  history_mass n s := by
    rw [dayLaw, measure_congr (historyEvent_ae_eq_cone s (ν n) (ν_positive n) (γ n s))]
    exact history_mass_pos s (ν n) (ν_positive n) (γ n s)
  child_mass n s b := by
    rw [dayLaw, measure_congr (childEvent_ae_eq_cone s b (ν n) (ν_positive n) (γ n s))]
    exact child_mass_pos s b (ν n) (ν_positive n) (γ n s)
  history_probability n s := (historyLaw_regular n s).probability
  history_moments n s := (historyLaw_regular n s).memLp_two
  child_probability n s b := (childLaw_regular n s b).probability
  child_moments n s b := (childLaw_regular n s b).memLp_two
  mean_identity := history_mean_coordinate
  proportions := ν_recursion_events
  corrections := μ_recursion_events
  ν_flip := ν_flip
  μ_flip := μ_flip
  γ_flip := γ_flip
  signed_balance := ν_signed_sum
  covariance_posDef := universal_conditional_covariance_posDef

end MajorityDynamics.Universal
