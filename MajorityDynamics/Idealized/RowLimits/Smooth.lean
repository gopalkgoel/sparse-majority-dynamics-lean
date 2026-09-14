import MajorityDynamics.Idealized.RowLimits.Basic
import MajorityDynamics.Idealized.Logit
import MajorityDynamics.Local.RowModel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smoothness of the actual finite binomial law under logit tilts.
The support is fixed as the tilt varies. Even the null-event convention is
smooth: an empty fixed support has identically zero conditional moments. -/

noncomputable section
open scoped BigOperators ContDiff

namespace MajorityDynamics.Idealized.RowLimits

open Binomial

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_logistic {r : ℕ∞} {g : E → ℝ} (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun x => (logistic (g x) : ℝ)) := by
  exact hg.exp.div (contDiff_const.add hg.exp) (fun x => ne_of_gt (by positivity))

theorem contDiff_logitTilt {r : ℕ∞} (N : ℕ) (p : Probability) (v : ℝ)
    {g : E → ℝ} (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun x => (logitTilt N p (g x) v : ℝ)) :=
  contDiff_logistic (contDiff_const.add (hg.div_const _))

theorem contDiff_mass {r : ℕ∞} (η : ι → ℕ) (q : E → ι → Probability)
    (hq : ∀ i, ContDiff ℝ r (fun x => (q x i : ℝ))) (a : Box η) :
    ContDiff ℝ r (fun x => mass η (q x) a) := by
  unfold mass
  exact contDiff_prod fun i _ => (contDiff_const.mul ((hq i).pow _)).mul
    ((contDiff_const.sub (hq i)).pow _)

theorem contDiff_eventMass {r : ℕ∞} (η : ι → ℕ) (q : E → ι → Probability)
    (hq : ∀ i, ContDiff ℝ r (fun x => (q x i : ℝ))) (S : Finset (Box η)) :
    ContDiff ℝ r (fun x => eventMass η (q x) S) := by
  exact ContDiff.sum fun a _ => contDiff_mass η q hq a

theorem contDiff_expectation {r : ℕ∞} (η : ι → ℕ) (q : E → ι → Probability)
    (hq : ∀ i, ContDiff ℝ r (fun x => (q x i : ℝ))) (S : Finset (Box η))
    (f : E → Box η → ℝ) (hf : ∀ a, ContDiff ℝ r (fun x => f x a)) :
    ContDiff ℝ r (fun x => expectation η (q x) S (f x)) := by
  classical
  by_cases hS : S.Nonempty
  · apply ContDiff.sum
    intro a ha
    exact ((contDiff_mass η q hq a).div (contDiff_eventMass η q hq S)
      (fun x => (eventMass_pos η (q x) hS).ne')).mul (hf a)
  · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hS', expectation, Finset.sum_empty]
    exact contDiff_const

theorem contDiff_eventRatio {r : ℕ∞} (η : ι → ℕ) (q : E → ι → Probability)
    (hq : ∀ i, ContDiff ℝ r (fun x => (q x i : ℝ))) (S T : Finset (Box η)) :
    ContDiff ℝ r (fun x => eventMass η (q x) T / eventMass η (q x) S) := by
  classical
  by_cases hS : S.Nonempty
  · exact (contDiff_eventMass η q hq T).div (contDiff_eventMass η q hq S)
      (fun x => (eventMass_pos η (q x) hS).ne')
  · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hS', eventMass, Finset.sum_empty, div_zero]
    exact contDiff_const

theorem contDiff_conditionalMean {r : ℕ∞} (η : ι → ℕ) (q : E → ι → Probability)
    (hq : ∀ i, ContDiff ℝ r (fun x => (q x i : ℝ))) (S : Finset (Box η)) (i : ι) :
    ContDiff ℝ r (fun x => conditionalMean η (q x) S i) :=
  contDiff_expectation η q hq S (fun _ a => vector a i) (fun _ => contDiff_const)

/-- Centered conditional covariance of any two smooth observables. -/
theorem contDiff_conditionalCovariance {r : ℕ∞} (η : ι → ℕ)
    (q : E → ι → Probability)
    (hq : ∀ i, ContDiff ℝ r (fun x => (q x i : ℝ))) (S : Finset (Box η))
    (f g : E → Box η → ℝ)
    (hf : ∀ a, ContDiff ℝ r (fun x => f x a))
    (hg : ∀ a, ContDiff ℝ r (fun x => g x a)) :
    ContDiff ℝ r (fun x => expectation η (q x) S (fun a =>
      (f x a - expectation η (q x) S (f x)) *
      (g x a - expectation η (q x) S (g x)))) := by
  apply contDiff_expectation η q hq S
  intro a
  exact ((hf a).sub (contDiff_expectation η q hq S f hf)).mul
    ((hg a).sub (contDiff_expectation η q hq S g hg))

/-- Coordinate logit parameters are smooth on the entire Euclidean parameter
space; neither positive trial counts nor positive scale denominators are needed
for this algebraic statement. -/
theorem contDiff_coordinateTilt {r : ℕ∞} (N : ℕ) (p : Probability)
    (ν : ι → ℝ) (i : ι) :
    ContDiff ℝ r (fun σ : ι → ℝ => (logitTilt N p (σ i) (ν i) : ℝ)) :=
  contDiff_logitTilt N p (ν i) (contDiff_apply ℝ ℝ i)

open Universal

variable {n : ℕ}

theorem contDiff_rowTilt (N : ℕ) (p : Probability) (t : History (n + 1)) :
    ContDiff ℝ ∞ (fun σ : Row (n + 1) => (rowTilt N p σ t : ℝ)) :=
  contDiff_logitTilt N p (ν n t) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : History (n + 1) => ℝ) t).contDiff

theorem contDiff_binomialMass (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Box (Local.trials sizes s))) :
    ContDiff ℝ ∞ (binomialMass N p sizes s S) :=
  contDiff_eventMass _ _ (contDiff_rowTilt N p) S

theorem contDiff_binomialMean (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Box (Local.trials sizes s))) (t : History (n + 1)) :
    ContDiff ℝ ∞ (binomialMean N p sizes s S t) := by
  classical
  have h := contDiff_expectation (Local.trials sizes s) (rowTilt N p)
    (contDiff_rowTilt N p) S (fun _ a => vector a t) (fun _ => contDiff_const)
  change ContDiff ℝ ∞ (fun σ => binomialMean N p sizes s S t σ)
  simpa only [binomialMean, binomialFirst, binomialMass, expectation, conditionalWeight,
    Finset.sum_div, div_mul_eq_mul_div] using h

theorem contDiff_binomialCovariance (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Box (Local.trials sizes s)))
    (t t' : History (n + 1)) :
    ContDiff ℝ ∞ (binomialCovariance N p sizes s S t t') := by
  classical
  have h := contDiff_expectation (Local.trials sizes s) (rowTilt N p)
    (contDiff_rowTilt N p) S (fun _ a => vector a t * vector a t')
    (fun _ => contDiff_const)
  have hsecond : ContDiff ℝ ∞ (fun σ =>
      binomialSecond N p sizes s S t t' σ / binomialMass N p sizes s S σ) := by
    simpa only [binomialSecond, binomialMass, expectation, conditionalWeight,
      Finset.sum_div, div_mul_eq_mul_div] using h
  exact hsecond.sub ((contDiff_binomialMean N p sizes s S t).mul
    (contDiff_binomialMean N p sizes s S t'))

/-- The complete smoothness clause of Lemma E.3, with no asymptotic assumptions. -/
theorem smooth_quantities (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) : SmoothQuantities N p sizes s where
  history_mass := contDiff_binomialMass N p sizes s _
  child_mass _b := contDiff_binomialMass N p sizes s _
  split _b := contDiff_eventRatio _ _ (contDiff_rowTilt N p) _ _
  history_mean t := contDiff_binomialMean N p sizes s _ t
  child_mean _b t := contDiff_binomialMean N p sizes s _ t
  covariance t t' := contDiff_binomialCovariance N p sizes s _ t t'

end MajorityDynamics.Idealized.RowLimits
