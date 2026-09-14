import MajorityDynamics.Idealized.LinearResponse.Basic
import MajorityDynamics.Idealized.RowLimits.Smooth

/-! Global smoothness in `σ` of the effective tilt and of every finite-law
quantity of Lemma E.4. Only nonemptiness of the supports is used, so the
statement holds for every size vector with `2n + 5 ≤ sizes t`. -/

noncomputable section
open scoped BigOperators ContDiff

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal
open MajorityDynamics.Idealized.RowLimits (contDiff_logistic contDiff_eventMass
  contDiff_conditionalMean contDiff_eventRatio contDiff_mass)

variable {n : ℕ}

theorem contDiff_effectiveTilt (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (t : History (n + 1)) :
    ContDiff ℝ ∞ (fun σ : Row (n + 1) => (effectiveTilt N p ref reference sizes s τ σ t : ℝ)) := by
  have hproj : ContDiff ℝ ∞ (fun σ : Row (n + 1) => σ t) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : History (n + 1) => ℝ) t).contDiff
  have hg : ContDiff ℝ ∞ (fun σ : Row (n + 1) =>
      Binomial.logOdds (reference t) +
        Real.log (residual (p : ℝ) ref ref s t / residual (p : ℝ) ref sizes s t) +
        τ * betaScale N (p : ℝ) n * σ t) :=
    (contDiff_const.add contDiff_const).add (contDiff_const.mul hproj)
  exact contDiff_logistic hg

theorem smooth_response_quantities (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (hS : (Local.historySupport sizes s).Nonempty) :
    SmoothResponseQuantities N p ref reference sizes s τ := by
  have hq : ∀ t, ContDiff ℝ ∞
      (fun σ : Row (n + 1) => (effectiveTilt N p ref reference sizes s τ σ t : ℝ)) :=
    contDiff_effectiveTilt N p ref reference sizes s τ
  have hmass (S : Finset (Binomial.Box (Local.trials sizes s))) :
      ContDiff ℝ ∞ (fun σ : Row (n + 1) =>
        Binomial.eventMass (Local.trials sizes s) (effectiveTilt N p ref reference sizes s τ σ) S) :=
    contDiff_eventMass (Local.trials sizes s) (fun σ => effectiveTilt N p ref reference sizes s τ σ) hq S
  have hmean (S : Finset (Binomial.Box (Local.trials sizes s))) (t : History (n + 1)) :
      ContDiff ℝ ∞ (fun σ : Row (n + 1) =>
        Binomial.conditionalMean (Local.trials sizes s)
          (effectiveTilt N p ref reference sizes s τ σ) S t) :=
    contDiff_conditionalMean (Local.trials sizes s)
      (fun σ => effectiveTilt N p ref reference sizes s τ σ) hq S t
  have hsecond (t t' : History (n + 1)) :
      ContDiff ℝ ∞ (fun σ : Row (n + 1) =>
        (∑ a ∈ Local.historySupport sizes s,
          Binomial.mass (Local.trials sizes s) (effectiveTilt N p ref reference sizes s τ σ) a *
            (Binomial.vector a t * Binomial.vector a t')) /
          Binomial.eventMass (Local.trials sizes s) (effectiveTilt N p ref reference sizes s τ σ)
            (Local.historySupport sizes s)) := by
    have hnum : ContDiff ℝ ∞ (fun σ : Row (n + 1) =>
        ∑ a ∈ Local.historySupport sizes s,
          Binomial.mass (Local.trials sizes s) (effectiveTilt N p ref reference sizes s τ σ) a *
            (Binomial.vector a t * Binomial.vector a t')) :=
      ContDiff.sum fun a _ => (contDiff_mass (Local.trials sizes s)
        (fun σ => effectiveTilt N p ref reference sizes s τ σ) hq a).mul contDiff_const
    exact hnum.div (hmass (Local.historySupport sizes s))
      (fun σ => (Binomial.eventMass_pos _ (effectiveTilt N p ref reference sizes s τ σ) hS).ne')
  exact
    { tilt := hq
      history_mass := hmass (Local.historySupport sizes s)
      child_mass := fun b => hmass (Local.childSupport sizes s b)
      split := fun b => contDiff_eventRatio (Local.trials sizes s)
        (fun σ => effectiveTilt N p ref reference sizes s τ σ) hq
        (Local.historySupport sizes s) (Local.childSupport sizes s b)
      history_mean := fun t => hmean (Local.historySupport sizes s) t
      child_mean := fun b t => hmean (Local.childSupport sizes s b) t
      covariance := fun t t' => (hsecond t t').sub
        ((hmean (Local.historySupport sizes s) t).mul (hmean (Local.historySupport sizes s) t')) }

end MajorityDynamics.Idealized.LinearResponse
