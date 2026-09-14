import MajorityDynamics.Idealized.LinearResponse.Main

/-!
# Lemma E.4 endpoint checks

Exact type checks of the public endpoints, an independently written expansion
of the statements (so that the actual quantifier order and conclusions are
visible here, not only through the definitions), and guarded axiom audits.
-/

open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal

example : LinearResponseSpecTheorem := linear_response_spec
example : LinearResponseTheorem := linear_response
example : LinearResponseRealTheorem := linear_response_real

/-- The natural-parameter statement, expanded. -/
example :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
    ∀ T R : ℝ, 1 < T → 0 < R →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : Binomial.Probability, Binomial.Approximation.Density θ T N p →
    ∀ a : Process.Data,
      Process.Specification N p (responseHorizon θ) (processExponent θ T) a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ sizes : Local.Sizes n,
      (∀ t, |(sizes t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ T * sizeScale N (p : ℝ) n) →
    ∀ s : History (n + 1),
      (∀ t, 0 < residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t) ∧
      (∀ t, 0 < residual (p : ℝ) (a.state n).sizes sizes s t) ∧
      (∀ (σ : Row (n + 1)) t,
        0 < (processEffectiveTilt N p a n sizes s τ σ t : ℝ) ∧
          (processEffectiveTilt N p a n sizes s τ σ t : ℝ) < 1) ∧
      (∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ t,
        |(processEffectiveTilt N p a n sizes s τ σ t : ℝ) - p| ≤
          C * (p : ℝ) / Real.sqrt ((p : ℝ) * N)) ∧
      (∀ (σ : Row (n + 1)) t,
        Binomial.logOdds (processEffectiveTilt N p a n sizes s τ σ t) +
            Real.log (residual (p : ℝ) (a.state n).sizes sizes s t /
              ((p : ℝ) * ((a.state n).sizes t : ℝ))) =
          Binomial.logOdds (a.tilt n s t) +
            Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
              ((p : ℝ) * ((a.state n).sizes t : ℝ))) +
            τ * betaScale N (p : ℝ) n * σ t) ∧
      SmoothResponseQuantities N p (a.state n).sizes (a.tilt n s) sizes s τ ∧
      (∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ t,
        |(historyMean sizes s (processEffectiveTilt N p a n sizes s τ σ) t -
            (a.state n).edges s t / ((a.state n).sizes s : ℝ)) /
            (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) -
          ∑ t', conditionalCovariance n s t t' * σ t'| ≤
          C * (N : ℝ) ^ (-responseRate θ n)) ∧
      (∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ b,
        |(splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) -
            splitProbability (a.state n).sizes s b (a.tilt n s)) /
            (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) -
          ν (n + 1) (append s b) / ν n s *
            ∑ t', σ t' * ((∫ x, x t' ∂childLaw n s b) - (∫ x, x t' ∂historyLaw n s))| ≤
          C * (N : ℝ) ^ (-responseRate θ n)) ∧
      (∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ b t,
        |childMean sizes s b (processEffectiveTilt N p a n sizes s τ σ) t -
            childMean (a.state n).sizes s b (a.tilt n s) t| ≤
          C * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) ∧
      (∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
        φStar n / 4 ≤ historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ)) ∧
      (∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ b,
        φStar n / 2 ≤ splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) ∧
          splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) ≤
            1 - φStar n / 2) := by
  intro θ hθlo hθhi n hk T R hT hR
  obtain ⟨C, hC, N₀, hN₀, h⟩ := linear_response θ hθlo hθhi n hk T R hT hR
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N hN p hp a hspec τ hτ₁ hτ₂ sizes hclose s
  have hc := h N hN p hp a hspec τ hτ₁ hτ₂ sizes hclose s
  exact ⟨hc.reference_residual_pos, hc.residual_pos, hc.tilt_in_unit, hc.tilt_bound,
    hc.tilt_equation, hc.smooth, hc.mean_response, hc.split_response, hc.child_mean_response,
    hc.history_nondegenerate, hc.split_nondegenerate⟩

/-- The real-density statement, expanded: the rate precedes `T, R`; the
process is the constructed Theorem 5.2 process; `p ∈ (0,1)` and the positivity of
the integer sizes are conclusions. -/
example :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
    ∃ κ : ℝ, κ = responseRate θ n ∧ 0 < κ ∧
    ∀ T R : ℝ, 1 < T → 0 < R →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
    ∃ hp : 0 < p ∧ p < 1,
      referenceDataReal θ T N p = referenceData θ T N ⟨p, hp⟩ ∧
      Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
        (referenceDataReal θ T N p) ∧
      (∀ b : Process.Data, Process.Recursion N ⟨p, hp⟩ (responseHorizon θ) b →
        Process.AgreeThrough (responseHorizon θ) (referenceDataReal θ T N p) b) ∧
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ,
        (∀ t, |(η t : ℝ) - (((referenceDataReal θ T N p).state n).sizes t : ℝ)| ≤
          T * sizeScale N p n) →
        (∀ t, 0 < η t) ∧ (∀ t, (((η t).toNat : ℕ) : ℝ) = (η t : ℝ)) ∧
        ∀ s : History (n + 1),
          ResponseConclusion N ⟨p, hp⟩ (referenceDataReal θ T N p) n
            (fun t => (η t).toNat) s τ R C κ :=
  linear_response_real

/-- The exact effective-tilt equation, standalone. -/
example {n : ℕ} (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) (t : History (n + 1))
    (href : 0 < residual (p : ℝ) ref ref s t) (hnew : 0 < residual (p : ℝ) ref sizes s t)
    (hcenter : 0 < (p : ℝ) * (ref t : ℝ)) :
    Binomial.logOdds (effectiveTilt N p ref reference sizes s τ σ t) +
        Real.log (residual (p : ℝ) ref sizes s t / ((p : ℝ) * (ref t : ℝ))) =
      Binomial.logOdds (reference t) +
        Real.log (residual (p : ℝ) ref ref s t / ((p : ℝ) * (ref t : ℝ))) +
        τ * betaScale N (p : ℝ) n * σ t :=
  effectiveTilt_equation N p ref reference sizes s τ σ t href hnew hcenter

/-- The A.2 different-trial tilt is exactly `τβ₀σ`. -/
example {n : ℕ} (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1))
    (href : ∀ t, 0 < residual (p : ℝ) ref ref s t)
    (hnew : ∀ t, 0 < residual (p : ℝ) ref sizes s t) :
    Binomial.Approximation.tiltDifference p ref (Local.trials ref s) (Local.trials sizes s)
        reference (effectiveTilt N p ref reference sizes s τ σ) =
      fun t => τ * betaScale N (p : ℝ) n * σ t :=
  effectiveTilt_difference N p ref reference sizes s τ σ href hnew

end MajorityDynamics.Idealized.LinearResponse

/-- info: 'MajorityDynamics.Idealized.LinearResponse.linear_response_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.LinearResponse.linear_response_spec

/-- info: 'MajorityDynamics.Idealized.LinearResponse.linear_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.LinearResponse.linear_response

/-- info: 'MajorityDynamics.Idealized.LinearResponse.linear_response_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.LinearResponse.linear_response_real

/-- info: 'MajorityDynamics.Idealized.LinearResponse.effectiveTilt_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.LinearResponse.effectiveTilt_equation

/-- info: 'MajorityDynamics.Idealized.LinearResponse.effectiveTilt_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.LinearResponse.effectiveTilt_difference
