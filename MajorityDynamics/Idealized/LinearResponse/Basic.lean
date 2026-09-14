import MajorityDynamics.Idealized.Process.Main
import MajorityDynamics.Idealized.RowLimits.Main
import MajorityDynamics.Universal.Section4

/-!
# Lemma E.4 (`lem:tilt-vs-linear-map`): the concrete contract

Conventions follow the rest of the project: the level index `n` is the paper's
day `k = n + 1`, so `History (n + 1)` is the coordinate type `{0,1}^k`,
`√(pN)^{k-1} = √(pN)^n`, and `Universal.φStar n` is the paper's `φ*_k`.

* `effectiveTilt` is the paper's `q^σ`, defined by the logistic of
  `logit λ̃[s,t] + log((ñ[t] - 1_{s=t} - pñ[t]) / (n[t] - 1_{s=t} - pñ[t])) + τβ₀σ[t]`;
  the trial-count correction is part of the definition, and
  `ResponseConclusion.tilt_equation` is the paper's displayed exact equation.
* All row quantities (`historyMass`, `historyMean`, `childMean`,
  `splitProbability`, `historyCovariance`) are finite formulas for the actual
  product-binomial law `Binomial.law (Local.trials sizes s) q` on the literal
  tie-aware supports `Local.historySupport`/`Local.childSupport`; see
  `Binomial.conditionalMean_eq_integral` and `Binomial.conditionalLaw_event`.
* The Gaussian side uses the actual universal conditioned laws `historyLaw`,
  `childLaw`, the centered covariance `conditionalCovariance`, and `ν`.
* The reference process is the actual Theorem 5.2 process, selected once by
  `referenceData` from `Process.idealized_process_real`.

Clause map to the paper: `tilt_bound` and `smooth` are the introductory
assertions; `mean_response` is (i); `split_response` is (ii);
`child_mean_response` is (iii); `history_nondegenerate` and
`split_nondegenerate` are (iv).
-/

noncomputable section
open scoped BigOperators ContDiff

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal

/-- `D_θ = ⌊1/(1-θ)⌋ + 1`, the horizon of Theorem 5.2 used by the lemma. -/
def responseHorizon (θ : ℝ) : ℕ := ⌊1 / (1 - θ)⌋₊ + 1

theorem responseHorizon_pos (θ : ℝ) : 1 ≤ responseHorizon θ := Nat.le_add_left 1 _

/-- `κ = ½ min{c₁, θ/2, (1-θ)/2}` with `c₁ = (1 - k(1-θ))/2`, `k = n + 1`. -/
def responseRate (θ : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * min ((1 - ((n : ℝ) + 1) * (1 - θ)) / 2) (min (θ / 2) ((1 - θ) / 2))

/-- `β₀ = √(pN)^{k-1} / √N`. -/
def betaScale (N : ℕ) (p : ℝ) (n : ℕ) : ℝ := Real.sqrt (p * (N : ℝ)) ^ n / Real.sqrt (N : ℝ)

/-- `√N √(pN)^{k-1}`, the size tolerance. -/
def sizeScale (N : ℕ) (p : ℝ) (n : ℕ) : ℝ := Real.sqrt (N : ℝ) * Real.sqrt (p * (N : ℝ)) ^ n

variable {n : ℕ}

def diagonal (s t : History (n + 1)) : ℝ := if s = t then 1 else 0

/-- `n[t] - 1_{s=t} - p ñ[t]`, the residual trial count around the center `p ñ[t]`. -/
def residual (p : ℝ) (ref sizes : Local.Sizes n) (s t : History (n + 1)) : ℝ :=
  (sizes t : ℝ) - diagonal s t - p * (ref t : ℝ)

/-- The paper's `q^σ`. -/
def effectiveTilt (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) : History (n + 1) → Binomial.Probability :=
  fun t => Idealized.logistic (Binomial.logOdds (reference t) +
    Real.log (residual (p : ℝ) ref ref s t / residual (p : ℝ) ref sizes s t) +
    τ * betaScale N (p : ℝ) n * σ t)

theorem logOdds_effectiveTilt (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) (t : History (n + 1)) :
    Binomial.logOdds (effectiveTilt N p ref reference sizes s τ σ t) =
      Binomial.logOdds (reference t) +
        Real.log (residual (p : ℝ) ref ref s t / residual (p : ℝ) ref sizes s t) +
        τ * betaScale N (p : ℝ) n * σ t :=
  Idealized.logOdds_logistic _

/-! ### Finite quantities of the actual row law -/

def historyMass (sizes : Local.Sizes n) (s : History (n + 1))
    (q : History (n + 1) → Binomial.Probability) : ℝ :=
  Binomial.eventMass (Local.trials sizes s) q (Local.historySupport sizes s)

def childMass (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (q : History (n + 1) → Binomial.Probability) : ℝ :=
  Binomial.eventMass (Local.trials sizes s) q (Local.childSupport sizes s b)

def historyMean (sizes : Local.Sizes n) (s : History (n + 1))
    (q : History (n + 1) → Binomial.Probability) (t : History (n + 1)) : ℝ :=
  Binomial.conditionalMean (Local.trials sizes s) q (Local.historySupport sizes s) t

def childMean (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (q : History (n + 1) → Binomial.Probability) (t : History (n + 1)) : ℝ :=
  Binomial.conditionalMean (Local.trials sizes s) q (Local.childSupport sizes s b) t

/-- `P[J_{sb} | I_s]` for the actual row law. -/
def splitProbability (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (q : History (n + 1) → Binomial.Probability) : ℝ :=
  childMass sizes s b q / historyMass sizes s q

/-- Centered conditional covariance given `I_s`. -/
def historyCovariance (sizes : Local.Sizes n) (s : History (n + 1))
    (q : History (n + 1) → Binomial.Probability) (t t' : History (n + 1)) : ℝ :=
  (∑ a ∈ Local.historySupport sizes s, Binomial.mass (Local.trials sizes s) q a *
      (Binomial.vector a t * Binomial.vector a t')) / historyMass sizes s q -
    historyMean sizes s q t * historyMean sizes s q t'

theorem historyMean_eq_rowMean (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s t : History (n + 1)) : historyMean sizes s (q s) t = Local.rowMean sizes q s t := rfl

/-- The effective tilt of a row of a process. -/
def processEffectiveTilt (N : ℕ) (p : Binomial.Probability) (a : Process.Data) (n : ℕ)
    (sizes : Local.Sizes n) (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) :
    History (n + 1) → Binomial.Probability :=
  effectiveTilt N p (a.state n).sizes (a.tilt n s) sizes s τ σ

/-! ### Gaussian side -/

/-- `(Σ_s σ)[t]`. -/
def covarianceAction (n : ℕ) (s : History (n + 1)) (σ : Row (n + 1)) (t : History (n + 1)) : ℝ :=
  ∑ t', conditionalCovariance n s t t' * σ t'

/-- `(ν[sb]/ν[s]) Σ_{t'} σ[t'] (E[W_{t'} | J_{sb}] - E[W_{t'} | I_s])`. -/
def gaussianSplitResponse (n : ℕ) (s : History (n + 1)) (b : Bool) (σ : Row (n + 1)) : ℝ :=
  ν (n + 1) (append s b) / ν n s *
    ∑ t', σ t' * ((∫ x, x t' ∂childLaw n s b) - (∫ x, x t' ∂historyLaw n s))

/-! ### Smoothness -/

structure SmoothResponseQuantities (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) : Prop where
  tilt : ∀ t, ContDiff ℝ ∞
    (fun σ : Row (n + 1) => (effectiveTilt N p ref reference sizes s τ σ t : ℝ))
  history_mass : ContDiff ℝ ∞
    (fun σ : Row (n + 1) => historyMass sizes s (effectiveTilt N p ref reference sizes s τ σ))
  child_mass : ∀ b, ContDiff ℝ ∞
    (fun σ : Row (n + 1) => childMass sizes s b (effectiveTilt N p ref reference sizes s τ σ))
  split : ∀ b, ContDiff ℝ ∞
    (fun σ : Row (n + 1) => splitProbability sizes s b (effectiveTilt N p ref reference sizes s τ σ))
  history_mean : ∀ t, ContDiff ℝ ∞
    (fun σ : Row (n + 1) => historyMean sizes s (effectiveTilt N p ref reference sizes s τ σ) t)
  child_mean : ∀ b t, ContDiff ℝ ∞
    (fun σ : Row (n + 1) => childMean sizes s b (effectiveTilt N p ref reference sizes s τ σ) t)
  covariance : ∀ t t', ContDiff ℝ ∞
    (fun σ : Row (n + 1) => historyCovariance sizes s (effectiveTilt N p ref reference sizes s τ σ) t t')

/-! ### The conclusion of Lemma E.4 for one row -/

/-- Every clause of `lem:tilt-vs-linear-map` for the row `s`, the reference
process `a` at level `n`, actual sizes `sizes`, and lead parameter `τ`. -/
structure ResponseConclusion (N : ℕ) (p : Binomial.Probability) (a : Process.Data) (n : ℕ)
    (sizes : Local.Sizes n) (s : History (n + 1)) (τ R C κ : ℝ) : Prop where
  reference_residual_pos : ∀ t, 0 < residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t
  residual_pos : ∀ t, 0 < residual (p : ℝ) (a.state n).sizes sizes s t
  tilt_in_unit : ∀ (σ : Row (n + 1)) t,
    0 < (processEffectiveTilt N p a n sizes s τ σ t : ℝ) ∧
      (processEffectiveTilt N p a n sizes s τ σ t : ℝ) < 1
  tilt_bound : ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ t,
    |(processEffectiveTilt N p a n sizes s τ σ t : ℝ) - p| ≤
      C * (p : ℝ) / Real.sqrt ((p : ℝ) * N)
  tilt_equation : ∀ (σ : Row (n + 1)) t,
    Binomial.logOdds (processEffectiveTilt N p a n sizes s τ σ t) +
        Real.log (residual (p : ℝ) (a.state n).sizes sizes s t /
          ((p : ℝ) * ((a.state n).sizes t : ℝ))) =
      Binomial.logOdds (a.tilt n s t) +
        Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
          ((p : ℝ) * ((a.state n).sizes t : ℝ))) +
        τ * betaScale N (p : ℝ) n * σ t
  smooth : SmoothResponseQuantities N p (a.state n).sizes (a.tilt n s) sizes s τ
  mean_response : ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ t,
    |(historyMean sizes s (processEffectiveTilt N p a n sizes s τ σ) t -
        (a.state n).edges s t / ((a.state n).sizes s : ℝ)) /
        (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) - covarianceAction n s σ t| ≤
      C * (N : ℝ) ^ (-κ)
  split_response : ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ b,
    |(splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) -
        splitProbability (a.state n).sizes s b (a.tilt n s)) /
        (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) -
        gaussianSplitResponse n s b σ| ≤ C * (N : ℝ) ^ (-κ)
  child_mean_response : ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ b t,
    |childMean sizes s b (processEffectiveTilt N p a n sizes s τ σ) t -
        childMean (a.state n).sizes s b (a.tilt n s) t| ≤
      C * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))
  history_nondegenerate : ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
    φStar n / 4 ≤ historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ)
  split_nondegenerate : ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ b,
    φStar n / 2 ≤ splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) ∧
      splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) ≤ 1 - φStar n / 2

/-! ### Selection of the reference process (Theorem 5.2) -/

theorem processExistence (θ T : ℝ) (h : 1 / 2 < θ ∧ θ < 1 ∧ 1 < T) :
    ∃ ell : ℕ, 1 ≤ ell ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
        ∃ hp : 0 < p ∧ p < 1, ∃ a : Process.Data,
          Process.Specification N ⟨p, hp⟩ (responseHorizon θ) ell a ∧
            ∀ b : Process.Data, Process.Recursion N ⟨p, hp⟩ (responseHorizon θ) b →
              Process.AgreeThrough (responseHorizon θ) a b :=
  Process.idealized_process_real θ h.1 h.2.1 (responseHorizon θ) (responseHorizon_pos θ) T h.2.2

open scoped Classical in
/-- The logarithmic exponent of the selected Theorem 5.2 process; fixed before `N`. -/
def processExponent (θ T : ℝ) : ℕ :=
  if h : 1 / 2 < θ ∧ θ < 1 ∧ 1 < T then (processExistence θ T h).choose else 1

open scoped Classical in
/-- The threshold of the selected Theorem 5.2 process; fixed before `N`. -/
def processThreshold (θ T : ℝ) : ℕ :=
  if h : 1 / 2 < θ ∧ θ < 1 ∧ 1 < T then (processExistence θ T h).choose_spec.2.choose else 1

def defaultProbability : Binomial.Probability := ⟨1 / 2, by norm_num, by norm_num⟩

def defaultData : Process.Data where
  state _ := { sizes := fun _ => 0, edges := fun _ _ => 0 }
  tilt _ := fun _ _ => defaultProbability

open scoped Classical in
/-- The reference idealized process. Inside the range of Theorem 5.2 it is a
process with the selected specification; the fallback is never used there. -/
def referenceData (θ T : ℝ) (N : ℕ) (p : Binomial.Probability) : Process.Data :=
  if h : ∃ a : Process.Data,
      Process.Specification N p (responseHorizon θ) (processExponent θ T) a then
    h.choose
  else defaultData

open scoped Classical in
/-- Total real-density version of the selection. -/
def referenceDataReal (θ T : ℝ) (N : ℕ) (p : ℝ) : Process.Data :=
  if hp : 0 < p ∧ p < 1 then referenceData θ T N ⟨p, hp⟩ else defaultData

/-! ### The public statements -/

/-- Lemma E.4 for every process satisfying the Theorem 5.2 specification with a
given exponent `ell`; constants and thresholds follow `θ, n, T, R, ell`. -/
def LinearResponseSpecTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
  ∀ T R : ℝ, 1 < T → 0 < R → ∀ ell : ℕ, 1 ≤ ell →
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : Binomial.Probability, Binomial.Approximation.Density θ T N p →
  ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
  ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
  ∀ sizes : Local.Sizes n,
    (∀ t, |(sizes t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ T * sizeScale N (p : ℝ) n) →
  ∀ s : History (n + 1), ResponseConclusion N p a n sizes s τ R C (responseRate θ n)

/-- Lemma E.4 with the actual selected process exponent. -/
def LinearResponseTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
  ∀ T R : ℝ, 1 < T → 0 < R →
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : Binomial.Probability, Binomial.Approximation.Density θ T N p →
  ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) (processExponent θ T) a →
  ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
  ∀ sizes : Local.Sizes n,
    (∀ t, |(sizes t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ T * sizeScale N (p : ℝ) n) →
  ∀ s : History (n + 1), ResponseConclusion N p a n sizes s τ R C (responseRate θ n)

/-- The literal real-density, integer-size statement with the constructed
reference process. The rate `κ` is fixed before `T` and `R`; `p ∈ (0,1)`, the
positivity of the integer sizes, and all trial-count positivity are derived. -/
def LinearResponseRealTheorem : Prop :=
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
          (fun t => (η t).toNat) s τ R C κ

end MajorityDynamics.Idealized.LinearResponse
