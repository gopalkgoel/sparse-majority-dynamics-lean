import MajorityDynamics.Idealized.Logit
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Appendix A.2: explicit uniform targets

These are target propositions, not axioms. Proofs are supplied separately. Constants and
thresholds precede every varying density, trial count, and tilt. Monomials
are represented by a coefficient and their coordinate exponents. Natural
trial counts suffice in the eventual regime of the manuscript.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Binomial.Approximation

def Density (θ T : ℝ) (n : ℕ) (p : Probability) : Prop :=
  T⁻¹ * (n : ℝ) ^ (-θ) < (p : ℝ) ∧ (p : ℝ) < T * (n : ℝ) ^ (-θ)

def scale (n : ℕ) (p : Probability) : ℝ := Real.sqrt ((p : ℝ) * n)

def pointMass (m k : ℕ) (q : Probability) : ℝ :=
  (ProbabilityTheory.binomial m (closedProbability q)).real {k}

/-- The Gamma continuation of `x!`. -/
def factorial (x : ℝ) : ℝ := Real.Gamma (x + 1)

def pointSlope (n m : ℕ) (p q : Probability) : ℝ :=
  (q : ℝ) * ((m : ℝ) - (p : ℝ) * n) / ((1 - (q : ℝ)) * ((p : ℝ) * n))

/-- Both tiers of `lem:binomial_estimate`, with nonzero positive normalizations
and multiplicative errors stated as absolute inequalities. -/
def PointEstimateTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : Probability,
  Density θ T n p → ∀ m : ℕ, ∀ q : Probability,
  |(m : ℝ) - n| < T * n / scale n p →
  |(q : ℝ) - p| < T * (p : ℝ) / scale n p →
  ∃ N₁ N₂ : ℝ, 0 < N₁ ∧ 0 < N₂ ∧ ∀ k : ℕ,
  |(k : ℝ) - (p : ℝ) * n| ≤ scale n p * Real.log n →
  let x := (k : ℝ) - (p : ℝ) * n
  let v := (p : ℝ) * n
  let κ := pointSlope n m p q
  let F := N₁ * κ ^ x * (factorial v * v ^ x / factorial k)
  let G := N₂ * Real.exp (-((x - scale n p * Real.log κ * scale n p) ^ 2) / (2 * v))
  |pointMass m k q - F| ≤ C * (p : ℝ) * (Real.log n) ^ 2 * |F| ∧
  |pointMass m k q - G| ≤ C * (Real.log n) ^ 3 / scale n p * |G|

def monomial {d : ℕ} (c : ℝ) (e : Fin d → ℕ) (x : Fin d → ℝ) : ℝ :=
  c * ∏ i, x i ^ e i

def centered {d : ℕ} (p : Probability) (ref : Fin d → ℕ) (a : Fin d → ℕ) : Fin d → ℝ :=
  fun i => (a i : ℝ) - (p : ℝ) * ref i

def Sizes {d : ℕ} (T : ℝ) (n : ℕ) (η : Fin d → ℕ) : Prop :=
  ∀ i, T⁻¹ * n < (η i : ℝ) ∧ (η i : ℝ) < T * n

def OrthogonalRows {r d : ℕ} (M : Fin r → Fin d → ℤ) : Prop :=
  (∀ j, ∃ i, M j i ≠ 0) ∧ ∀ j k, j ≠ k → ∑ i, M j i * M k i = 0

def gaussianLaw {d : ℕ} (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ) :
    Measure (Fin d → ℝ) :=
  Measure.pi fun i => ProbabilityTheory.gaussianReal
    (Real.sqrt ((p : ℝ) * η i) * α i) ⟨(p : ℝ) * η i, mul_nonneg p.property.1.le (Nat.cast_nonneg _)⟩

def gaussianEvent {r d : ℕ} (M : Fin r → Fin d → ℤ)
    (p : Probability) (η : Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ j, -(p : ℝ) * (∑ i, (M j i : ℝ) * η i) ≤ ∑ i, (M j i : ℝ) * x i}

def gaussianTilt {d : ℕ} (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ) :
    Fin d → Probability :=
  fun i => Idealized.logistic (logOdds p + α i / Real.sqrt ((p : ℝ) * η i))

/-- `thm:general_poly_calc`: actual product laws, integer orthogonal normals,
literal mixed binomial inequalities, and the paper's logarithmic error power. -/
def GaussianComparisonTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → ∀ d : ℕ, 0 < d →
  ∀ r : ℕ, ∀ M : Fin r → Fin d → ℤ, OrthogonalRows M →
  ∀ strict : Fin r → Bool, ∀ c : ℝ, ∀ e : Fin d → ℕ,
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : Probability,
  Density θ T n p → ∀ η : Fin d → ℕ, Sizes T n η →
  (∀ j, |∑ i, (M j i : ℝ) * η i| < T * n / scale n p) →
  ∀ α : Fin d → ℝ, (∀ i, |α i| < T) →
  |(∫ a in inequalityEvent (fun j i => (M j i : ℝ)) strict,
      monomial c e (centered p η a) ∂law η (gaussianTilt p η α)) -
    (∫ x in gaussianEvent M p η, monomial c e x ∂gaussianLaw p η α)| ≤
      C * (scale n p) ^ (((∑ i, e i : ℕ) : ℝ) - 1) * (Real.log n) ^ (3 + (∑ i, e i) + d)

def tiltDifference {d : ℕ} (p : Probability) (ref old new : Fin d → ℕ)
    (q₀ q₁ : Fin d → Probability) (i : Fin d) : ℝ :=
  Real.log (((q₁ i : ℝ) / (1 - (q₁ i : ℝ)) * ((new i : ℝ) - (p : ℝ) * ref i)) /
    ((q₀ i : ℝ) / (1 - (q₀ i : ℝ)) * ((old i : ℝ) - (p : ℝ) * ref i)))

def moment {r d : ℕ} (M : Fin r → Fin d → ℝ) (strict : Fin r → Bool)
    (p : Probability) (ref trials : Fin d → ℕ) (q : Fin d → Probability)
    (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ a in inequalityEvent M strict, f (centered p ref a) ∂law trials q

/-- `thm:tilted_expansion`. The reference, old, and new trial vectors are
distinct parameters. The first moments in the normalization correction are
unconditional; no condition on `M * ref` is imposed. -/
def TiltedExpansionTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → ∀ d : ℕ, 0 < d →
  ∀ r : ℕ, ∀ M : Fin r → Fin d → ℝ, ∀ strict : Fin r → Bool,
  ∀ c : ℝ, ∀ e : Fin d → ℕ,
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : Probability,
  Density θ T n p → ∀ ref old new : Fin d → ℕ, Sizes T n ref →
  (∀ i, 0 < old i ∧ 0 < new i) →
  (∀ i, |(old i : ℝ) - ref i| < T * n / scale n p ∧
    |(new i : ℝ) - ref i| < T * n / scale n p) →
  ∀ q₀ q₁ : Fin d → Probability,
  (∀ i, |(q₀ i : ℝ) - p| < T * (p : ℝ) / scale n p ∧
    |(q₁ i : ℝ) - p| < T * (p : ℝ) / scale n p) →
  ‖tiltDifference p ref old new q₀ q₁‖ < T / (scale n p * (Real.log n) ^ 2) →
  let β := tiltDifference p ref old new q₀ q₁
  let F := monomial c e
  let E₀ := moment M strict p ref old q₀ F
  |moment M strict p ref new q₁ F - E₀ -
    (∑ i, β i * moment M strict p ref old q₀ (fun x => x i * F x)) +
    (∑ i, β i * (∫ a, centered p ref a i ∂law old q₀) * E₀)| ≤
      C * max (p : ℝ) (‖β‖ ^ 2 * ((p : ℝ) * n) * (Real.log n) ^ 2) *
        (scale n p) ^ (∑ i, e i) * (Real.log n) ^ (2 + ∑ i, e i)

/-- Completion requires all three original endpoints, not just helper bounds. -/
def AppendixA2Theorem : Prop :=
  PointEstimateTheorem ∧ GaussianComparisonTheorem ∧ TiltedExpansionTheorem

end MajorityDynamics.Binomial.Approximation
