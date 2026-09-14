import MajorityDynamics.StrongBijection
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Concrete interfaces for Gaussian conditional means

Source: `latest/main.tex`, `lem:open-conditioning`, `thm:orthant-bijection`,
and `cor:cone-bijection`. Definitions and propositions in this file are not
proofs of the analytic assertions. No assertion is installed as an axiom.

The actual Gaussian is Mathlib's `multivariateGaussian`. All laws use the same
centered covariance matrix. `CoreTheorem` excludes the cone corollary so the
core proof can be compiled independently of that corollary.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Covariance (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

variable {d : ℕ}

/-- Matrix action in the Euclidean norm used for differentiation. -/
abbrev matrixCLM (A : Covariance d) : Space d →L[ℝ] Space d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) A

/-- The same invertible matrix action, bundled for the inverse function theorem. -/
def matrixCLE (A : Covariance d) (hA : IsUnit A) : Space d ≃L[ℝ] Space d :=
  ContinuousLinearEquiv.ofUnit (hA.map (Matrix.toEuclideanCLM (𝕜 := ℝ))).unit

@[simp]
theorem matrixCLE_coe (A : Covariance d) (hA : IsUnit A) :
    (matrixCLE A hA : Space d →L[ℝ] Space d) = matrixCLM A :=
  (hA.map (Matrix.toEuclideanCLM (𝕜 := ℝ))).unit_spec

theorem matrixCLM_bijective (A : Covariance d) (hA : IsUnit A) :
    Function.Bijective (matrixCLM A) :=
  ContinuousLinearMap.isUnit_iff_bijective.mp (hA.map (Matrix.toEuclideanCLM (𝕜 := ℝ)))

/-- Normalized restriction. Positive finite mass must be proved by consumers. -/
def condition (μ : Measure (Space d)) (O : Set (Space d)) : Measure (Space d) :=
  (μ O)⁻¹ • μ.restrict O

def mean (ν : Measure (Space d)) : Space d := ∫ x, x ∂ν

/-- Centered covariance, not Mathlib's uncentered `covarianceOperator`. -/
def covMatrix (ν : Measure (Space d)) : Covariance d :=
  fun i j => covariance (fun x => x i) (fun x => x j) ν

def gaussianLaw (S : Covariance d) (γ : Space d) : Measure (Space d) :=
  multivariateGaussian γ S

def conditionalLaw (S : Covariance d) (O : Set (Space d)) (γ : Space d) :=
  condition (gaussianLaw S γ) O

def conditionalMean (S : Covariance d) (O : Set (Space d)) (γ : Space d) :=
  mean (conditionalLaw S O γ)

def conditionalCov (S : Covariance d) (O : Set (Space d)) (γ : Space d) :=
  covMatrix (conditionalLaw S O γ)

def naturalParameter (S : Covariance d) (γ : Space d) : Space d :=
  matrixCLM S⁻¹ γ

def exponent (S : Covariance d) (θ x : Space d) : ℝ :=
  ⟪θ, x⟫ - (1 / 2) * ⟪x, matrixCLM S⁻¹ x⟫

def weight (S : Covariance d) (θ x : Space d) : ℝ :=
  Real.exp (exponent S θ x)

def partition (S : Covariance d) (O : Set (Space d)) (θ : Space d) : ℝ :=
  ∫ x in O, weight S θ x

def logPartition (S : Covariance d) (O : Set (Space d)) (θ : Space d) : ℝ :=
  Real.log (partition S O θ)

def naturalLaw (S : Covariance d) (O : Set (Space d)) (θ : Space d) :=
  (volume.restrict O).tilted (exponent S θ)

def naturalMean (S : Covariance d) (O : Set (Space d)) (θ : Space d) :=
  mean (naturalLaw S O θ)

def naturalCov (S : Covariance d) (O : Set (Space d)) (θ : Space d) :=
  covMatrix (naturalLaw S O θ)

/-- The Jacobian is `C * S⁻¹`: the inverse original covariance acts first. -/
def jacobian (S : Covariance d) (O : Set (Space d)) (γ : Space d) :
    Space d →L[ℝ] Space d :=
  (matrixCLM (conditionalCov S O γ)).comp (matrixCLM S⁻¹)

/-- The common probability/moment interface for the generic conditioning proof. -/
structure RegularOn (ν : Measure (Space d)) (O : Set (Space d)) : Prop where
  probability : IsProbabilityMeasure ν
  memLp_two : MemLp id 2 ν
  mass : ν O = 1
  absolutelyContinuous : ν ≪ volume

/-- D2's generic result; proving this does not assume a Gaussian theorem. -/
def ConditioningTheorem : Prop :=
  ∀ (d : ℕ) (ν : Measure (Space d)) (O : Set (Space d)),
    IsOpen O → Convex ℝ O → RegularOn ν O →
    mean ν ∈ O ∧ (covMatrix ν).PosDef

/-- D1's density bridge, with a positive normalizing constant independent of the mean. -/
def GaussianDensityFormula (S : Covariance d) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ γ : Space d,
    gaussianLaw S γ = volume.withDensity
      (fun x => ENNReal.ofReal (c * weight S 0 (x - γ)))

/-- The law identity, consuming density and partition facts but no calculus theorem. -/
def LawBridge (S : Covariance d) (O : Set (Space d)) : Prop :=
  ∀ γ, naturalLaw S O (naturalParameter S γ) = conditionalLaw S O γ

/-- D3's measure-theoretic outputs before differentiation. -/
structure PartitionFacts (S : Covariance d) (O : Set (Space d)) : Prop where
  integrable_weight : ∀ θ, Integrable (weight S θ) (volume.restrict O)
  partition_pos : ∀ θ, 0 < partition S O θ
  weighted_moments : ∀ θ (n : ℕ),
    Integrable (fun x => ‖x‖ ^ n * weight S θ x) (volume.restrict O)
  natural_regular : ∀ θ, RegularOn (naturalLaw S O θ) O

/-- D3's all-order local domination interface. The bound is uniform in nearby parameters. -/
def LocalDomination (S : Covariance d) (O : Set (Space d)) : Prop :=
  ∀ (θ₀ : Space d) (n : ℕ), ∃ ε : ℝ, 0 < ε ∧
    ∃ bound : Space d → ℝ, Integrable bound (volume.restrict O) ∧
      ∀ θ ∈ Metric.ball θ₀ ε, ∀ x, ‖x‖ ^ n * weight S θ x ≤ bound x

/-- D3's Fréchet calculus outputs, expressed in the shared moment types. -/
structure LogPartitionFacts (S : Covariance d) (O : Set (Space d)) : Prop where
  smooth_logPartition : ContDiff ℝ ∞ (logPartition S O)
  smooth_naturalMean : ContDiff ℝ ∞ (naturalMean S O)
  hasGradientAt : ∀ θ, HasGradientAt (logPartition S O) (naturalMean S O θ) θ
  hasFDerivAt : ∀ θ, HasFDerivAt (naturalMean S O) (matrixCLM (naturalCov S O θ)) θ

/-- D5's uniform linear lower bound, stronger than mere radial divergence. -/
def CoerciveAt (S : Covariance d) (O : Set (Space d)) (y : Space d) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ θ,
    a * ‖θ‖ + b ≤ logPartition S O θ - ⟪θ, y⟫

def MeanSurjective (S : Covariance d) (O : Set (Space d)) : Prop :=
  ∀ y ∈ O, ∃ θ, naturalMean S O θ = y

/-- The concrete A.5/D.2 conclusion for fixed covariance and conditioning set. -/
structure CoreResult (S : Covariance d) (O : Set (Space d)) : Prop where
  mass_pos : ∀ γ, 0 < gaussianLaw S γ O
  mass_lt_top : ∀ γ, gaussianLaw S γ O < (⊤ : ℝ≥0∞)
  probability : ∀ γ, IsProbabilityMeasure (conditionalLaw S O γ)
  moments : ∀ γ, MemLp id 2 (conditionalLaw S O γ)
  mean_mem : ∀ γ, conditionalMean S O γ ∈ O
  covariance_posDef : ∀ γ, (conditionalCov S O γ).PosDef
  smooth : ContDiff ℝ ∞ (conditionalMean S O)
  hasFDerivAt : ∀ γ, HasFDerivAt (conditionalMean S O) (jacobian S O γ) γ
  derivative_bijective : ∀ γ, Function.Bijective (jacobian S O γ)
  strong_bijection : ∃ f : StrongBijection O, f.toFun = conditionalMean S O

/-- The exact main analytic target. No cone conclusion or internal analytic input occurs here. -/
def CoreTheorem : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (S : Covariance d), S.PosDef →
    ∀ O : Set (Space d), O.Nonempty → IsOpen O → Convex ℝ O → CoreResult S O

def cone {r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) : Set (Space d) :=
  {x | ∀ i, 0 < (M *ᵥ x) i}

/-- The separate cone target, including the zero-row case. -/
def ConeTheorem : Prop :=
  ∀ (d r : ℕ), 1 ≤ d → r ≤ d →
    ∀ (M : Matrix (Fin r) (Fin d) ℝ), M.rank = r →
      ∀ (S : Covariance d), S.PosDef →
        (cone M).Nonempty ∧ IsOpen (cone M) ∧ Convex ℝ (cone M) ∧
          ∃ f : StrongBijection (cone M), f.toFun = conditionalMean S (cone M)

end MajorityDynamics.Analysis.ConditionalGaussian
