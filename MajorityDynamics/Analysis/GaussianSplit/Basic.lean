import MajorityDynamics.Analysis.ConditionalGaussian.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian regression interface for the coherence argument

The original law here is a standard Gaussian. Conditioning on a measurable
event of a linear projection need not give a Gaussian law. The strictly positive
conditional covariance is a separate, proved input at applications.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace MajorityDynamics.Analysis.GaussianSplit

abbrev Space := ConditionalGaussian.Space

/-- Scalar linear observable of a Euclidean Gaussian. -/
def linear {d : ℕ} (a : Space d) : Space d → ℝ := fun x => ⟪a, x⟫

/-- The exact standard-Gaussian regression assertion needed in §4. -/
def StandardSplitTheorem : Prop :=
  ∀ (d : ℕ) (V : Submodule ℝ (Space d)) (A : Set (Space d)),
    MeasurableSet A →
    let E := V.starProjection ⁻¹' A
    let ρ := stdGaussian (Space d)
    ρ E ≠ 0 →
    (∀ v : Space d, v ≠ 0 → 0 < covarianceBilin (cond ρ E) v v) →
    ∀ (a z : Space d) (c : ℝ),
    (∀ v ∈ V, covarianceBilin (cond ρ E) a v = 0) →
    0 < covarianceBilin (cond ρ E) a z →
    0 < (∫ x, linear a x ∂cond ρ (E ∩ {x | 0 < c + linear z x})) -
      ∫ x, linear a x ∂cond ρ E

end MajorityDynamics.Analysis.GaussianSplit
