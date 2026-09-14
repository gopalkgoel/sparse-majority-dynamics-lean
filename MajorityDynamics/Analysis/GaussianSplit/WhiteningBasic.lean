import MajorityDynamics.Analysis.GaussianSplit.Basic

/-! # Affine Gaussian split interface for the universal response -/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace MajorityDynamics.Analysis.GaussianSplit

open ConditionalGaussian

def affineHistory {d m : ℕ} (h : Fin m → Space d) (c : Fin m → ℝ) : Set (Space d) :=
  {x | ∀ i, 0 < c i + linear (h i) x}

/-- The generic positive-split assertion, before specializing to the paper's histories.
This is a proposition defining a proof obligation, not an axiom. -/
def AffineSplitTheorem : Prop :=
  ∀ (d m : ℕ) (S : Covariance d), S.PosDef →
    ∀ (γ : Space d) (h : Fin m → Space d) (c : Fin m → ℝ)
      (a z : Space d) (q : ℝ),
      0 < gaussianLaw S γ (affineHistory h c) →
      0 < gaussianLaw S γ (affineHistory h c ∩ {x | 0 < q + linear z x}) →
      (∀ i, covarianceBilin (condition (gaussianLaw S γ) (affineHistory h c)) a (h i) = 0) →
      0 < covarianceBilin (condition (gaussianLaw S γ) (affineHistory h c)) a z →
      0 < (∫ x, linear a x
        ∂condition (gaussianLaw S γ) (affineHistory h c ∩ {x | 0 < q + linear z x})) -
        (∫ x, linear a x ∂condition (gaussianLaw S γ) (affineHistory h c))

end MajorityDynamics.Analysis.GaussianSplit
