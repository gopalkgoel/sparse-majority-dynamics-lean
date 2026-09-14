import MajorityDynamics.Analysis.Perturbation.Basic
import MajorityDynamics.Analysis.ConditionalGaussian.Cones

/-!
# The compact cone targets in Appendix D.3

Source: `thm:perturbed-bijection`, final assertion. Coordinate bounds represent
the paper's infinity norm, not the smaller Euclidean ball. The row-margin
condition is vacuous for zero rows, giving precisely the closed cube.
These compact sets need not be nonempty, even when M has full row rank.
-/

noncomputable section

open Set
open scoped Matrix

namespace MajorityDynamics.Analysis.Perturbation

variable {d r : ℕ}

/-- The paper's K_T, with the minimum row-margin written as universal inequalities. -/
def compactCone (M : Matrix (Fin r) (Fin d) ℝ) (T : ℝ) : Set (Space d) :=
  {y | (∀ j, |y j| ≤ T) ∧ ∀ i, T⁻¹ ≤ (M *ᵥ y) i}

/-- D.3 specialized to the exact compact cone sets, including zero rows. -/
def ConePerturbationTheorem : Prop :=
  ∀ (d r : ℕ), 1 ≤ d → r ≤ d →
    ∀ (M : Matrix (Fin r) (Fin d) ℝ), M.rank = r →
      ∀ f : StrongBijection (ConditionalGaussian.cone M),
        ∀ T : ℝ, 1 < T → ∀ C₀ : ℝ, 0 < C₀ →
          PerturbationAt f (compactCone M T) C₀

/-- The cone perturbation statement for the concrete conditional-mean map from D.2. -/
def GaussianConePerturbationTheorem : Prop :=
  ∀ (d r : ℕ), 1 ≤ d → r ≤ d →
    ∀ (M : Matrix (Fin r) (Fin d) ℝ), M.rank = r →
      ∀ (S : ConditionalGaussian.Covariance d), S.PosDef →
        ∀ T : ℝ, 1 < T → ∀ C₀ : ℝ, 0 < C₀ →
          ∃ f : StrongBijection (ConditionalGaussian.cone M),
            f.toFun = ConditionalGaussian.conditionalMean S (ConditionalGaussian.cone M) ∧
              PerturbationAt f (compactCone M T) C₀

end MajorityDynamics.Analysis.Perturbation
