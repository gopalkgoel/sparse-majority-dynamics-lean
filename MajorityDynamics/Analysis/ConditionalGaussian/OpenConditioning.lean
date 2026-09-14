import MajorityDynamics.Analysis.ConditionalGaussian.GaussianDensity
import MajorityDynamics.Analysis.ConditionalGaussian.Conditioning

/-!
# Conditioning an actual Gaussian on an open convex set

Source: `latest/main.tex`, Appendix A.5, `lem:open-conditioning`.
This specialization is closed: it assumes only the covariance and geometric
hypotheses from the paper, not a density formula or any analytic proof contract.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

/-- Normalization, second moments, support and absolute continuity of the
actual conditioned Gaussian, including arbitrary unbounded open sets. -/
theorem gaussian_conditional_regular (S : Covariance d) (hS : S.PosDef)
    (O : Set (Space d)) (hne : O.Nonempty) (hO : IsOpen O) (γ : Space d) :
    RegularOn (conditionalLaw S O γ) O :=
  regularOn_condition (gaussianLaw S γ) O (gaussianLaw_memLp_two S γ)
    (gaussianLaw_absolutelyContinuous S hS γ)
    (gaussianLaw_mass_pos S hS γ O hO hne) (gaussianLaw_mass_lt_top S γ O)

/-- The paper's open-conditioning lemma for Mathlib's multivariate Gaussian. -/
theorem open_conditioning (S : Covariance d) (hS : S.PosDef)
    (O : Set (Space d)) (hne : O.Nonempty) (hO : IsOpen O) (hconv : Convex ℝ O)
    (γ : Space d) :
    0 < gaussianLaw S γ O ∧ conditionalMean S O γ ∈ O ∧
      (conditionalCov S O γ).PosDef :=
  ⟨gaussianLaw_mass_pos S hS γ O hO hne,
    conditioning d (conditionalLaw S O γ) O hO hconv
      (gaussian_conditional_regular S hS O hne hO γ)⟩

end MajorityDynamics.Analysis.ConditionalGaussian
