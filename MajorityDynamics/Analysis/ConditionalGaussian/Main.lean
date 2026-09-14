import MajorityDynamics.Analysis.ConditionalGaussian.Core
import MajorityDynamics.Analysis.ConditionalGaussian.Cones
import MajorityDynamics.Analysis.ConditionalGaussian.OpenConditioning

/-!
# Gaussian conditional means: completed analytic milestone

`core` proves A.5/D.2's concrete conditional-mean conclusion, and the cone
specialization follows here. These results do not import the paper's pending
expansion or pseudorandomness assumptions, and do not discharge those stages.
-/

namespace MajorityDynamics.Analysis.ConditionalGaussian

/-- The closed cone corollary, including zero rows. -/
theorem cone_bijection : ConeTheorem := cone_of_core core

/-- Both exact targets of the D-CM milestone, with no internal analytic hypotheses. -/
theorem main : CoreTheorem ∧ ConeTheorem := ⟨core, cone_bijection⟩

end MajorityDynamics.Analysis.ConditionalGaussian
