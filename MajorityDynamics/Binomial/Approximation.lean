import MajorityDynamics.Binomial.PointEstimate
import MajorityDynamics.Binomial.GaussianComparison
import MajorityDynamics.Binomial.TiltedExpansion

/-! # Completion of Appendix A.2

All three original uniform statements hold for the actual probability laws.
The only external mathematical input is the cited scalar binomial Chernoff bound.
-/

namespace MajorityDynamics.Binomial.Approximation

/-- The complete A.2 package: point estimates, polynomial Gaussian comparison,
and the different-trial tilted expansion. -/
theorem appendix_a2 : AppendixA2Theorem :=
  ⟨point_estimate, gaussian_comparison, tilted_expansion⟩

end MajorityDynamics.Binomial.Approximation
