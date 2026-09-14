import MajorityDynamics.Idealized.Process.OneStep
import MajorityDynamics.Idealized.Process.Induction
import MajorityDynamics.Idealized.Process.RealDensity

/-! # Theorem 5.2: the complete idealized process -/

namespace MajorityDynamics.Idealized.Process

/-- The full finite-horizon theorem. Every analytic and combinatorial internal
obligation is supplied by a checked proof. -/
theorem idealized_process : IdealizedProcessTheorem :=
  idealized_process_of_step one_step

/-- The literal real-density version, with the uniform eventual conversion
to a success probability proved internally. -/
theorem idealized_process_real : IdealizedProcessRealTheorem :=
  idealized_process_real_of_probability idealized_process

end MajorityDynamics.Idealized.Process
