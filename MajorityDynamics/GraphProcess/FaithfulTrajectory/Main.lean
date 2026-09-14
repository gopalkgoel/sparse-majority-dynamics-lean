import MajorityDynamics.GraphProcess.FaithfulTrajectory.Full
import MajorityDynamics.Idealized.CriticalDay.Main

noncomputable section
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory

/-- The complete faithful trajectory, including the integer-case extra day.
Every analytic, initialization and current-state transition input is proved. -/
theorem faithful_trajectory {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ ζ : ℝ, 0 < ζ ∧
      FullPrefix θ T U δ ζ (⌈1/(1-θ)⌉₊-1) :=
  trajectory_of_critical Idealized.CriticalDay.critical_day hθlo hθhi hT

end MajorityDynamics.GraphProcess.FaithfulTrajectory
