import MajorityDynamics.Paper.Expansion.Reduction
import MajorityDynamics.Idealized.CriticalDay.Main

noncomputable section
namespace MajorityDynamics.Paper.Expansion

/-- Corollary 5.9, with every original internal mathematical obligation
supplied. The uniform graph law, initial count and day are unchanged. -/
theorem expansion : ExpansionPhase :=
  expansion_of_critical Idealized.CriticalDay.critical_day

end MajorityDynamics.Paper.Expansion
