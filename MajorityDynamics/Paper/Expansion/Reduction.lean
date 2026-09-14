import MajorityDynamics.Paper.Expansion.Assembly
import MajorityDynamics.GraphProcess.FaithfulTrajectory.Seed

noncomputable section
namespace MajorityDynamics.Paper.Expansion
open Idealized GraphProcess.FaithfulTrajectory

/-- Final expansion reduction. Every internal input except the literal 5.5
contract is supplied by proved endpoints in this module's imports. -/
theorem expansion_of_critical (hcritical : CriticalDay.CriticalDayTheorem.{0}) : ExpansionPhase := by
  intro θ T hθlo hθhi hT
  let k := ⌊1/(1-θ)⌋₊
  have hx : 1 < 1/(1-θ) := (lt_div_iff₀ (by linarith)).mpr (by linarith)
  have hk : 1 ≤ k := Nat.le_floor (by simpa using hx.le)
  by_cases heq : (k:ℝ) = 1/(1-θ)
  · let n := k-1
    have hnadd : n+1 = k := Nat.sub_add_cancel hk
    have hncrit' : (n:ℝ)+1 = 1/(1-θ) := by
      have h : ((n+1:ℕ):ℝ) = (k:ℝ) := congrArg (fun x:ℕ => (x:ℝ)) hnadd
      push_cast at h
      exact h.trans heq
    obtain ⟨U,hTU,δ,hδ,hprefix⟩ := faithful_prefix hθlo hθhi hT n (by linarith)
    obtain ⟨ζ,hζ,hgain⟩ := critical_from_uniform hcritical hθlo hθhi hT hTU hδ n hncrit' hprefix.last
    apply critical_expansion hθlo hθhi hT hζ (n := n+1) ?_ hgain
    change n+1+1 = k+1
    omega
  · have hkn : (k:ℝ) < 1/(1-θ) := by
      have hle : (k:ℝ) ≤ 1/(1-θ) := Nat.floor_le (by linarith)
      exact lt_of_le_of_ne hle heq
    obtain ⟨U,hTU,δ,hδ,hprefix⟩ := faithful_prefix hθlo hθhi hT k hkn
    exact noncritical_expansion hθlo hθhi hT hTU hδ rfl hprefix.last

end MajorityDynamics.Paper.Expansion
