import MajorityDynamics.GraphProcess.FaithfulTrajectory.CriticalGain
import MajorityDynamics.GraphProcess.LocalTransition.TerminalSizes

/-! The critical lead calculation uses only child sizes, so it also consumes
the terminal size-only transition. -/
noncomputable section
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Universal

theorem critical_gain_of_terminal_size_success
    {V : Type*} [Fintype V] {N n : ℕ} {C ζ : ℝ}
    (hcard : Fintype.card V = N)
    (y : Local.CoarseData V n) (q : Local.Tilt n)
    (hgain : ∀ s b, ζ*(N:ℝ) ≤ sign b *
      (Local.templateSizes y.sizes q (append s b) -
        (N:ℝ)*ν (n+1) (append s b)))
    (herror : C*LocalTransition.sizeScale N ≤ (ζ/2)*(N:ℝ))
    (z : Local.CoarseData V (n+1))
    (hz : LocalTransition.TerminalSizeSuccess y q C z) :
    CriticalGain N (ζ/2) z := by
  intro u
  have he := hz.2 (parent u) (last u)
  rw [append_parent_last, hcard] at he
  have hg := hgain (parent u) (last u)
  rw [append_parent_last] at hg
  have he' := abs_le.mp (he.trans herror)
  change ζ/2*(N:ℝ) ≤ sign (last u) *
    ((z.sizes u:ℝ)-(N:ℝ)*ν (n+1) u)
  cases hb : last u <;>
    simp only [hb, sign_false, sign_true, one_mul, neg_one_mul] at * <;>
    nlinarith [he'.1, he'.2]

end MajorityDynamics.GraphProcess.FaithfulTrajectory
