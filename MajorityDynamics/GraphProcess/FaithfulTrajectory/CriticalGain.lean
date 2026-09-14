import MajorityDynamics.GraphProcess.FaithfulTrajectory.Lead
import MajorityDynamics.GraphProcess.LocalTransition.Basic

noncomputable section
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Universal

/-- The extra critical day's lower bound on every individual history block. -/
def CriticalGain {V : Type*} [Fintype V] {n : ℕ}
    (N : ℕ) (ζ : ℝ) (y : Local.CoarseData V n) : Prop :=
  ∀ s, ζ*(N:ℝ) ≤ character (Fin.last n) s*((y.sizes s:ℝ)-(N:ℝ)*ν n s)

theorem critical_gain_of_local_success {V : Type*} [Fintype V] {N n : ℕ}
    {p C ζ : ℝ} (hcard : Fintype.card V = N)
    (y : Local.CoarseData V n) (q : Local.Tilt n)
    (hgain : ∀ s b, ζ*(N:ℝ) ≤ sign b*(Local.templateSizes y.sizes q (append s b)-
      (N:ℝ)*ν (n+1) (append s b)))
    (herror : C*LocalTransition.sizeScale N ≤ (ζ/2)*(N:ℝ))
    (z : Local.CoarseData V (n+1)) (hz : LocalTransition.LocalSuccess y q p C z) :
    CriticalGain N (ζ/2) z := by
  intro u
  have he := hz.2.2.1 (parent u) (last u)
  rw [append_parent_last,hcard] at he
  have hg := hgain (parent u) (last u)
  rw [append_parent_last] at hg
  have he' := abs_le.mp (he.trans herror)
  change ζ/2*(N:ℝ) ≤ sign (last u)*((z.sizes u:ℝ)-(N:ℝ)*ν (n+1) u)
  cases hb : last u <;> simp only [hb,sign_false,sign_true,one_mul,neg_one_mul] at * <;>
    nlinarith [he'.1,he'.2]

theorem critical_gain_lead {N n : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N)
    (p : ℝ) (ζ : ℝ)
    (hg : CriticalGain N ζ (CoarseKernel.rho p (FineState.actualState G c n))) :
    (Fintype.card (Universal.History (n+1)):ℝ)*ζ*(N:ℝ) ≤
      Paper.lead (Paper.coloringOnDay G c (n+1)) := by
  rw [← signed_actual_partition G c]
  exact lead_of_critical_gains _ N ζ hg

end MajorityDynamics.GraphProcess.FaithfulTrajectory
