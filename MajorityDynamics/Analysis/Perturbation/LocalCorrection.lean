import MajorityDynamics.Analysis.Perturbation.Basic
import MajorityDynamics.Literature.Brouwer

/-!
# The local Brouwer correction argument

Source: `latest/main.tex`, Appendix D.3, `thm:perturbed-bijection`.
The inverse is evaluated only at points proved to lie in its target. The
approximation assumption is needed only on the prescribed radius-R ball.
Brouwer is an explicit input to this reduction, so the reduction itself has
no mathematical axioms beyond Lean's standard foundations.
-/

noncomputable section

open Set Metric

namespace MajorityDynamics.Analysis.Perturbation

/-- A local perturbation has a nearby solution, conditional on Brouwer.
Neither the target nor the region of inverse control needs to be convex. -/
theorem localPerturbation_of_brouwer
    (hb : MajorityDynamics.Literature.BrouwerClosedBall) :
    LocalPerturbationTheorem := by
  intro d B f V y r L R δ hVB hy _hr hL _hδ hnear hLip hR hδr hLδ g hg happrox
  let x₀ := f.invFun y
  let z : Space d → Space d := fun x => y + f.toFun x - g x
  let h : Space d → Space d := fun x => f.invFun (z x)
  have hxR (x : Space d) (hx : x ∈ closedBall x₀ 1) : ‖x‖ ≤ R :=
    (norm_le_norm_add_const_of_dist_le hx).trans hR
  have hzdist (x : Space d) (hx : x ∈ closedBall x₀ 1) : ‖z x - y‖ ≤ δ := by
    calc
      ‖z x - y‖ = ‖f.toFun x - g x‖ := by
        congr 1
        dsimp [z]
        abel
      _ = ‖g x - f.toFun x‖ := norm_sub_rev _ _
      _ ≤ δ := happrox x (hxR x hx)
  have hzV (x : Space d) (hx : x ∈ closedBall x₀ 1) : z x ∈ V :=
    hnear (z x) ((hzdist x hx).trans hδr.le)
  have hhbound (x : Space d) (hx : x ∈ closedBall x₀ 1) :
      ‖h x - x₀‖ ≤ L * δ :=
    (hLip (z x) (hzV x hx) y hy).trans
      (mul_le_mul_of_nonneg_left (hzdist x hx) hL)
  have hzcont : Continuous z := (continuous_const.add f.smooth.continuous).sub hg
  have hhcont : ContinuousOn h (closedBall x₀ 1) :=
    f.smooth_inv.continuousOn.comp hzcont.continuousOn (fun x hx => hVB (hzV x hx))
  have hhmap : MapsTo h (closedBall x₀ 1) (closedBall x₀ 1) := by
    intro x hx
    simpa only [mem_closedBall, dist_eq_norm] using (hhbound x hx).trans hLδ
  obtain ⟨x, hx, hfix⟩ := hb d x₀ 1 zero_lt_one h hhcont hhmap
  have hfx : f.toFun x = z x := by
    calc
      f.toFun x = f.toFun (h x) := congrArg f.toFun hfix.symm
      _ = z x := f.right_inv (z x) (hVB (hzV x hx))
  have hzero : y - g x = 0 := by
    calc
      y - g x = z x - f.toFun x := by dsimp [z]; abel
      _ = 0 := by rw [← hfx, sub_self]
  refine ⟨x, (sub_eq_zero.mp hzero).symm, ?_⟩
  simpa only [hfix] using hhbound x hx

end MajorityDynamics.Analysis.Perturbation
