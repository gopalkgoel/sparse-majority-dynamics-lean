import MajorityDynamics.Literature.Goals.Brouwer.Statement
import MajorityDynamics.Literature.FixedPoint.Brouwer

/-! L05 — Brouwer fixed point on a closed ball.

Mathematical source: Hatcher, *Algebraic Topology* (2002), Corollary 2.15,
printed p. 114; see Statement.lean for the precise citation.

The checked general compact-convex theorem is ported from harfe's MIT-licensed
`fixed-point-theorems-lean4`, revision 770940ddf9878cf61952ed53d910b92bca841838:
https://github.com/harfe/fixed-point-theorems-lean4/blob/770940ddf9878cf61952ed53d910b92bca841838/FixedPointTheorems/brouwer.lean
The attributed source proof and license are in `Literature/FixedPoint/`.
The adapter below preserves continuity only on the ball and includes dimension zero.
-/

open Set Metric

namespace MajorityDynamics.Literature

/-- The original closed-ball contract, now proved from the attributed source proof. -/
theorem brouwer_closedBall : BrouwerClosedBall := by
  intro d c r hr h hcont hmaps
  let f : C(closedBall c r, closedBall c r) :=
    ⟨fun x => ⟨h x, hmaps x.property⟩,
      hcont.domRestrict.subtype_mk _⟩
  obtain ⟨x, hx⟩ := FixedPoint.brouwer_fixed_point (closedBall c r)
    (convex_closedBall c r) (isCompact_closedBall c r)
    ⟨c, mem_closedBall_self hr.le⟩ f
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

end MajorityDynamics.Literature
