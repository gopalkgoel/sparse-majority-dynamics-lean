import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# External input: Brouwer's fixed-point theorem

Source: Hatcher, *Algebraic Topology* (2002), Corollary 2.15, printed p. 114.
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf#page=123
The source states the theorem for the closed unit disk. Translation and positive
scaling give the equivalent closed-ball formulation below. This is an explicit
literature axiom under the project's chosen conditional-formalization scope;
the proof work is tracked in the adjacent Main.lean.

Used by `latest/main.tex`, `thm:perturbed-bijection`. The finite-dimensional
ambient space, continuity on the ball, and self-map condition are all explicit.
-/

open Set Metric

namespace MajorityDynamics.Literature

/-- Brouwer for a positive-radius closed ball in finite-dimensional Euclidean space. -/
def BrouwerClosedBall : Prop :=
  ∀ (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
    ∀ h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      ContinuousOn h (closedBall c r) →
      MapsTo h (closedBall c r) (closedBall c r) →
      ∃ x ∈ closedBall c r, h x = x


end MajorityDynamics.Literature
