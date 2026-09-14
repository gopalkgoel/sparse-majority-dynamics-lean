import MajorityDynamics.Idealized.Process.Basic
import MajorityDynamics.Idealized.RowLimits.RealExponent

/-! # The literal real-density quantifier in Theorem 5.2 -/

noncomputable section
open Filter
open scoped Topology

namespace MajorityDynamics.Idealized.Process

/-- The same complete theorem for every real `p` in the prescribed interval.
The interval is proved to lie in `(0,1)` before constructing the probability
parameter; no extra bound on `p` is assumed. -/
def IdealizedProcessRealTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ D : ℕ, 1 ≤ D →
  ∀ T : ℝ, 1 < T → ∃ ell : ℕ, 1 ≤ ell ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : ℝ,
    T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
    ∃ hp : 0 < p ∧ p < 1, ∃ a : Data,
      Specification N ⟨p, hp⟩ D ell a ∧
        ∀ b : Data, Recursion N ⟨p, hp⟩ D b → AgreeThrough D a b

theorem idealized_process_real_of_probability (h : IdealizedProcessTheorem) :
    IdealizedProcessRealTheorem := by
  intro θ hθlo hθhi D hD T hT
  obtain ⟨ell, hell, N₀, hN₀, hmain⟩ := h θ hθlo hθhi D hD T hT
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (RowLimits.eventually_real_density_probability θ T (by linarith) (by linarith))
  refine ⟨ell, hell, max N₀ N₁, hN₀.trans (le_max_left _ _), ?_⟩
  intro N hN p hp₀ hp₁
  have hp := hN₁ N ((le_max_right _ _).trans hN) p hp₀ hp₁
  exact ⟨hp, hmain N ((le_max_left _ _).trans hN) ⟨p, hp⟩ ⟨hp₀, hp₁⟩⟩

end MajorityDynamics.Idealized.Process
