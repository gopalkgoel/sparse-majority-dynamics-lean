import MajorityDynamics.Idealized.CriticalDay.RowInputs

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

/-- Original faithful sizes approach the universal proportions at a uniform
positive polynomial rate on the critical day. -/
theorem relative_sizes (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∀ᶠ N : ℕ in atTop,
    ∀ p : Binomial.Probability, Density θ T N p →
    ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
    FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
    ∀ s, |(naturalSizes η s : ℝ) - N * ν n s| ≤
      (N : ℝ) ^ (-responseRate θ 0) * N := by
  obtain ⟨U, C, _, _, hinput⟩ := faithful_row_inputs θ T δ hθlo hθhi hT hδ n ell hk
  filter_upwards [hinput,
    eventually_small θ T hθlo hθhi hT 0 (ell + 1) (first_day_subcritical hθlo hθhi)]
    with N hi hs
  intro p hp a ha τ hτ hτT η e hf s
  have hclose := ((hi p hp a ha τ hτ hτT η e hf).2 s).close s
  have hsmall := mul_le_mul_of_nonneg_left ((hs p hp).2.2.1) (Nat.cast_nonneg N)
  have hsmall' : N / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ (ell + 1) ≤
      (N : ℝ) ^ (-responseRate θ 0) * N := by
    convert hsmall using 1 <;> first | ring | rfl
  exact hclose.trans hsmall'

end MajorityDynamics.Idealized.CriticalDay
