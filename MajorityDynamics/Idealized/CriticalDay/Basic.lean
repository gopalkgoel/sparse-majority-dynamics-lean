import MajorityDynamics.Idealized.PerturbedEvolution.Basic
import MajorityDynamics.Idealized.RowLimits.Basic

/-! The complete original-input edge-day contract (Theorem 5.5 / E.6).
Level `n` is paper day `n+1`. The macroscopic gain is chosen before the
faithfulness exponent, exactly expressing its independence of that exponent. -/
noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt PerturbedEvolution

structure Conclusion {V : Type*} [Fintype V] {n : ℕ}
    (N : ℕ) (p : Binomial.Probability) (y : Local.CoarseData V n)
    (T₁ δ₁ φ₁ ζ : ℝ) : Prop where
  exists_unique : ∃! q : Local.Tilt n, Local.Solves y.sizes y.realEdges q
  admissible : ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
    Local.Admissible y q T₁ φ₁ (p : ℝ)
  approximation : ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
    ∀ s t, |(q s t : ℝ) - logitTilt N p (γ n s t) (ν n t)| ≤
      (p : ℝ) / Real.sqrt ((p : ℝ) * N) * (N : ℝ) ^ (-δ₁)
  gain : ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
    ∀ s b, sign b * (Local.templateSizes y.sizes q (append s b) -
      (N : ℝ) * ν (n + 1) (append s b)) ≥ ζ * N

def CriticalDayTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
  ∀ n : ℕ, (n : ℝ) + 1 = 1 / (1 - θ) →
  ∀ T : ℝ, 1 < T → ∃ ζ : ℝ, 0 < ζ ∧
  ∀ δ : ℝ, 0 < δ →
  ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧
  ∃ φ₁ : ℝ, 0 < φ₁ ∧ φ₁ < 1 / 2 ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
  ∃ hp : 0 < p ∧ p < 1,
    Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
      (referenceDataReal θ T N p) ∧
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ (V : Type*) [Fintype V], Fintype.card V = N →
    ∀ y : Local.CoarseData V n,
      Faithful N p T δ τ (referenceDataReal θ T N p) y →
      Conclusion N ⟨p, hp⟩ y T₁ δ₁ φ₁ ζ

end MajorityDynamics.Idealized.CriticalDay
