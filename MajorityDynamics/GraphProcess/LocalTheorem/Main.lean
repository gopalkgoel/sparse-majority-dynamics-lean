import MajorityDynamics.GraphProcess.LocalTheorem.Real
import MajorityDynamics.GraphProcess.FiberTransference.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.LocalTheorem
universe u

/-- Full Proposition 3.9: the actual graphical fiber satisfies the original
R1/R2/R3 simultaneously, uniformly with vanishing failure and coefficient one. -/
theorem fiber_degree_array_estimates {θ T φ ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      (CoarseKernel.Lambda p y).real
        {σ | ¬ LocalTransition.FiberTypical y q p 1 σ} ≤ ε :=
  uniform_fiber_epsilon_of_transfer n hθlo hθhi hT hφ
    (FiberTransference.uniform_transfer n hθlo hθhi hT hφ) hε

/-- Full Theorem 3.3. Every internal statistical premise of the existing
mixture assembly is discharged by a proved original-input theorem. -/
theorem local_coarse_transition {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) :
    LocalCoarseTransitionTheorem.{u} θ T φ n :=
  local_coarse_transition_of_transfer n hθlo hθhi hT hφ hφ1
    (FiberTransference.uniform_transfer n hθlo hθhi hT hφ)

/-- Full Theorem 3.3 with literal real density in the manuscript's sparse window. -/
theorem local_coarse_transition_real {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) :
    LocalCoarseTransitionRealTheorem.{u} θ T φ n :=
  real_of_unit n hθlo hθhi hT (local_coarse_transition n hθlo hθhi hT hφ hφ1)

end MajorityDynamics.GraphProcess.LocalTheorem
