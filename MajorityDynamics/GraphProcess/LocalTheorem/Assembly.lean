import MajorityDynamics.GraphProcess.LocalTheorem.Fiber
import MajorityDynamics.GraphProcess.KernelSplitting.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.LocalTheorem
universe u

/-- The original local coarse-transition theorem, in uniform epsilon form.
The single error constant precedes epsilon, the size threshold, and every
varying carrier, density, coarse state and tilt. -/
def LocalCoarseTransitionTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
    IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
    (CoarseKernel.Kbar p y).real {z | ¬ LocalTransition.LocalSuccess y q p C z} ≤ ε ∧
    1-ε ≤ (CoarseKernel.Kbar p y).real {z | LocalTransition.LocalSuccess y q p C z}

/-- Assembly from the full event-wise transfer theorem; the closed Main
supplies this sole intermediate premise by its proved implementation. -/
theorem local_coarse_transition_of_transfer {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2)
    (htransfer : FiberTransference.TransferTheorem.{u} θ T φ n) :
    LocalCoarseTransitionTheorem.{u} θ T φ n := by
  refine ⟨1+2*T,by linarith,?_⟩
  intro ε hε
  have he : 0 < ε/2 := by positivity
  obtain ⟨N₁,h₁⟩ := uniform_fiber_epsilon_of_transfer n hθlo hθhi hT hφ htransfer he
  obtain ⟨N₂,h₂⟩ := KernelSplitting.typical_kernel_splitting_epsilon (Cf := 1)
    n hθlo hθhi hT hφ hφ1 zero_le_one he
  obtain ⟨N₃,h₃⟩ := LocalTransition.uniform_typical_failure n hθlo hθhi hT
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hf := h₁ N (by omega) V hcard p hlo hhi y q ha
  have hs := h₂ N (by omega) V hcard p hlo hhi y q ha
  have h := h₃ N (by omega) V hcard p hlo hhi y q φ ha
    1 (2*T) (ε/2) (ε/2) zero_le_one (by linarith) he.le he.le hf hs
  have := h.2.1
  have hb : (CoarseKernel.Kbar p y).real
      {z | ¬ LocalTransition.LocalSuccess y q p (1+2*T) z} ≤ ε := by
    linarith [h.2.2.2]
  refine ⟨h.2.1,hb,?_⟩
  have hc := probReal_compl_eq_one_sub (μ := CoarseKernel.Kbar p y)
    ((Set.toFinite {z | LocalTransition.LocalSuccess y q p (1+2*T) z}).measurableSet)
  change (CoarseKernel.Kbar p y).real
    {z | ¬ LocalTransition.LocalSuccess y q p (1+2*T) z} =
    1-(CoarseKernel.Kbar p y).real {z | LocalTransition.LocalSuccess y q p (1+2*T) z} at hc
  linarith

end MajorityDynamics.GraphProcess.LocalTheorem
