import MajorityDynamics.GraphProcess.LocalTheorem.Basic
import MajorityDynamics.GraphProcess.FiberTransference.Basic

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace MajorityDynamics.GraphProcess.LocalTheorem
universe u

/-- Integration of the proved exact-total concentration with an event-wise
transfer theorem. The closed paper endpoint supplies that theorem, below. -/
theorem uniform_fiber_estimates_of_transfer {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ)
    (htransfer : FiberTransference.TransferTheorem.{u} θ T φ n) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      IsProbabilityMeasure (CoarseKernel.Lambda p y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      (CoarseKernel.Lambda p y).real
        {σ | ¬ LocalTransition.FiberTypical y q p 1 σ} ≤ fiberError C N := by
  obtain ⟨C,hC,N₁,h₁⟩ := htransfer
  obtain ⟨N₂,h₂⟩ := RowExactTotals.uniform_conditioned_concentration (A := 1)
    n hθlo hθhi hT hφ
  obtain ⟨N₃,h₃⟩ := AdmissibleFiber.uniform_admissible_unit n hθlo hθhi hT
  refine ⟨C,hC,max N₁ (max N₂ N₃),?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  obtain ⟨_,_,hlaws⟩ := h₃ N (by omega) V hcard p hlo hhi y q φ ha.toCore
  have := hlaws.lambda_probability
  refine ⟨hlaws.lambda_probability,hlaws.kbar_probability,hlaws.lambda_support,?_⟩
  have ht := h₁ N (by omega) V hcard p hlo hhi y q ha.toCore
    {d | RowConcentration.Good y p q d}
  have hr := h₂ N (by omega) V hcard p hlo hhi y q ha.toCore
  exact (typical_failure_le p y q hlaws.lambda_support).trans
    (ht.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hr hC.le)))

/-- Uniform vanishing fiber failure; the R1/R2/R3 tolerances keep coefficient one. -/
theorem uniform_fiber_epsilon_of_transfer {θ T φ ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ)
    (htransfer : FiberTransference.TransferTheorem.{u} θ T φ n) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      (CoarseKernel.Lambda p y).real
        {σ | ¬ LocalTransition.FiberTypical y q p 1 σ} ≤ ε := by
  obtain ⟨C,_,N₁,h₁⟩ := uniform_fiber_estimates_of_transfer n hθlo hθhi hT hφ htransfer
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp
    ((fiberError_tendsto C).eventually (eventually_lt_nhds hε))
  refine ⟨max N₁ N₂,?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  exact (h₁ N (by omega) V hcard p hlo hhi y q ha).2.2.2 |>.trans (h₂ N (by omega)).le

end MajorityDynamics.GraphProcess.LocalTheorem
