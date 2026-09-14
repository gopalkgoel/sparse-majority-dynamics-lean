import MajorityDynamics.GraphProcess.LocalTheorem.Fiber
import MajorityDynamics.GraphProcess.FiberTransference.Main
import MajorityDynamics.GraphProcess.LocalTransition.TerminalSizes

/-! The actual-graph local theorem needed on the last expansion day.  It uses
history conditioning but permits either new child probability to vanish. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace MajorityDynamics.GraphProcess.LocalTheorem
universe u

/-- The full fiber estimate under core admissibility.  The proof is the same
exact-total transfer as Proposition 3.9; child nondegeneracy is not used. -/
theorem uniform_core_fiber_estimates_of_transfer {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ)
    (htransfer : FiberTransference.TransferTheorem.{u} θ T φ n) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.CoreAdmissible y q T φ p →
      IsProbabilityMeasure (CoarseKernel.Lambda p y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      (CoarseKernel.Lambda p y).real
        {σ | ¬ LocalTransition.FiberTypical y q p 1 σ} ≤ fiberError C N := by
  obtain ⟨C, hC, N₁, h₁⟩ := htransfer
  obtain ⟨N₂, h₂⟩ := RowExactTotals.uniform_conditioned_concentration (A := 1)
    n hθlo hθhi hT hφ
  obtain ⟨N₃, h₃⟩ := AdmissibleFiber.uniform_admissible_unit n hθlo hθhi hT
  refine ⟨C, hC, max N₁ (max N₂ N₃), ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  obtain ⟨_, _, hlaws⟩ := h₃ N (by omega) V hcard p hlo hhi y q φ ha
  let := hlaws.lambda_probability
  refine ⟨hlaws.lambda_probability, hlaws.kbar_probability,
    hlaws.lambda_support, ?_⟩
  have ht := h₁ N (by omega) V hcard p hlo hhi y q ha
    {d | RowConcentration.Good y p q d}
  have hr := h₂ N (by omega) V hcard p hlo hhi y q ha
  exact (typical_failure_le p y q hlaws.lambda_support).trans
    (ht.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hr hC.le)))

/-- Vanishing fiber failure, retaining the probability and support facts used
by the terminal Kbar assembly. -/
theorem uniform_core_fiber_epsilon {θ T φ ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.CoreAdmissible y q T φ p →
      IsProbabilityMeasure (CoarseKernel.Lambda p y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      (CoarseKernel.Lambda p y).real
        {σ | ¬ LocalTransition.FiberTypical y q p 1 σ} ≤ ε := by
  obtain ⟨C, _, N₁, h₁⟩ := uniform_core_fiber_estimates_of_transfer
    n hθlo hθhi hT hφ
    (FiberTransference.uniform_transfer n hθlo hθhi hT hφ)
  obtain ⟨N₂, h₂⟩ := eventually_atTop.mp
    ((fiberError_tendsto C).eventually (eventually_lt_nhds hε))
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have h := h₁ N (by omega) V hcard p hlo hhi y q ha
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (h₂ N (by omega)).le⟩

/-- Terminal analogue of the local coarse-transition theorem.  Its output has
the correct refined sizes with high probability but is not required to be a
new admissible state. -/
def TerminalSizeTransitionTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
    Local.CoreAdmissible y q T φ p →
    IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
    (CoarseKernel.Kbar p y).real
      {z | ¬ LocalTransition.TerminalSizeSuccess y q C z} ≤ ε ∧
    1-ε ≤ (CoarseKernel.Kbar p y).real
      {z | LocalTransition.TerminalSizeSuccess y q C z}

theorem terminal_size_transition {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    TerminalSizeTransitionTheorem.{u} θ T φ n := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro ε hε
  obtain ⟨N₀, h₀⟩ := uniform_core_fiber_epsilon n hθlo hθhi hT hφ hε
  obtain ⟨N₁, h₁⟩ := AdmissibleFiber.uniform_admissible_unit n hθlo hθhi hT
  refine ⟨max N₀ N₁, ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  obtain ⟨_, hKbar, _, htyp⟩ :=
    h₀ N (by omega) V hcard p hlo hhi y q ha
  obtain ⟨hpi, ⟨_, _, hG⟩, _⟩ :=
    h₁ N (by omega) V hcard p hlo hhi y q φ ha
  have hsize : (CoarseKernel.Lambda p y).real
      {σ | ¬ LocalTransition.SizeFiberGood y q 1 σ} ≤ ε := by
    apply (measureReal_mono ?_).trans htyp
    intro σ hbad hgood
    exact hbad (LocalTransition.sizeFiberGood_of_fiberGood y q p 1 σ hgood.2)
  have hfail := LocalTransition.terminal_size_failure p y q 1 ε
    hpi.1 hpi.2 hG.attainable hε.le hsize
  refine ⟨hKbar, hfail, ?_⟩
  have hc := probReal_compl_eq_one_sub (μ := CoarseKernel.Kbar p y)
    ((Set.toFinite {z | LocalTransition.TerminalSizeSuccess y q 1 z}).measurableSet)
  change (CoarseKernel.Kbar p y).real
      {z | ¬ LocalTransition.TerminalSizeSuccess y q 1 z} =
    1-(CoarseKernel.Kbar p y).real
      {z | LocalTransition.TerminalSizeSuccess y q 1 z} at hc
  linarith

end MajorityDynamics.GraphProcess.LocalTheorem
