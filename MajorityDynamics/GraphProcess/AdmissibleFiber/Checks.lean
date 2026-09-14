import MajorityDynamics.GraphProcess.AdmissibleFiber.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.GraphProcess.AdmissibleFiber.Checks
universe u

/-- Expanded same-witness and all-law consumer: no attainability, positive
conditioning, normalization, or intermediate existence assumption is present. -/
theorem original_input_consumers {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∃ hp : 0 < p ∧ p < 1,
      let pI : unitInterval := ⟨p, hp.1.le, hp.2.le⟩
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p →
      (∃ (d : RowArray.Ambient y.part) (G : SimpleGraph V),
        d ∈ GoodArrays.E0 y T p ∧ RowArray.totals d = y.edge ∧
        d ∈ RowArray.history y.part ∧ RowArray.Regular p d ∧
        RowArray.Gamma y.part y.edge 1 p d ∧
        (∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d) ∧
        History.degreeArray y.part G = RowArray.values d ∧
        RowArray.graphArray y.part G = d ∧ G ∈ CoarseKernel.E p y ∧
        CoarseKernel.actualCoarse p G (CoarseKernel.initial y) n = y ∧
        (∀ c : V → Bool, FineState.CompatibleInitial y.part c →
          CoarseKernel.actualCoarse p G c n = y) ∧
        RowArray.Gamma y.part y.edge 1 p (RowArray.graphArray y.part G) ∧
        (∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p (RowArray.graphArray y.part G))) ∧
      CoarseKernel.pAttainable p y ∧
      0 < SimpleGraph.binomialRandom V pI (CoarseKernel.E p y) ∧
      IsProbabilityMeasure (cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.E p y)) ∧
      cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.E p y) = uniformOn (CoarseKernel.E p y) ∧
      IsProbabilityMeasure (CoarseKernel.Lambda pI y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar pI y) ∧
      CoarseKernel.Lambda pI y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      CoarseKernel.Lambda pI y {σ | CoarseKernel.Regular p σ.part σ.deg} = 1 ∧
      0 < GraphicalArray.law y.part y.edge
        (RowArray.history y.part ∩ {d | RowArray.Regular p d}) ∧
      IsProbabilityMeasure (cond (GraphicalArray.law y.part y.edge)
        (RowArray.history y.part ∩ {d | RowArray.Regular p d})) ∧
      (∀ c : V → Bool,
        (0 < SimpleGraph.binomialRandom V pI (CoarseKernel.currentEvent p c y) ↔
          FineState.CompatibleInitial y.part c) ∧
        (¬ FineState.CompatibleInitial y.part c →
          CoarseKernel.currentEvent p c y = ∅ ∧
          cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.currentEvent p c y) = 0) ∧
        (FineState.CompatibleInitial y.part c →
          CoarseKernel.currentEvent p c y = CoarseKernel.E p y ∧
          IsProbabilityMeasure
            (cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.currentEvent p c y)) ∧
          (cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.currentEvent p c y)).map
            (fun G => FineState.actualState G c n) = CoarseKernel.Lambda pI y ∧
          (cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.currentEvent p c y)).map
            (fun G => CoarseKernel.rho p (FineState.actualState G c (n+1))) = CoarseKernel.Kbar pI y ∧
          ∀ B : Set (Local.CoarseData V (n+1)),
            cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.currentEvent p c y)
              {G | CoarseKernel.rho p (FineState.actualState G c (n+1)) ∈ B} =
              CoarseKernel.Kbar pI y B)) ∧
      (cond (SimpleGraph.binomialRandom V pI) (CoarseKernel.E p y)).map
        (RowArray.graphArray y.part) =
        cond (GraphicalArray.law y.part y.edge)
          (RowArray.history y.part ∩ {d | RowArray.Regular p d}) ∧
      (∀ B : Set (RowArray.Ambient y.part),
        CoarseKernel.Lambda pI y {σ | σ.deg ∈ RowArray.values '' B} =
          cond (GraphicalArray.law y.part y.edge)
            (RowArray.history y.part ∩ {d | RowArray.Regular p d}) B) := by
  obtain ⟨N₀, h₀⟩ := uniform_admissible n hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi
  obtain ⟨hp, hall⟩ := h₀ N hN V hcard p hlo hhi
  refine ⟨hp, ?_⟩
  dsimp only
  intro y q φ ha
  obtain ⟨⟨d, G, hg⟩, h⟩ := hall y q φ ha.toCore
  refine ⟨⟨d, G, hg.good, hg.totals, hg.history, hg.regular, hg.gamma_one, hg.gamma,
    hg.degrees, hg.array_eq, hg.coarse_event, hg.actual, hg.compatible_actual,
    hg.graph_gamma_one, hg.graph_gamma⟩, hg.attainable,
    h.graph_pos, h.graph_probability, h.graph_uniform,
    h.lambda_probability, h.kbar_probability, h.lambda_support, h.lambda_regularity,
    h.graphical_pos, h.graphical_probability, ?_, h.graph_array_law, h.proposition_3_7⟩
  intro c
  exact ⟨h.current_positive_iff c,
    fun hc => ⟨h.incompatible_empty c hc, h.incompatible_cond_zero c hc⟩,
    fun hc => ⟨h.current_event c hc, h.current_probability c hc,
      h.fine_law c hc, h.coarse_law c hc, h.transition c hc⟩⟩

/-- k=1 is n=0: no earlier-history test is added accidentally. -/
example {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V 0) (q : Local.Tilt 0) (φ : ℝ),
      Local.Admissible y q T φ p →
      (0 < (p : ℝ) ∧ (p : ℝ) < 1) ∧
      (∃ (d : RowArray.Ambient y.part) (G : SimpleGraph V), Realizes y T p d G) ∧
        ActualLaws p y := by
  obtain ⟨N₀, h⟩ := uniform_admissible_unit 0 hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q φ ha
  exact h N hN V hcard p hlo hhi y q φ ha.toCore

end MajorityDynamics.GraphProcess.AdmissibleFiber.Checks

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.graph_mem_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.graph_mem_E

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.realizes_of_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.realizes_of_array

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_realization

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.currentEvent_empty_of_incompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.currentEvent_empty_of_incompatible

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.current_cond_zero_of_incompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.current_cond_zero_of_incompatible

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.current_positive_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.current_positive_iff

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.actual_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.actual_laws

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_realization_and_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_realization_and_laws

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_admissible

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_admissible_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.uniform_admissible_unit

/-- info: 'MajorityDynamics.GraphProcess.AdmissibleFiber.Checks.original_input_consumers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AdmissibleFiber.Checks.original_input_consumers
