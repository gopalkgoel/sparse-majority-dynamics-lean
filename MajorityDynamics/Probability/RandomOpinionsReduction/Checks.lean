import MajorityDynamics.Probability.RandomOpinionsReduction.Main

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace MajorityDynamics.Probability.RandomOpinionsReduction

-- Independently spelled input: both natural floors, all uniform parameters,
-- the actual binomial graph law and the original all-plus conclusion.
example : Paper.MainTheorem =
    (∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p : unitInterval) (τ : ℝ) (c : Fin N → Bool),
        (T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) ∧ (p : ℝ) < T*(N : ℝ)^(-θ)) →
        T⁻¹ ≤ τ → τ ≤ T →
        (Finset.univ.filter (fun v => c v = false)).card = N/2 + ⌊τ*Real.sqrt N⌋₊ →
        SimpleGraph.binomialRandom (Fin N) p
          {G | ∀ v, Paper.coloringOnDay G c (Paper.convergenceDay θ) v = false}ᶜ ≤
            ENNReal.ofReal ε) := by
  classical
  rfl

example : Paper.MainTheorem → RandomOpinionsTheorem := random_opinions_of_main
example : Paper.MainTheorem → RandomOpinionsRealTheorem := random_opinions_real_of_main
example : Paper.MainTheorem → RandomOpinionsFiniteTheorem := random_opinions_finite_of_main
example : Paper.MainTheorem → RandomOpinionsFiniteRealTheorem := random_opinions_finite_real_of_main

theorem convergenceDay_formula (θ : ℝ) :
    Paper.convergenceDay θ = 2 * ⌊1/(1-θ)⌋₊ + 3 := by
  unfold Paper.convergenceDay Paper.expansionDay
  omega

-- Expanded output: the product order is (coloring, graph), with an actual
-- product of fair bits, and a single sign valid for every later time.
example (hmain : Paper.MainTheorem) :
    ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : unitInterval,
        (T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) ∧ (p : ℝ) < T*(N : ℝ)^(-θ)) →
        ((Measure.pi (fun _ : Fin N => fairBitLaw)).prod
          (SimpleGraph.binomialRandom (Fin N) p))
          {z | ∃ b : Bool, ∀ t : ℕ, 2*⌊1/(1-θ)⌋₊+3 ≤ t →
            ∀ v, Paper.coloringOnDay z.2 z.1 t v = b}ᶜ ≤ ENNReal.ofReal ε := by
  simpa only [RandomOpinionsTheorem, jointLaw, uniformColoringLaw, Paper.graphLaw,
    Paper.densityRange, consensusEvent, convergenceDay_formula] using random_opinions_of_main hmain

example (hmain : Paper.MainTheorem) :
    ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Type) [Fintype V], Fintype.card V = N →
        ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
          ∃ hp : 0 < p ∧ p < 1,
            ((Measure.pi (fun _ : V => fairBitLaw)).prod
              (SimpleGraph.binomialRandom V ⟨p, hp.1.le, hp.2.le⟩))
              {z | ∃ b : Bool, ∀ t : ℕ, 2*⌊1/(1-θ)⌋₊+3 ≤ t →
                ∀ v, (nextColoringV z.2)^[t-1] z.1 v = b}ᶜ ≤ ENNReal.ofReal ε := by
  simpa only [RandomOpinionsFiniteRealTheorem, jointLawV, uniformColoringLawV,
    consensusEventV, coloringOnDayV, convergenceDay_formula] using random_opinions_finite_real_of_main hmain

example (N : ℕ) : IsProbabilityMeasure (uniformColoringLaw N) := inferInstance
example (N : ℕ) (p : unitInterval) : IsProbabilityMeasure (jointLaw N p) := inferInstance
example (b : Bool) : fairBitLaw {b} = 1/2 := fairBitLaw_singleton b

example {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W) (p : unitInterval) :
    (SimpleGraph.binomialRandom V p).map e.simpleGraph = SimpleGraph.binomialRandom W p :=
  graph_law_transport e p

example {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W)
    (G : SimpleGraph V) (c : V → Bool) (t : ℕ) :
    coloringOnDayV (e.simpleGraph G) (coloringEquiv e c) t =
      coloringEquiv e (coloringOnDayV G c t) := coloringOnDay_transport e G c t

example {N : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N) (t : ℕ) :
    coloringOnDayV G c t = Paper.coloringOnDay G c t := coloringOnDay_fin G c t

example (ε : ℝ) (hε : 0 < ε) : ∃ A : ℝ, 1 < A ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → uniformColoringLaw N
      {c | A⁻¹*Real.sqrt N ≤ |(Paper.plusCount c : ℝ)-(N : ℝ)/2| ∧
        |(Paper.plusCount c : ℝ)-(N : ℝ)/2| ≤ A*Real.sqrt N}ᶜ ≤ ENNReal.ofReal ε :=
  random_bias_window ε hε

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.random_opinions_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms random_opinions_of_main

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.random_opinions_real_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms random_opinions_real_of_main

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.random_opinions_finite_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms random_opinions_finite_of_main

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.random_opinions_finite_real_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms random_opinions_finite_real_of_main

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.random_bias_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms random_bias_window

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.small_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms small_ball

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.upper_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_tail

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.central_binomial_sq_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms central_binomial_sq_bound

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.binomial_point_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_point_bound

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.exact_majority_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_majority_bias

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.densityRange_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms densityRange_mono

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.nextColoring_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextColoring_flip

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloringOnDay_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloringOnDay_flip

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.flip_success_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flip_success_probability

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.nextColoring_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextColoring_constant

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.consensus_persistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms consensus_persistence

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloring_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloring_uniform

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.plusCount_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms plusCount_probability

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloring_coordinates_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloring_coordinates_independent

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloring_coordinate_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloring_coordinate_law

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.graph_coloring_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_coloring_independent

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.average_failure_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms average_failure_bound

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.graph_law_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_law_transport

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloring_law_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloring_law_transport

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.joint_law_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_law_transport

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.nextColoring_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextColoring_transport

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloringOnDay_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloringOnDay_transport

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloringV_coordinates_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloringV_coordinates_independent

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.coloringV_coordinate_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coloringV_coordinate_law

/-- info: 'MajorityDynamics.Probability.RandomOpinionsReduction.graph_coloringV_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_coloringV_independent

end MajorityDynamics.Probability.RandomOpinionsReduction
