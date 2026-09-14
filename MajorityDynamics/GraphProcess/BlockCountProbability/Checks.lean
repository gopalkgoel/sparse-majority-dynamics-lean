import MajorityDynamics.GraphProcess.BlockCountProbability.Main
import MajorityDynamics.GraphProcess.BlockCountProbability.FiniteChecks

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.BlockCountProbability.Checks
open Universal
universe u

example {V : Type*} [Fintype V] {n : ℕ} (y : Local.CoarseData V n) :
    GraphicalArray.fixedCountFamily y.part y.edge =
      {G : SimpleGraph V | History.edgeTotals y.part
        (History.degreeArray y.part G) = y.edge} := rfl

example {V : Type*} [Fintype V] {n : ℕ} (y : Local.CoarseData V n) (s : History (n+1)) :
    (((y.edge s s/2).toNat : ℕ) : ℝ) = (y.edge s s : ℝ)/2 :=
  half_toNat_real (y.edge_nonneg s s) (y.edge_even s)

example {V : Type*} [Fintype V] {n : ℕ} (p : unitInterval) (y : Local.CoarseData V n) :
    (SimpleGraph.binomialRandom V p).real
        {G : SimpleGraph V | History.edgeTotals y.part
          (History.degreeArray y.part G) = y.edge} =
      (∏ s, (ProbabilityTheory.binomial ((y.sizes s).choose 2) p).real
        {(y.edge s s/2).toNat}) *
      (∏ z : BlockDecomposition.Pair (History (n+1)),
        (ProbabilityTheory.binomial (y.sizes z.val.1*y.sizes z.val.2) p).real
          {(y.edge z.val.1 z.val.2).toNat}) := exact_factorization p y

example (n : ℕ) : factorCount n = 2^(n+1)+(2^(n+1)).choose 2 := rfl

example {θ T : ℝ} (n : ℕ) (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N)) →
      (∀ s, Real.exp (-C*N) ≤
        (ProbabilityTheory.binomial ((y.sizes s).choose 2) p).real
          {(y.edge s s/2).toNat}) ∧
      (∀ s t, s ≠ t → Real.exp (-C*N) ≤
        (ProbabilityTheory.binomial (y.sizes s*y.sizes t) p).real
          {(y.edge s t).toNat}) := uniform_component_lower n hθlo hθhi hT

example {θ T : ℝ} (n : ℕ) (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N)) →
      Real.exp (-C*N) ≤ (SimpleGraph.binomialRandom V p).real
        {G : SimpleGraph V | History.edgeTotals y.part
          (History.degreeArray y.part G) = y.edge} := count_event_lower n hθlo hθhi hT

end MajorityDynamics.GraphProcess.BlockCountProbability.Checks

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.loss_bound

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.error_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.error_identity

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.cross_real_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.cross_real_bounds

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.internal_real_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.internal_real_bounds

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.half_toNat_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.half_toNat_real

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.finite_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.finite_regime

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.uniform_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.uniform_regime

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.point_lower_of_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.point_lower_of_loss

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.binomial_lower_of_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.binomial_lower_of_loss

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.factorCount_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.factorCount_eq

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.product_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.product_lower

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.uniform_component_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.uniform_component_lower

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.count_event_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.count_event_lower
