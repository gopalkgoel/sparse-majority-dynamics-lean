import MajorityDynamics.GraphProcess.AutomaticGraphicality.Main

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.AutomaticGraphicality.Checks
universe u
open AutomaticGraphicality

example {V : Type*} [Fintype V] {n : ℕ} (y : Local.CoarseData V n)
    (d : RowArray.Ambient y.part) {T p : ℝ}
    (hN : 0 < (Fintype.card V : ℝ)) (hT : 1 < T) (hp : 0 < p)
    (hx : 1 ≤ p * Fintype.card V) (hxT : 4 * T ^ 6 ≤ p * Fintype.card V)
    (hpSmall : p ≤ 1 / (12 * T ^ 2))
    (hsizes : ∀ s, (Fintype.card V : ℝ) / T ≤ (Local.partSizes y.part s : ℝ))
    (hcounts : ∀ s t,
      |(y.edge s t : ℝ) - p * (Local.partSizes y.part s : ℝ) * (Local.partSizes y.part t : ℝ)| ≤
      T * (Fintype.card V : ℝ) ^ 2 * p / Real.sqrt (p * Fintype.card V))
    (htot : History.edgeTotals y.part (RowArray.values d) = y.edge)
    (hreg : ∀ v t, |(RowArray.values d v t : ℝ) - p * (Local.partSizes y.part t : ℝ)| ≤
      (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ)) :
    ∃ G : SimpleGraph V, History.degreeArray y.part G = RowArray.values d :=
  finite_graphicality y d hN hT hp hx hxT hpSmall hsizes hcounts htot hreg

-- Exact paper input/output check, with both κ and ordered totals expanded.
example {θ T : ℝ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ (n : ℕ) (p : ℝ),
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ) / T ≤ (Local.partSizes y.part s : ℝ)) →
      (∀ s t,
        |(y.edge s t : ℝ) - p * (Local.partSizes y.part s : ℝ) * (Local.partSizes y.part t : ℝ)| ≤
        T * (N : ℝ) ^ 2 * p / Real.sqrt (p * N)) →
      History.edgeTotals y.part (RowArray.values d) = y.edge →
      (∀ v t, |(RowArray.values d v t : ℝ) - p * (Local.partSizes y.part t : ℝ)| ≤
        (p * N) ^ (4 / 7 : ℝ)) →
      ∃ G : SimpleGraph V, History.degreeArray y.part G = RowArray.values d := by
  obtain ⟨N₀, hN₀⟩ := automatic_graphicality_exists.{u} hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard n p hpLo hpHi y d hsizes hcounts htot hreg
  apply hN₀ N hN V hcard n p hpLo hpHi y d hsizes hcounts htot
  simpa only [RowArray.Regular, CoarseKernel.Regular, hcard] using hreg

end MajorityDynamics.GraphProcess.AutomaticGraphicality.Checks

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.block_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.block_sum

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.block_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.block_sum_eq

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.block_sum_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.block_sum_even

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.opposite_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.opposite_sums

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.degree_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.degree_upper

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.count_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.count_lower

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.internal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.internal_bound

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.cross_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.cross_bound

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.eventually_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.eventually_regime

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.graphical_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.graphical_of_bound

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.cross_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.cross_of_bound

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.graphical_of_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.graphical_of_uniform_bound

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.finite_graphicality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.finite_graphicality

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.automatic_graphicality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.automatic_graphicality

/-- info: 'MajorityDynamics.GraphProcess.AutomaticGraphicality.automatic_graphicality_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.AutomaticGraphicality.automatic_graphicality_exists
