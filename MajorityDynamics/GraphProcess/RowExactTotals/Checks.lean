import MajorityDynamics.GraphProcess.RowExactTotals.Main

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.totalExponent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.totalExponent_eq

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.absorb_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.absorb_constant

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.eventually_absorb_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.eventually_absorb_constant

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.product_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.product_power

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.rowCondition_eq_clt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.rowCondition_eq_clt

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.admissible_history_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.admissible_history_balance

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.admissible_clt_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.admissible_clt_geometry

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_block_local_clt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_block_local_clt

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_block_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_block_lower

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.fiber_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.fiber_prod

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.conditioned_blockCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.conditioned_blockCopies

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.blockCopies_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.blockCopies_sum

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.exactTotals_blockCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.exactTotals_blockCopies

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.exactTotals_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.exactTotals_factorization

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.exactTotals_real_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.exactTotals_real_factorization

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_exact_total_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_exact_total_lower_bound

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_exact_totals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_exact_totals

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_conditioned_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_conditioned_concentration

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_binomial_regularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_binomial_regularity

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal
universe u

/-- Expanded B.5 acceptance: original admissibility, actual measures, literal
ordered integer totals, prescribed explicit exponent and normalization. -/
example {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      let μ := cond (RowArray.law y.part q) (RowArray.history y.part)
      let E := {d : RowArray.Ambient y.part |
        History.edgeTotals y.part (RowArray.values d) = y.edge}
      IsProbabilityMeasure μ ∧
      ((N : ℝ)^2*p)^(-((2^(n+1)*(2^n+1) : ℕ) : ℝ)) ≤ μ.real E ∧
      0 < μ E ∧ IsProbabilityMeasure (cond μ E) ∧
      cond μ E = cond (RowArray.law y.part q) (RowArray.history y.part ∩ E) :=
  by
    obtain ⟨N₀, h⟩ := uniform_exact_totals n hθlo hθhi hT hφ
    refine ⟨N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    exact h N hN V hcard p hlo hhi y q ha.toCore

/-- Expanded B.6 acceptance: κ is the existing literal graph-process predicate. -/
example {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      let μ := cond (RowArray.law y.part q) (RowArray.history y.part)
      μ.real {d | ¬ CoarseKernel.Regular p y.part (RowArray.values d)} ≤ (N : ℝ)^(-A) ∧
      (cond μ {d | History.edgeTotals y.part (RowArray.values d) = y.edge}).real
        {d | ¬ CoarseKernel.Regular p y.part (RowArray.values d)} ≤ (N : ℝ)^(-A) :=
  by
    obtain ⟨N₀, h⟩ := uniform_binomial_regularity (A := A) n hθlo hθhi hT hφ
    refine ⟨N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    exact h N hN V hcard p hlo hhi y q ha.toCore

/-- Expanded concentration acceptance: all three original scales and actual
child template statistics survive exact-total conditioning. -/
example {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      (cond (cond (RowArray.law y.part q) (RowArray.history y.part))
        {d | History.edgeTotals y.part (RowArray.values d) = y.edge}).real
        {d | ¬ ((∀ v t, |(RowArray.values d v t : ℝ) - p*y.sizes t| ≤
            Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V))^(2/3 : ℝ)) ∧
          (∀ s b, |((RowArray.childSet d s b).card : ℝ) -
            Local.templateSizes y.sizes q (append s b)| ≤
              Real.sqrt (Fintype.card V)*Real.log (Fintype.card V)) ∧
          (∀ s t b, |(RowArray.childMass d s b t : ℝ) -
            Local.templateHalfEdges y.sizes q (append s b) t| ≤
              (Fintype.card V : ℝ)^2*p/Real.sqrt (Fintype.card V)*
                Real.log (Fintype.card V)))} ≤ (N : ℝ)^(-A) :=
  by
    obtain ⟨N₀, h⟩ := uniform_conditioned_concentration (A := A) n hθlo hθhi hT hφ
    refine ⟨N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    exact h N hN V hcard p hlo hhi y q ha.toCore

/-- First history level remains in the theorem range: no matrix constraints. -/
example : totalExponent 0 = 4 := by norm_num [totalExponent]

end MajorityDynamics.GraphProcess.RowExactTotals
