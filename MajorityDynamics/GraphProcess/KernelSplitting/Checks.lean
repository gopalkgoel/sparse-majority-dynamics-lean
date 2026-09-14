import MajorityDynamics.GraphProcess.KernelSplitting.Main

/-! Literal original input/output contracts and exact axiom boundaries. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting.Checks
open Universal KernelInputs
universe u

/-- Expanded original R1/R2 inputs and literal manuscript output. -/
theorem original_S2 {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y →
      (∀ v t, |(σ.deg v t : ℝ)-p*y.sizes t| ≤
        Real.sqrt (p*N)*Real.log N^((2:ℝ)/3)) →
      (∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ)-
        Local.templateSizes y.sizes q (append s b)| ≤
        Cf*(Real.sqrt (N : ℝ)*Real.log N)) →
      (FineKernel.K σ).real {τ | ¬ (∀ v t, |(τ.deg v t : ℝ)-p*(Local.partSizes τ.part t : ℝ)| ≤
          (p*N)^((4:ℝ)/7))} ≤ (N:ℝ)^(-A) := by
  obtain ⟨N₀,h₀⟩ := uniform_regularity_failure.{u} n hθlo hθhi hT hφ hφ1 hCf hA
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have h1 : DegreeTypical y p σ := by simpa only [DegreeTypical,hcard] using hR1
  have h2 : SizeTypical y q Cf σ := by
    simpa only [SizeTypical,child,LocalTransition.sizeScale,hcard] using hR2
  simpa only [LocalTransition.KernelGood,CoarseKernel.Regular,LocalTransition.edgeScale,
    KernelEdgeSplitting.unionError,hcard] using
      h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2

/-- Expanded original R1/R2 inputs and literal manuscript output. -/
theorem original_kernel_splitting {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y →
      (∀ v t, |(σ.deg v t : ℝ)-p*y.sizes t| ≤
        Real.sqrt (p*N)*Real.log N^((2:ℝ)/3)) →
      (∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ)-
        Local.templateSizes y.sizes q (append s b)| ≤
        Cf*(Real.sqrt (N : ℝ)*Real.log N)) →
      (FineKernel.K σ).real {τ | ¬ (τ.part = FineState.refinement σ ∧
        (∀ v t, |(τ.deg v t : ℝ)-p*(Local.partSizes τ.part t : ℝ)| ≤
          (p*N)^((4:ℝ)/7)) ∧
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          (2*T)*((N : ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/(N : ℝ))*Real.log N))} ≤ (N:ℝ)^(-A) + (2:ℝ)^(2*n+5)/Real.log N := by
  obtain ⟨N₀,h₀⟩ := kernel_splitting_estimates.{u} n hθlo hθhi hT hφ hφ1 hCf hA
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have h1 : DegreeTypical y p σ := by simpa only [DegreeTypical,hcard] using hR1
  have h2 : SizeTypical y q Cf σ := by
    simpa only [SizeTypical,child,LocalTransition.sizeScale,hcard] using hR2
  simpa only [LocalTransition.KernelGood,CoarseKernel.Regular,LocalTransition.edgeScale,
    KernelEdgeSplitting.unionError,hcard] using
      h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2

/-- Expanded original R1/R2 inputs and literal manuscript output. -/
theorem original_kernel_splitting_epsilon {θ T φ Cf ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y →
      (∀ v t, |(σ.deg v t : ℝ)-p*y.sizes t| ≤
        Real.sqrt (p*N)*Real.log N^((2:ℝ)/3)) →
      (∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ)-
        Local.templateSizes y.sizes q (append s b)| ≤
        Cf*(Real.sqrt (N : ℝ)*Real.log N)) →
      (FineKernel.K σ).real {τ | ¬ (τ.part = FineState.refinement σ ∧
        (∀ v t, |(τ.deg v t : ℝ)-p*(Local.partSizes τ.part t : ℝ)| ≤
          (p*N)^((4:ℝ)/7)) ∧
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          (2*T)*((N : ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/(N : ℝ))*Real.log N))} ≤ ε := by
  obtain ⟨N₀,h₀⟩ := kernel_splitting_estimates_epsilon.{u} n hθlo hθhi hT hφ hφ1 hCf hε
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have h1 : DegreeTypical y p σ := by simpa only [DegreeTypical,hcard] using hR1
  have h2 : SizeTypical y q Cf σ := by
    simpa only [SizeTypical,child,LocalTransition.sizeScale,hcard] using hR2
  simpa only [LocalTransition.KernelGood,CoarseKernel.Regular,LocalTransition.edgeScale,
    KernelEdgeSplitting.unionError,hcard] using
      h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2

/-- The first history day n=0 is covered without a positive-level restriction. -/
theorem first_history_day {θ T φ Cf ε : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V 0) (q : Local.Tilt 0),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V 0,
      CoarseKernel.rho p σ = y →
      (∀ v t, |(σ.deg v t : ℝ)-p*y.sizes t| ≤
        Real.sqrt (p*N)*Real.log N^((2:ℝ)/3)) →
      (∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ)-
        Local.templateSizes y.sizes q (append s b)| ≤
        Cf*(Real.sqrt (N : ℝ)*Real.log N)) →
      (FineKernel.K σ).real {τ | ¬ (τ.part = FineState.refinement σ ∧
        (∀ v t, |(τ.deg v t : ℝ)-p*(Local.partSizes τ.part t : ℝ)| ≤
          (p*N)^((4:ℝ)/7)) ∧
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          (2*T)*((N : ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/(N : ℝ))*Real.log N))} ≤ ε := by
  exact original_kernel_splitting_epsilon.{u} 0 hθlo hθhi hT hφ hφ1 hCf hε

end MajorityDynamics.GraphProcess.KernelSplitting.Checks

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.sampleNext_cross_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.sampleNext_cross_degree

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.sampleNext_internal_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.sampleNext_internal_degree

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.next_degree_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.next_degree_nonneg

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.next_degree_le_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.next_degree_le_parent

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.next_degree_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.next_degree_le_card

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.internal_degree_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.internal_degree_real

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.cross_degree_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.cross_degree_real

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.negative_degree_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.negative_degree_real

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.above_parent_degree_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.above_parent_degree_real

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.internal_point_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.internal_point_tail

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.bipartite_point_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.bipartite_point_tail

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.entry_failure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.entry_failure_le

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.entry_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.entry_count

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.K_regularity_failure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.K_regularity_failure_le

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.sampled_point_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.sampled_point_tail

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.uniform_regularity_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.uniform_regularity_failure

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.kernel_splitting_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.kernel_splitting_estimates

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.kernel_splitting_estimates_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.kernel_splitting_estimates_epsilon

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.typical_kernel_splitting_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.typical_kernel_splitting_estimates

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.typical_kernel_splitting_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.typical_kernel_splitting_epsilon

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.Checks.original_S2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.Checks.original_S2

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.Checks.original_kernel_splitting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.Checks.original_kernel_splitting

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.Checks.original_kernel_splitting_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.Checks.original_kernel_splitting_epsilon

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.Checks.first_history_day' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.Checks.first_history_day


/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.manuscript_kernel_splitting_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.manuscript_kernel_splitting_epsilon
