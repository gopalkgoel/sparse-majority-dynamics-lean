import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Main

/-! Expanded original-input contracts and exact dependency audits. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks
open Universal BlockDecomposition KernelInputs
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
universe u

/-- The quantitative endpoint uses the original R1 and R2 bounds. Its event is
literal S1 and every ordered S3 inequality, including both diagonal cases. -/
theorem original_split_edges {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
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
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          (2*T)*((N : ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/(N : ℝ))*Real.log N))} ≤
        (2 : ℝ)^(2*n+5)/Real.log N := by
  obtain ⟨N₀,h₀⟩ := uniform_split_edges_failure.{u} n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have h1 : DegreeTypical y p σ := by simpa only [DegreeTypical,hcard] using hR1
  have h2 : SizeTypical y q Cf σ := by
    simpa only [SizeTypical,child,LocalTransition.sizeScale,hcard] using hR2
  simpa only [SplitEdgesGood,EdgesGood,EdgeGood,LocalTransition.edgeScale,hcard,unionError]
    using h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2

/-- Every error tolerance is chosen before the carrier, density, and fine state;
the same original degree and size inputs suffice. -/
theorem original_split_edges_epsilon {θ T φ Cf ε : ℝ} (n : ℕ)
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
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          (2*T)*((N : ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/(N : ℝ))*Real.log N))} ≤ ε := by
  obtain ⟨N₀,h₀⟩ := uniform_split_edges_failure_epsilon.{u}
    n hθlo hθhi hT hφ hφ1 hCf hε
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have h1 : DegreeTypical y p σ := by simpa only [DegreeTypical,hcard] using hR1
  have h2 : SizeTypical y q Cf σ := by
    simpa only [SizeTypical,child,LocalTransition.sizeScale,hcard] using hR2
  simpa only [SplitEdgesGood,EdgesGood,EdgeGood,LocalTransition.edgeScale,hcard]
    using h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2

/-- The only probabilistic premise still requested by the full KernelGood
consumer is S2, here expanded as the actual next state's degree inequalities. -/
theorem original_kernelGood_from_S2 {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
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
        Cf*(Real.sqrt (N : ℝ)*Real.log N)) → ∀ er : ℝ,
      (FineKernel.K σ).real {τ | ¬ (∀ v t,
        |(τ.deg v t : ℝ)-p*(Local.partSizes τ.part t : ℝ)| ≤
          (p*N)^((4:ℝ)/7))} ≤ er →
      (FineKernel.K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤
        er + (2 : ℝ)^(2*n+5)/Real.log N := by
  obtain ⟨N₀,h₀⟩ := uniform_kernelGood_failure.{u} n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2 er hS2
  have h1 : DegreeTypical y p σ := by simpa only [DegreeTypical,hcard] using hR1
  have h2 : SizeTypical y q Cf σ := by
    simpa only [SizeTypical,child,LocalTransition.sizeScale,hcard] using hR2
  have hr : (FineKernel.K σ).real {τ | ¬ CoarseKernel.Regular p τ.part τ.deg} ≤ er := by
    simpa only [CoarseKernel.Regular,hcard] using hS2
  simpa only [unionError] using h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2 er hr

/-- The unchanged full event retains both S1 and S2 alongside all of S3. -/
theorem kernelGood_expansion {V : Type*} [Fintype V] {n : ℕ}
    (y : Local.CoarseData V n) (p C : ℝ) (σ : FineState.State V n)
    (τ : FineState.State V (n+1)) :
    LocalTransition.KernelGood y p C σ τ ↔
      τ.part = FineState.refinement σ ∧
      (∀ v t, |(τ.deg v t : ℝ)-p*(Local.partSizes τ.part t : ℝ)| ≤
        (p*Fintype.card V)^((4:ℝ)/7)) ∧
      ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
        (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
          (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
        C*((Fintype.card V : ℝ)^2*p*
          Real.sqrt ((p*Fintype.card V)^((1:ℝ)/7)/(Fintype.card V : ℝ))*
          Real.log (Fintype.card V)) := Iff.rfl

/-- The full-typicality adapter includes level zero and uses the same coefficient. -/
theorem level_zero_typical {θ T φ Cf : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V 0) (q : Local.Tilt 0),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V 0,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      (FineKernel.K σ).real {τ | ¬ SplitEdgesGood y p (2*T) σ τ} ≤
        (2 : ℝ)^5/Real.log N :=
  uniform_typical_split_edges_failure 0 hθlo hθhi hT hφ hφ1 hCf

/-- Both actual component marginal laws, with the reverse orientation included. -/
theorem component_marginals {V : Type*} [Fintype V] {n : ℕ}
    (σ : FineState.State V n) (s t : History (n+1)) (hst : s ≠ t) :
    (FineKernel.componentLaw σ).map (internalSample σ s) =
      fixedDegreeLaw (fun v : Block σ.part s => (σ.deg v s).toNat) ∧
    (FineKernel.componentLaw σ).map (crossSample σ s t) =
      bipartiteFixedDegreeLaw (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat) ∧
    (FineKernel.componentLaw σ).map (crossSample σ t s) =
      bipartiteFixedDegreeLaw (fun w : Block σ.part t => (σ.deg w s).toNat)
        (fun v : Block σ.part s => (σ.deg v t).toNat) :=
  ⟨internalSample_law σ s,crossSample_law σ s t hst,crossSample_law σ t s hst.symm⟩

/-- All three actual count conventions are checked together: an ordered
rectangle, twice an internal edge count, and the literal child/complement cut. -/
theorem component_counts {V : Type*} [Fintype V] {n : ℕ}
    (σ : FineState.State V n) (F : ComponentFiber σ.part σ.deg) (p : ℝ)
    (s t : History (n+1)) (b c : Bool) (hbc : b ≠ c) :
    (CoarseKernel.rho p (FineKernel.sampleNext σ F)).realEdges (append s b) (append t c) =
      (rectangleCount (childInBlock σ s b) (childInBlock σ t c)
        (crossSample σ s t F) : ℝ) ∧
    (CoarseKernel.rho p (FineKernel.sampleNext σ F)).realEdges (append s b) (append s b) =
      2*(internalCount (childInBlock σ s b) (internalSample σ s F) : ℝ) ∧
    (CoarseKernel.rho p (FineKernel.sampleNext σ F)).realEdges (append s b) (append s c) =
      (cutCount (childInBlock σ s b) (internalSample σ s F) : ℝ) :=
  ⟨sampleNext_rectangle_count σ F p s t b c,sampleNext_internal_count σ F p s b,
    sampleNext_cut_count σ F p s b c hbc⟩

/-- The finite union runs over all ordered child pairs, even at level zero. -/
example : Fintype.card (History 1 × History 1 × Bool × Bool) = 16 := by
  exact child_pair_count 0

end MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks

/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_split_edges_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_split_edges_failure
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_split_edges_failure_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_split_edges_failure_epsilon
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_kernelGood_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_kernelGood_failure
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_typical_split_edges_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.uniform_typical_split_edges_failure
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.original_split_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.original_split_edges
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.original_split_edges_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.original_split_edges_epsilon
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.original_kernelGood_from_S2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.original_kernelGood_from_S2
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.kernelGood_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.kernelGood_expansion
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.level_zero_typical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.level_zero_typical
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.component_marginals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.component_marginals
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.component_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks.component_counts
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.internalSample_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.internalSample_law
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.transpose_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.transpose_law
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.crossSample_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.crossSample_law
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.internalSample_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.internalSample_real
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.crossSample_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.crossSample_real
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.sampleNext_rectangle_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.sampleNext_rectangle_count
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.sampleNext_internal_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.sampleNext_internal_count
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.sampleNext_cut_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.sampleNext_cut_count
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_splitEdges_failure_eq_edges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_splitEdges_failure_eq_edges
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.child_pair_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.child_pair_count
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_edges_failure_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_edges_failure_le
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_splitEdges_failure_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_splitEdges_failure_le
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_kernelGood_failure_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.K_kernelGood_failure_le
/-- info: 'MajorityDynamics.GraphProcess.KernelEdgeSplitting.pair_failure_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelEdgeSplitting.pair_failure_le
