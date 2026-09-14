import MajorityDynamics.GraphProcess.KernelInputs.Main

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelInputs.Checks
open Universal
open MajorityDynamics.Probability.FixedDegreeSampling
universe u

/-- Expanded original-input endpoint: constant and threshold precede all finite data. -/
theorem original_windows {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ U : ℝ, 1 < U ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y →
      (∀ v t, |(σ.deg v t : ℝ)-p*y.sizes t| ≤
        Real.sqrt (p*Fintype.card V)*Real.log (Fintype.card V)^((2:ℝ)/3)) →
      (∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ)-
        Local.templateSizes y.sizes q (append s b)| ≤
        Cf*(Real.sqrt (Fintype.card V)*Real.log (Fintype.card V))) →
      (0 < p ∧ p < 1) ∧
      (∀ s, (N:ℝ)/T ≤ (y.sizes s : ℝ) ∧ (y.sizes s : ℝ) ≤ N ∧ 2 ≤ (y.sizes s : ℝ)) ∧
      (∀ s b, φ*N/(2*T) ≤ ((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) ∧
        ((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) ≤ N ∧
        0 < ((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ)) ∧
      (∀ t, U⁻¹*(y.sizes t : ℝ)^(-θ) < p ∧ p < U*(y.sizes t : ℝ)^(-θ)) ∧
      (∀ s t, U⁻¹*(y.sizes t : ℝ) ≤ (y.sizes s : ℝ) ∧ (y.sizes s : ℝ) ≤ U*(y.sizes t : ℝ)) ∧
      (∀ s t b, U⁻¹*(y.sizes t : ℝ) ≤ ((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) ∧
        U⁻¹*(y.sizes t : ℝ) ≤ (y.sizes s : ℝ)-(RowArray.childSet (RowArray.stateArray σ) s b).card) ∧
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        U*(y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)) ∧
      (∀ t, 2*((y.edge t t/2).toNat : ℤ) = y.edge t t ∧
        |((y.edge t t/2).toNat : ℝ)-p*(y.sizes t : ℝ)*((y.sizes t : ℝ)-1)/2| ≤
          U*(y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)) ∧
      (∀ v u t, |(σ.deg v t : ℝ)-p*y.sizes t| ≤ (p*y.sizes u)^((4:ℝ)/7)) ∧
      (∀ v u t, |((σ.deg v u : ℝ)-p*y.sizes u)/Real.sqrt (p*y.sizes u)| ≤ Real.log (y.sizes t)) ∧
      (∀ v u, (σ.deg v u : ℝ) = p*y.sizes u +
        (((σ.deg v u : ℝ)-p*y.sizes u)/Real.sqrt (p*y.sizes u))*Real.sqrt (p*y.sizes u)) := by
  obtain ⟨U,hU,N₀,h₀⟩ := uniform_inputs n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨U,hU,N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ h1 h2
  have h := h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2
  exact ⟨⟨h.p_pos,h.p_lt_one⟩,by simpa only [hcard] using h.parent_sizes,
    by simpa only [hcard] using h.child_sizes,h.density,h.relative_sizes,h.subset_sizes,
    h.cross_count,fun t => ⟨internal_total_half y t,h.internal_count t⟩,
    h.degree_window,h.normalized_window,h.normalized_identity⟩

/-- Direct same-parameter FiberTypical endpoint at level zero. -/
theorem original_level_zero {θ T φ Cf : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ U : ℝ, 1 < U ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V 0) (q : Local.Tilt 0),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V 0,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      Verified θ T φ p U y σ :=
  uniform_typical_inputs 0 hθlo hθhi hT hφ hφ1 hCf

/-- The two different C.2 normalizations are visible together. -/
example {V : Type*} [Fintype V] {n : ℕ} {θ T φ p U : ℝ}
    {y : Local.CoarseData V n} {σ : FineState.State V n}
    (h : Verified θ T φ p U y σ) (s t : History (n+1)) :
    (∀ v : BlockDecomposition.Block σ.part s,
      |((σ.deg v t).toNat : ℝ)-p*y.sizes t| ≤ (p*y.sizes t)^((4:ℝ)/7) ∧
      |(((σ.deg v t).toNat : ℝ)-p*y.sizes t)/Real.sqrt (p*y.sizes t)| ≤ Real.log (y.sizes t)) ∧
    (∀ w : BlockDecomposition.Block σ.part t,
      |((σ.deg w s).toNat : ℝ)-p*y.sizes s| ≤ (p*y.sizes t)^((4:ℝ)/7) ∧
      |(((σ.deg w s).toNat : ℝ)-p*y.sizes s)/Real.sqrt (p*y.sizes s)| ≤ Real.log (y.sizes t)) :=
  h.bipartite_degrees s t

/-- Exact existing component families and their counts, without a probability or
independent graphicality premise. -/
theorem actual_components {V : Type*} [Fintype V] {n : ℕ} {p : ℝ}
    {y : Local.CoarseData V n} {σ : FineState.State V n}
    (hρ : CoarseKernel.rho p σ = y) (s t : History (n+1)) :
    (∃ G ∈ graphFamily (fun v : BlockDecomposition.Block σ.part s => (σ.deg v s).toNat),
      G.edgeFinset.card = (y.edge s s/2).toNat) ∧
    (∃ E ∈ bipartiteFamily (fun v : BlockDecomposition.Block σ.part s => (σ.deg v t).toNat)
      (fun w : BlockDecomposition.Block σ.part t => (σ.deg w s).toNat),
      (E.ncard : ℤ) = y.edge s t) :=
  ⟨internal_component_exists hρ s,cross_component_exists hρ s t⟩

/-- The subsets passed to those families are literally the original children,
with exact complement and mass identities. -/
theorem actual_subsets {V : Type*} [Fintype V] {n : ℕ}
    (σ : FineState.State V n) (s t : History (n+1)) (b : Bool) :
    (childInBlock σ s b).card = (RowArray.childSet (RowArray.stateArray σ) s b).card ∧
    Finset.univ \ childInBlock σ s b = childInBlock σ s (!b) ∧
    (∑ v ∈ childInBlock σ s b, ((σ.deg v t).toNat : ℝ)) =
      (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) :=
  ⟨childInBlock_card σ s b,childInBlock_complement σ s b,childInBlock_nat_mass_real σ s b t⟩

/-- The exact tail and edge scales are preserved under original inputs. -/
theorem original_tail_scales {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      (∀ t, 2*((y.sizes t : ℝ)^2*p*Real.sqrt ((p*y.sizes t)^((1:ℝ)/7)/(y.sizes t : ℝ))*
        Real.log (y.sizes t)) ≤ 2*T*((N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/(N:ℝ))*Real.log N)) ∧
      (∀ s t b (a : ℤ), (p*N)^((4:ℝ)/7) < |(a:ℝ)-p*(RowArray.childSet (RowArray.stateArray σ) s b).card| →
        (Real.log (y.sizes t))^100 ≤ (p*N)^((1:ℝ)/14) ∧
        (p*N)^((1:ℝ)/14) ≤ |((a:ℝ)-p*(RowArray.childSet (RowArray.stateArray σ) s b).card)/
          Real.sqrt (p*(RowArray.childSet (RowArray.stateArray σ) s b).card)|) := by
  obtain ⟨U,_hU,N₀,h₀⟩ := uniform_inputs n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ h1 h2
  have h := h₀ N hN V hcard p hlo hhi y q hLA σ hρ h1 h2
  exact ⟨by simpa only [hcard,localEdgeScale,LocalTransition.edgeScale] using h.doubled_edge_scale,
    by simpa only [hcard] using h.tail_threshold⟩

/-- Additional tail exponent requests only enlarge N₀; they do not enter U. -/
theorem original_union_absorption (n : ℕ) {θ T c A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hc : 0 < c) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      (N:ℝ)*2^(n+2)*(N+1)*Real.exp (-c*(p*N)^((1:ℝ)/7)) ≤ (N:ℝ)^(-A) :=
  Numerics.union_absorption n hθlo hθhi hT hc hA

end MajorityDynamics.GraphProcess.KernelInputs.Checks

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.child_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.child_partition

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.child_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.child_complement

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.child_size_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.child_size_lower

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.child_complement_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.child_complement_card

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.childInBlock_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.childInBlock_card

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.childInBlock_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.childInBlock_complement

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.childInBlock_nat_mass_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.childInBlock_nat_mass_real

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_total_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_total_half

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_total_half_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_total_half_real

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.cross_total_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.cross_total_nat

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_family_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_family_nonempty

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.cross_family_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.cross_family_nonempty

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_family_edge_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_family_edge_count

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.cross_family_edge_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.cross_family_edge_count

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_component_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_component_exists

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.cross_component_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.cross_component_exists

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Numerics.uniform_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Numerics.uniform_regime

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Numerics.relative_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Numerics.relative_density

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Numerics.relative_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Numerics.relative_sizes

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Numerics.union_absorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Numerics.union_absorption

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.count_scale_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.count_scale_bound

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.cross_count_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.cross_count_window

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_count_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_count_window

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.localEdgeScale_le_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.localEdgeScale_le_global

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.doubled_localEdgeScale_le_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.doubled_localEdgeScale_le_global

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.local_edge_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.local_edge_event

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.doubled_local_edge_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.doubled_local_edge_event

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.normalized_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.normalized_reconstruct

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.normalized_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.normalized_abs_le

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.kappa_normalized_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.kappa_normalized_lower

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.kappa_tail_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.kappa_tail_exp_le

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_center_double' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_center_double

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.internal_cross_center' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.internal_cross_center

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Verified.bipartite_degrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Verified.bipartite_degrees

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Verified.next_kappa_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Verified.next_kappa_failure

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.uniform_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.uniform_inputs

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.uniform_typical_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.uniform_typical_inputs

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Checks.original_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Checks.original_windows

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Checks.original_level_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Checks.original_level_zero

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Checks.actual_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Checks.actual_components

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Checks.actual_subsets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Checks.actual_subsets

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Checks.original_tail_scales' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Checks.original_tail_scales

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Checks.original_union_absorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Checks.original_union_absorption
