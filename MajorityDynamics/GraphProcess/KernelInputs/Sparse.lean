import MajorityDynamics.GraphProcess.KernelInputs.Main
import MajorityDynamics.GraphProcess.KernelInputs.SparseNumerics

/-! Actual deterministic kernel inputs on the uniform sparse range. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelInputs
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}
universe u

structure SparseVerified (θ T φ p U : ℝ) (y : Local.CoarseData V n)
    (σ : FineState.State V n) : Prop where
  N_pos : 0 < (Fintype.card V : ℝ)
  p_pos : 0 < p
  p_lt_one : p < 1
  part_eq : σ.part = y.part
  parent_sizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ) ∧
    (y.sizes s : ℝ) ≤ Fintype.card V ∧ 2 ≤ (y.sizes s : ℝ)
  child_sizes : ∀ s b, φ*Fintype.card V/(2*T) ≤ ((child σ s b).card : ℝ) ∧
    ((child σ s b).card : ℝ) ≤ Fintype.card V ∧ 0 < ((child σ s b).card : ℝ)
  density : ∀ t, U⁻¹*(y.sizes t : ℝ)^(-θ) < p ∧ p < U*(y.sizes t : ℝ)^(-(1/2 : ℝ))
  relative_sizes : ∀ s t, U⁻¹*(y.sizes t : ℝ) ≤ (y.sizes s : ℝ) ∧
    (y.sizes s : ℝ) ≤ U*(y.sizes t : ℝ)
  subset_sizes : ∀ s t b, U⁻¹*(y.sizes t : ℝ) ≤ ((child σ s b).card : ℝ) ∧
    U⁻¹*(y.sizes t : ℝ) ≤ (y.sizes s : ℝ) - (child σ s b).card
  cross_count : ∀ s t, |(y.edge s t : ℝ) - p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
    U*(y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)
  internal_count : ∀ t, |((y.edge t t / 2).toNat : ℝ) -
    p*(y.sizes t : ℝ)*((y.sizes t : ℝ)-1)/2| ≤
      U*(y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)
  radius_window : ∀ u, Real.sqrt (p*Fintype.card V)*
    Real.log (Fintype.card V)^((2:ℝ)/3) ≤ (p*y.sizes u)^((4:ℝ)/7)
  radius_log_window : ∀ u t, Real.sqrt (p*Fintype.card V)*
    Real.log (Fintype.card V)^((2:ℝ)/3) ≤
      Real.sqrt (p*y.sizes u)*Real.log (y.sizes t)
  degree_window : ∀ v u t, |(σ.deg v t : ℝ)-p*y.sizes t| ≤ (p*y.sizes u)^((4:ℝ)/7)
  normalized_window : ∀ v u t,
    |((σ.deg v u : ℝ)-p*y.sizes u)/Real.sqrt (p*y.sizes u)| ≤ Real.log (y.sizes t)
  normalized_identity : ∀ v u, (σ.deg v u : ℝ) = p*y.sizes u +
    (((σ.deg v u : ℝ)-p*y.sizes u)/Real.sqrt (p*y.sizes u))*Real.sqrt (p*y.sizes u)
  edge_scale : ∀ t, localEdgeScale (y.sizes t : ℝ) p ≤
    LocalTransition.edgeScale (Fintype.card V) p
  doubled_edge_scale : ∀ t, 2*localEdgeScale (y.sizes t : ℝ) p ≤
    2*T*LocalTransition.edgeScale (Fintype.card V) p
  tail_threshold : ∀ s t b (a : ℤ),
    (p*Fintype.card V)^((4:ℝ)/7) < |(a : ℝ)-p*(child σ s b).card| →
    (Real.log (y.sizes t))^100 ≤ (p*Fintype.card V)^((1:ℝ)/14) ∧
    (p*Fintype.card V)^((1:ℝ)/14) ≤
      |((a : ℝ)-p*(child σ s b).card)/Real.sqrt (p*(child σ s b).card)|

/-- Both side degree windows share the right-block C.1 tolerance, while the
C.2 normalizations use distinct side-specific square roots. -/
theorem SparseVerified.bipartite_degrees {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : SparseVerified θ T φ p U y σ)
    (s t : History (n+1)) :
    (∀ v : BlockDecomposition.Block σ.part s,
      |((σ.deg v t).toNat : ℝ)-p*y.sizes t| ≤ (p*y.sizes t)^((4:ℝ)/7) ∧
      |(((σ.deg v t).toNat : ℝ)-p*y.sizes t)/Real.sqrt (p*y.sizes t)| ≤ Real.log (y.sizes t)) ∧
    (∀ w : BlockDecomposition.Block σ.part t,
      |((σ.deg w s).toNat : ℝ)-p*y.sizes s| ≤ (p*y.sizes t)^((4:ℝ)/7) ∧
      |(((σ.deg w s).toNat : ℝ)-p*y.sizes s)/Real.sqrt (p*y.sizes s)| ≤ Real.log (y.sizes t)) := by
  constructor
  · intro v
    rw [degree_cast_real]
    exact ⟨h.degree_window v t t,h.normalized_window v t t⟩
  · intro w
    rw [degree_cast_real]
    exact ⟨h.degree_window w t s,h.normalized_window w s t⟩

/-- The actual next-state kappa failure supplies an original integer degree
and an actual child subset. No pointwise tail certificate is an input. -/
theorem SparseVerified.next_kappa_failure {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : SparseVerified θ T φ p U y σ)
    (τ : FineState.State V (n+1)) (hpart : τ.part = FineState.refinement σ)
    (hbad : ¬ CoarseKernel.Regular p τ.part τ.deg) :
    ∃ (v : V) (s : History (n+1)) (b : Bool),
      (p*Fintype.card V)^((4:ℝ)/7) < |(τ.deg v (append s b) : ℝ)-p*(child σ s b).card| ∧
      (Real.log (y.sizes s))^100 ≤
        |((τ.deg v (append s b) : ℝ)-p*(child σ s b).card)/
          Real.sqrt (p*(child σ s b).card)| := by
  simp only [CoarseKernel.Regular, not_forall, not_le] at hbad
  obtain ⟨v,u,hu⟩ := hbad
  let s := parent u
  let b := last u
  have he : append s b = u := append_parent_last u
  have hc : Local.partSizes τ.part u = (child σ s b).card := by
    simp only [child, hpart, RowArray.childSet_stateArray, he, History.block_card_partSizes]
  rw [hc] at hu
  refine ⟨v,s,b,?_,?_⟩
  · simpa only [he] using hu
  · have ht := h.tail_threshold s s b (τ.deg v u) hu
    simpa only [he] using ht.1.trans ht.2


theorem uniform_inputs_sparse {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (_hCf : 0 ≤ Cf) :
    ∃ U : ℝ, 1 < U ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      SparseVerified θ T φ p U y σ := by
  obtain ⟨N₀,h₀⟩ := Numerics.uniform_regime_sparse (Cf:=Cf) hθlo hθhi hT hφ hφ1
  have hU := Numerics.parameter_bounds hT hφ hφ1
  refine ⟨Numerics.parameter T φ,hU.1,N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ h1 h2
  have hg := h₀ N hN p hlo hhi
  have hN0 := hg.N_pos
  have hp0 := hg.p_pos
  have hT0 : 0 < T := by linarith
  have hs (s : History (n+1)) : (N:ℝ)/T ≤ (y.sizes s : ℝ) := by
    simpa only [hcard, div_eq_mul_inv, mul_comm] using hLA.sizes s
  have hsN (s : History (n+1)) : (y.sizes s : ℝ) ≤ N := by
    exact_mod_cast (y.sizes_le_card s).trans_eq hcard
  have hs2 (s : History (n+1)) : (2:ℝ) ≤ y.sizes s := hg.block_size _ (hs s) (hsN s)
  have hs0 (s : History (n+1)) : (0:ℝ) < y.sizes s := by linarith [hs2 s]
  have herr : Cf*LocalTransition.sizeScale (Fintype.card V) ≤ φ*Fintype.card V/(2*T) := by
    simpa only [LocalTransition.sizeScale, hcard, ← mul_assoc] using hg.size_error
  have hc (s : History (n+1)) (b : Bool) : φ*N/(2*T) ≤ ((child σ s b).card : ℝ) := by
    simpa only [hcard] using child_size_lower hT0 hφ.le hLA h2 herr s b
  have hcN (s : History (n+1)) (b : Bool) : ((child σ s b).card : ℝ) ≤ N := by
    exact_mod_cast (child_card_le σ s b).trans_eq hcard
  have hc0 (s : History (n+1)) (b : Bool) : (0:ℝ) < (child σ s b).card :=
    (by positivity : (0:ℝ) < φ*N/(2*T)).trans_le (hc s b)
  have hrel (s t : History (n+1)) (b : Bool) :=
    Numerics.relative_sizes hT hφ hφ1 hg.N_pos (hs t) (hsN t) (hs s) (hsN s) (hc s b)
  have hcounts (s t : History (n+1)) :
      |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*((N:ℝ)^2*p/Real.sqrt (p*N)) := by
    simpa only [Local.CoarseData.realEdges, Local.edgeScale, hcard] using hLA.edge_scale s t
  have hcount_scale (t : History (n+1)) :
      2*T^3*((y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)) ≤
        Numerics.parameter T φ*(y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t) := by
    calc
      _ ≤ Numerics.parameter T φ*((y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)) :=
        mul_le_mul_of_nonneg_right hU.2.2.1 (by positivity)
      _ = _ := by ring
  refine {
    N_pos := by simpa only [hcard] using hg.N_pos
    p_pos := hg.p_pos
    p_lt_one := hg.p_lt_one
    part_eq := fiber_part hρ
    parent_sizes := ?_
    child_sizes := ?_
    density := fun t => hg.density _ (hs t) (hsN t)
    relative_sizes := fun s t => ⟨(hrel s t false).1,(hrel s t false).2.1⟩
    subset_sizes := ?_
    cross_count := ?_
    internal_count := ?_
    radius_window := ?_
    radius_log_window := ?_
    degree_window := ?_
    normalized_window := ?_
    normalized_identity := fun v t => normalized_reconstruct hg.p_pos (hs0 t)
    edge_scale := ?_
    doubled_edge_scale := ?_
    tail_threshold := ?_ }
  · intro s
    simpa only [hcard] using (show (N:ℝ)/T ≤ (y.sizes s : ℝ) ∧
      (y.sizes s : ℝ) ≤ N ∧ 2 ≤ (y.sizes s : ℝ) from ⟨hs s,hsN s,hs2 s⟩)
  · intro s b
    simpa only [hcard] using (show φ*N/(2*T) ≤ ((child σ s b).card : ℝ) ∧
      ((child σ s b).card : ℝ) ≤ N ∧ 0 < ((child σ s b).card : ℝ) from ⟨hc s b,hcN s b,hc0 s b⟩)
  · intro s t b
    refine ⟨(hrel s t b).2.2,?_⟩
    rw [child_complement_card σ hρ s b]
    exact (hrel s t (!b)).2.2
  · intro s t
    exact (cross_count_window hT hg.p_pos hg.p_lt_one.le (hs2 t) (hs t) (hsN t)
      (hcounts s t)).trans (hcount_scale t)
  · intro t
    have he : (y.edge t t : ℝ) = 2*((y.edge t t/2).toNat : ℝ) :=
      (internal_total_half_real y t).symm
    have hh : |(y.edge t t : ℝ)-p*(y.sizes t : ℝ)^2| ≤
        T*((N:ℝ)^2*p/Real.sqrt (p*N)) := by
      simpa only [pow_two, mul_assoc] using hcounts t t
    exact (internal_count_window hT hg.p_pos hg.p_lt_one.le (hs2 t) (hs t) (hsN t)
      he hh).trans (hcount_scale t)
  · intro t
    simpa only [hcard] using hg.degree_window _ (hs t) (hsN t)
  · intro s t
    simpa only [hcard] using hg.log_window _ _ (hs t) (hsN t) (hs s) (hsN s)
  · intro v u t
    exact (h1 v t).trans (by simpa only [hcard] using hg.degree_window _ (hs u) (hsN u))
  · intro v s t
    apply normalized_abs_le hg.p_pos (hs0 s)
    exact (h1 v s).trans (by simpa only [hcard] using hg.log_window _ _ (hs t) (hsN t) (hs s) (hsN s))
  · intro t
    exact localEdgeScale_le_global (by linarith [hs2 t])
      (by simpa only [hcard] using hsN t) hg.p_pos
  · intro t
    exact doubled_localEdgeScale_le_global (by linarith [hs2 t])
      (by simpa only [hcard] using hsN t) hg.p_pos hT.le
  · intro s t b a hbad
    refine ⟨by simpa only [hcard] using hg.growth _ (hs t) (hsN t),?_⟩
    exact kappa_normalized_lower hg.p_pos (hc0 s b)
      (by simpa only [hcard] using hcN s b) hbad

/-- Direct unchanged FiberTypical consumer; its R3 component is not used. -/
theorem uniform_typical_inputs_sparse {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ U : ℝ, 1 < U ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      SparseVerified θ T φ p U y σ := by
  obtain ⟨U,hU,N₀,h₀⟩ := uniform_inputs_sparse n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨U,hU,N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ htyp
  exact h₀ N hN V hcard p hlo hhi y q hLA σ hρ htyp.1 htyp.2.1


end MajorityDynamics.GraphProcess.KernelInputs

