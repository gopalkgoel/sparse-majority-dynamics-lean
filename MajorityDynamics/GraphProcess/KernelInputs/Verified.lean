import MajorityDynamics.GraphProcess.KernelInputs.Children
import MajorityDynamics.GraphProcess.KernelInputs.Components
import MajorityDynamics.GraphProcess.KernelInputs.Scales
import MajorityDynamics.GraphProcess.KernelInputs.TailAlgebra

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelInputs
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- A collection of conclusions, produced from original inputs by `uniform_inputs`.
No consumer needs to supply this as an additional original-paper hypothesis. -/
structure Verified (θ T φ p U : ℝ) (y : Local.CoarseData V n)
    (σ : FineState.State V n) : Prop where
  N_pos : 0 < (Fintype.card V : ℝ)
  p_pos : 0 < p
  p_lt_one : p < 1
  part_eq : σ.part = y.part
  parent_sizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ) ∧
    (y.sizes s : ℝ) ≤ Fintype.card V ∧ 2 ≤ (y.sizes s : ℝ)
  child_sizes : ∀ s b, φ*Fintype.card V/(2*T) ≤ ((child σ s b).card : ℝ) ∧
    ((child σ s b).card : ℝ) ≤ Fintype.card V ∧ 0 < ((child σ s b).card : ℝ)
  density : ∀ t, U⁻¹*(y.sizes t : ℝ)^(-θ) < p ∧ p < U*(y.sizes t : ℝ)^(-θ)
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
theorem Verified.bipartite_degrees {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ)
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
theorem Verified.next_kappa_failure {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ)
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

end MajorityDynamics.GraphProcess.KernelInputs
