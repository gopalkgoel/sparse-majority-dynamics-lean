import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal KernelInputs
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
variable {V : Type*} [Fintype V] {n : ℕ}

theorem internal_center (y : Local.CoarseData V n) (σ : FineState.State V n)
    (s : History (n+1)) (b : Bool) :
    (RowArray.childMass (RowArray.stateArray σ) s b s : ℝ) *
      (RowArray.childMass (RowArray.stateArray σ) s b s : ℝ) / y.realEdges s s =
    2 * (∑ v ∈ childInBlock σ s b, ((σ.deg v s).toNat : ℝ))^2 /
      (4 * ((y.edge s s / 2).toNat : ℝ)) := by
  rw [childInBlock_nat_mass_real]
  change _ / (y.edge s s : ℝ) = _
  rw [← internal_total_half_real y s]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num
  ring

theorem cut_center (y : Local.CoarseData V n) (σ : FineState.State V n)
    (s : History (n+1)) (b c : Bool) (hbc : b ≠ c) :
    (RowArray.childMass (RowArray.stateArray σ) s b s : ℝ) *
      (RowArray.childMass (RowArray.stateArray σ) s c s : ℝ) / y.realEdges s s =
    (∑ v ∈ childInBlock σ s b, ((σ.deg v s).toNat : ℝ)) *
      (∑ v ∈ Finset.univ \ childInBlock σ s b, ((σ.deg v s).toNat : ℝ)) /
      (2 * ((y.edge s s / 2).toNat : ℝ)) := by
  have hc : (!b) = c := by cases b <;> cases c <;> simp_all
  rw [childInBlock_complement, hc, childInBlock_nat_mass_real, childInBlock_nat_mass_real]
  change _ / (y.edge s s : ℝ) = _
  rw [internal_total_half_real]

theorem cross_center (y : Local.CoarseData V n) (σ : FineState.State V n)
    (s t : History (n+1)) (b c : Bool) :
    (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
      (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t =
    (∑ v ∈ childInBlock σ s b, ((σ.deg v t).toNat : ℝ)) *
      (∑ w ∈ childInBlock σ t c, ((σ.deg w s).toNat : ℝ)) /
      ((y.edge s t).toNat : ℝ) := by
  rw [childInBlock_nat_mass_real, childInBlock_nat_mass_real, cross_total_nat_real]
  rfl

theorem verified_scale {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ) (hT : 1 < T)
    (s : History (n+1)) :
    edgeThreshold (y.sizes s) p ≤ (2*T)*LocalTransition.edgeScale (Fintype.card V) p := by
  have hN : 1 ≤ (Fintype.card V : ℝ) :=
    (by linarith [(h.parent_sizes s).2.2] : (1 : ℝ) ≤ y.sizes s).trans
      (h.parent_sizes s).2.1
  have hn := LocalTransition.edgeScale_nonneg (Fintype.card V) p hN h.p_pos.le
  have hs := h.edge_scale s
  change localEdgeScale (y.sizes s : ℝ) p ≤ _
  nlinarith

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
