import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The natural component degrees sum to the literal prescribed ordered total. -/
theorem block_degree_total {p : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (hρ : CoarseKernel.rho p σ = y)
    (s t : History (n+1)) :
    ∑ v : Block σ.part s, (σ.deg v t).toNat = (y.edge s t).toNat := by
  have hs : (∑ v : Block σ.part s, (σ.deg v t : ℤ)) = y.edge s t := by
    rw [← congrFun (congrFun (KernelInputs.fiber_totals hρ) s) t]
    exact (Finset.sum_subtype (History.block σ.part s)
      (fun v => History.mem_block σ.part s v) (fun v => σ.deg v t)).symm
  have hn : ((∑ v : Block σ.part s, (σ.deg v t).toNat : ℕ) : ℤ) =
      ((y.edge s t).toNat : ℤ) := by
    rw [Nat.cast_sum, KernelInputs.cross_total_nat]
    simpa only [state_degree_toNat_cast] using hs
  exact_mod_cast hn

/-- The actual internal component satisfies every original C.1 graph input. -/
theorem graph_input {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : KernelInputs.Verified θ T φ p U y σ)
    (hρ : CoarseKernel.rho p σ = y) (s : History (n+1)) :
    GraphInput (y.sizes s) (y.edge s s / 2).toNat p U
      (fun v : Block σ.part s => (σ.deg v s).toNat) := by
  obtain ⟨G,hG⟩ := KernelInputs.internal_family_nonempty σ s
  refine ⟨KernelInputs.block_card hρ s, ?_, ?_, h.internal_count s, ?_⟩
  · intro v
    have hb := G.degree_lt_card_verts v
    rw [show G.degree v = (σ.deg v s).toNat from hG v,
      KernelInputs.block_card hρ s] at hb
    omega
  · rw [block_degree_total hρ]
    have hh := KernelInputs.internal_total_half y s
    have hc := KernelInputs.cross_total_nat y s s
    omega
  · intro v
    rw [KernelInputs.degree_cast_real]
    exact h.degree_window v s s

/-- The actual cross component satisfies every original C.1 bipartite input.
This statement also permits equal block labels; no new realization premise is needed. -/
theorem bipartite_input {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : KernelInputs.Verified θ T φ p U y σ)
    (hρ : CoarseKernel.rho p σ = y) (s t : History (n+1)) :
    BipartiteInput (y.sizes s) (y.sizes t) (y.edge s t).toNat p U
      (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat) := by
  obtain ⟨E,hE⟩ := KernelInputs.cross_family_nonempty σ s t
  refine ⟨KernelInputs.block_card hρ s, KernelInputs.block_card hρ t,
    ?_, (h.relative_sizes s t).2, ?_, ?_, block_degree_total hρ s t,
    ?_, ?_, ?_, ?_⟩
  · simpa only [inv_mul_eq_div] using (h.relative_sizes s t).1
  · intro v
    rw [← show leftDegree E v = (σ.deg v t).toNat from hE.1 v, leftDegree]
    simpa only [KernelInputs.block_card hρ t] using
      (Finset.card_le_univ (leftNeighbors E v))
  · intro w
    rw [← show rightDegree E w = (σ.deg w s).toNat from hE.2 w, rightDegree]
    simpa only [KernelInputs.block_card hρ s] using
      (Finset.card_le_univ (rightNeighbors E w))
  · rw [block_degree_total hρ t s, y.edge_symm t s]
  · simpa only [KernelInputs.cross_total_nat_real] using h.cross_count s t
  · intro v
    rw [KernelInputs.degree_cast_real]
    exact h.degree_window v t t
  · intro w
    rw [KernelInputs.degree_cast_real]
    exact h.degree_window w t s

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
