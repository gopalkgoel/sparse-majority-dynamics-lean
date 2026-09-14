import MajorityDynamics.GraphProcess.CoarseKernel.Basic

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelInputs
open History FineState Local BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The named fiber identifies the actual partition, without a relabeling. -/
theorem fiber_part {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) : σ.part = y.part :=
  congrArg CoarseData.part h

theorem fiber_totals {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) : edgeTotals σ.part σ.deg = y.edge :=
  congrArg CoarseData.edge h

theorem block_card {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) (s : Universal.History (n+1)) :
    Fintype.card (Block σ.part s) = y.sizes s := by
  have hc : Fintype.card (Block σ.part s) = (block σ.part s).card := by
    simp only [Block, block, Fintype.card_subtype]
    congr 1
    ext v
    simp
  rw [hc, block_card_partSizes, fiber_part h]
  rfl

theorem degree_cast_real (σ : State V n) (v : V) (t : Universal.History (n+1)) :
    ((σ.deg v t).toNat : ℝ) = (σ.deg v t : ℝ) := by
  exact_mod_cast state_degree_toNat_cast σ v t

/-- The existing natural-degree sampling API has exactly the original center. -/
theorem component_degree_center {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) (v : V) (t : Universal.History (n+1)) :
    ((σ.deg v t).toNat : ℝ) - p * Fintype.card (Block σ.part t) =
      (σ.deg v t : ℝ) - p * y.sizes t := by
  rw [degree_cast_real, block_card h]

/-- Exact natural halving of the ordered diagonal total. -/
theorem internal_total_half (y : CoarseData V n) (s : Universal.History (n+1)) :
    2 * (((y.edge s s / 2).toNat : ℕ) : ℤ) = y.edge s s := by
  obtain ⟨k,hk⟩ := y.edge_even s
  have hn := y.edge_nonneg s s
  have hkn : 0 ≤ k := by omega
  have he : y.edge s s / 2 = k := by omega
  rw [he, Int.toNat_of_nonneg hkn]
  omega

theorem internal_total_half_real (y : CoarseData V n) (s : Universal.History (n+1)) :
    2 * ((y.edge s s / 2).toNat : ℝ) = (y.edge s s : ℝ) := by
  exact_mod_cast internal_total_half y s

theorem cross_total_nat (y : CoarseData V n) (s t : Universal.History (n+1)) :
    ((y.edge s t).toNat : ℤ) = y.edge s t :=
  Int.toNat_of_nonneg (y.edge_nonneg s t)

theorem cross_total_nat_real (y : CoarseData V n) (s t : Universal.History (n+1)) :
    ((y.edge s t).toNat : ℝ) = (y.edge s t : ℝ) := by
  exact_mod_cast cross_total_nat y s t

/-- Existing component families are inhabited by restrictions of the actual realizer. -/
theorem internal_family_nonempty (σ : State V n) (s : Universal.History (n+1)) :
    (graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat)).Nonempty :=
  state_graphFamily_nonempty σ s

theorem cross_family_nonempty (σ : State V n) (s t : Universal.History (n+1)) :
    (bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat)).Nonempty :=
  state_bipartiteFamily_nonempty σ s t

/-- Every sampled internal component has the prescribed undirected count. -/
theorem internal_family_edge_count {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) (s : Universal.History (n+1))
    (G : SimpleGraph (Block σ.part s))
    (hG : G ∈ graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat)) :
    G.edgeFinset.card = (y.edge s s / 2).toNat := by
  have hs : (∑ v : Block σ.part s, (σ.deg v s : ℤ)) = y.edge s s := by
    rw [← congrFun (congrFun (fiber_totals h) s) s]
    exact (Finset.sum_subtype (block σ.part s) (fun v => mem_block σ.part s v)
      (fun v => σ.deg v s)).symm
  have hd : (∑ v : Block σ.part s, (G.degree v : ℤ)) = y.edge s s := by
    simpa only [show ∀ v, G.degree v = (σ.deg v s).toNat from hG,
      state_degree_toNat_cast] using hs
  have he : (∑ v : Block σ.part s, (G.degree v : ℤ)) =
      2 * (G.edgeFinset.card : ℤ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hh := internal_total_half y s
  omega

/-- Every sampled cross component has the literal ordered cross total. -/
theorem cross_family_edge_count {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) (s t : Universal.History (n+1))
    (E : CrossEdges (Block σ.part s) (Block σ.part t))
    (hE : E ∈ bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat)) :
    (E.ncard : ℤ) = y.edge s t := by
  rw [bipartite_edge_count, Nat.cast_sum]
  simp_rw [hE.1, state_degree_toNat_cast]
  rw [← congrFun (congrFun (fiber_totals h) s) t]
  exact (Finset.sum_subtype (block σ.part s) (fun v => mem_block σ.part s v)
    (fun v => σ.deg v t)).symm

theorem cross_family_edge_count_nat {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) (s t : Universal.History (n+1))
    (E : CrossEdges (Block σ.part s) (Block σ.part t))
    (hE : E ∈ bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat)) :
    E.ncard = (y.edge s t).toNat := by
  have he := cross_family_edge_count h s t E hE
  omega

/-- In particular a concrete original internal family realizes that exact count. -/
theorem internal_component_exists {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) (s : Universal.History (n+1)) :
    ∃ G ∈ graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat),
      G.edgeFinset.card = (y.edge s s / 2).toNat := by
  obtain ⟨G,hG⟩ := internal_family_nonempty σ s
  exact ⟨G,hG,internal_family_edge_count h s G hG⟩

theorem cross_component_exists {p : ℝ} {σ : State V n} {y : CoarseData V n}
    (h : CoarseKernel.rho p σ = y) (s t : Universal.History (n+1)) :
    ∃ E ∈ bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat), (E.ncard : ℤ) = y.edge s t := by
  obtain ⟨E,hE⟩ := cross_family_nonempty σ s t
  exact ⟨E,hE,cross_family_edge_count h s t E hE⟩

end MajorityDynamics.GraphProcess.KernelInputs
