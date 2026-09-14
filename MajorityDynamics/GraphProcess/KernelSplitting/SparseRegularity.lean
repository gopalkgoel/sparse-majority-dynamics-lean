import MajorityDynamics.GraphProcess.KernelSplitting.Main
import MajorityDynamics.GraphProcess.KernelInputs.Sparse
import MajorityDynamics.Probability.NeighborhoodTail.Sparse

/-! Closed actual next-degree regularity on the uniform sparse range. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting
open Universal BlockDecomposition FineKernel KernelInputs
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Probability.NeighborhoodTail
open MajorityDynamics.Combinatorics.DegreeRatios
variable {V : Type*} [Fintype V] {n : ℕ}
universe u

theorem internal_point_tail_sparse {θ T φ p U c : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : SparseVerified θ T φ p U y σ)
    (hρ : CoarseKernel.rho p σ = y) (hc : 0 < c) (s : History (n+1))
    (hC : GraphCarrierConclusion c U (Block σ.part s) p)
    (v : Block σ.part s) (b : Bool) (a : ℤ) (ha : 0 ≤ a)
    (had : a ≤ σ.deg v s)
    (hbad : (p*Fintype.card V)^((4:ℝ)/7) <
      |(a : ℝ)-p*(child σ s b).card|) :
    (fixedDegreeLaw (fun w : Block σ.part s => (σ.deg w s).toNat)).real
      {G | ((G.neighborFinset v ∩ childInBlock σ s b).card : ℤ) = a} ≤
      Real.exp (-c*(p*Fintype.card V)^((1:ℝ)/7)) := by
  obtain ⟨G,hG⟩ := internal_family_nonempty σ s
  have hcap : ∀ w : Block σ.part s,
      ((σ.deg w s).toNat : ℤ) ≤ (Fintype.card (Block σ.part s) : ℤ)-1 := by
    intro w
    have hb := G.degree_lt_card_verts w
    rw [show G.degree w = (σ.deg w s).toNat from hG w] at hb
    omega
  have hsum : (∑ w : Block σ.part s, ((σ.deg w s).toNat : ℤ)) =
      2 * ((y.edge s s / 2).toNat : ℤ) := by
    rw [← Nat.cast_sum, KernelEdgeSplitting.block_degree_total hρ,
      cross_total_nat, internal_total_half]
  have hcount : |(((y.edge s s / 2).toNat : ℤ) : ℝ) -
      p * Fintype.card (Block σ.part s) *
        ((Fintype.card (Block σ.part s) : ℝ)-1)/2| ≤
      U*(Fintype.card (Block σ.part s) : ℝ)^2*p /
        Real.sqrt (p*Fintype.card (Block σ.part s)) := by
    simpa only [Int.cast_natCast, block_card hρ] using h.internal_count s
  have hdeg : ∀ w : Block σ.part s,
      |(((σ.deg w s).toNat : ℝ) - p*Fintype.card (Block σ.part s)) /
        Real.sqrt (p*Fintype.card (Block σ.part s))| ≤
      Real.log (Fintype.card (Block σ.part s)) := by
    intro w
    simpa only [degree_cast_real, block_card hρ] using h.normalized_window w s s
  have hS : (Fintype.card (Block σ.part s) : ℝ)/U ≤
      (childInBlock σ s b).card := by
    simpa only [block_card hρ, childInBlock_card, inv_mul_eq_div] using
      (h.subset_sizes s s b).1
  have hSc : (Fintype.card (Block σ.part s) : ℝ)/U ≤
      (Fintype.card (Block σ.part s) : ℝ)-(childInBlock σ s b).card := by
    simpa only [block_card hρ, childInBlock_card, inv_mul_eq_div] using
      (h.subset_sizes s s b).2
  have ht := h.tail_threshold s s b a hbad
  have hτ : Real.log (Fintype.card (Block σ.part s) : ℝ)^100 ≤
      |((a : ℝ)-p*(childInBlock σ s b).card) /
        Real.sqrt (p*(childInBlock σ s b).card)| := by
    simpa only [block_card hρ, childInBlock_card] using ht.1.trans ht.2
  have hh := (hC ((y.edge s s / 2).toNat : ℤ)
    (fun w : Block σ.part s => (σ.deg w s).toNat) hcap hsum hcount hdeg).2
    v (childInBlock σ s b) hS hSc a ha
    (by simpa only [state_degree_toNat_cast] using had) hτ
  rw [childInBlock_card] at hh
  convert hh.trans (kappa_tail_exp_le h.p_pos (h.child_sizes s b).2.2
    (h.child_sizes s b).2.1 hc.le hbad) using 1
  congr 1
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq]
  apply iff_of_eq
  congr 3
  ext w
  simp only [Finset.mem_inter]

/-- The cross component uses its opposite block as the population and retains
both distinct square-root normalizations in the C.2 degree hypotheses. -/
theorem bipartite_point_tail_sparse {θ T φ p U c : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : SparseVerified θ T φ p U y σ)
    (hρ : CoarseKernel.rho p σ = y) (hc : 0 < c) (s t : History (n+1))
    (hC : BipartiteCarrierConclusion c U (Block σ.part s) (Block σ.part t) p)
    (v : Block σ.part s) (b : Bool) (a : ℤ) (ha : 0 ≤ a)
    (had : a ≤ σ.deg v t)
    (hbad : (p*Fintype.card V)^((4:ℝ)/7) <
      |(a : ℝ)-p*(child σ t b).card|) :
    (bipartiteFixedDegreeLaw
      (fun w : Block σ.part s => (σ.deg w t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat)).real
      {E | ((leftNeighbors E v ∩ childInBlock σ t b).card : ℤ) = a} ≤
      Real.exp (-c*(p*Fintype.card V)^((1:ℝ)/7)) := by
  obtain ⟨E,hE⟩ := cross_family_nonempty σ s t
  have hsizeLo : (Fintype.card (Block σ.part t) : ℝ)/U ≤
      Fintype.card (Block σ.part s) := by
    simpa only [block_card hρ, inv_mul_eq_div] using (h.relative_sizes s t).1
  have hsizeHi : (Fintype.card (Block σ.part s) : ℝ) ≤
      U*Fintype.card (Block σ.part t) := by
    simpa only [block_card hρ] using (h.relative_sizes s t).2
  have hleftcap : ∀ w : Block σ.part s,
      (σ.deg w t).toNat ≤ Fintype.card (Block σ.part t) := by
    intro w
    rw [← show leftDegree E w = (σ.deg w t).toNat from hE.1 w, leftDegree]
    exact Finset.card_le_univ _
  have hrightcap : ∀ w : Block σ.part t,
      (σ.deg w s).toNat ≤ Fintype.card (Block σ.part s) := by
    intro w
    rw [← show rightDegree E w = (σ.deg w s).toNat from hE.2 w, rightDegree]
    exact Finset.card_le_univ _
  have hleftsum : (∑ w : Block σ.part s, ((σ.deg w t).toNat : ℤ)) =
      y.edge s t := by
    rw [← Nat.cast_sum, KernelEdgeSplitting.block_degree_total hρ, cross_total_nat]
  have hrightsum : (∑ w : Block σ.part t, ((σ.deg w s).toNat : ℤ)) =
      y.edge s t := by
    rw [← Nat.cast_sum, KernelEdgeSplitting.block_degree_total hρ,
      cross_total_nat, y.edge_symm t s]
  have hcount : |(y.edge s t : ℝ) - p*Fintype.card (Block σ.part s)*
      Fintype.card (Block σ.part t)| ≤
      U*(Fintype.card (Block σ.part t) : ℝ)^2*p /
        Real.sqrt (p*Fintype.card (Block σ.part t)) := by
    simpa only [block_card hρ] using h.cross_count s t
  have hleftdeg : ∀ w : Block σ.part s,
      |(((σ.deg w t).toNat : ℝ)-p*Fintype.card (Block σ.part t)) /
        Real.sqrt (p*Fintype.card (Block σ.part t))| ≤
      Real.log (Fintype.card (Block σ.part t)) := by
    intro w
    simpa only [degree_cast_real, block_card hρ] using h.normalized_window w t t
  have hrightdeg : ∀ w : Block σ.part t,
      |(((σ.deg w s).toNat : ℝ)-p*Fintype.card (Block σ.part s)) /
        Real.sqrt (p*Fintype.card (Block σ.part s))| ≤
      Real.log (Fintype.card (Block σ.part t)) := by
    intro w
    simpa only [degree_cast_real, block_card hρ] using h.normalized_window w s t
  have hS : (Fintype.card (Block σ.part t) : ℝ)/U ≤
      (childInBlock σ t b).card := by
    simpa only [block_card hρ, childInBlock_card, inv_mul_eq_div] using
      (h.subset_sizes t t b).1
  have hSc : (Fintype.card (Block σ.part t) : ℝ)/U ≤
      (Fintype.card (Block σ.part t) : ℝ)-(childInBlock σ t b).card := by
    simpa only [block_card hρ, childInBlock_card, inv_mul_eq_div] using
      (h.subset_sizes t t b).2
  have ht := h.tail_threshold t t b a hbad
  have hτ : Real.log (Fintype.card (Block σ.part t) : ℝ)^100 ≤
      |((a : ℝ)-p*(childInBlock σ t b).card) /
        Real.sqrt (p*(childInBlock σ t b).card)| := by
    simpa only [block_card hρ, childInBlock_card] using ht.1.trans ht.2
  have hh := (hC hsizeLo hsizeHi (y.edge s t)
    (fun w : Block σ.part s => (σ.deg w t).toNat)
    (fun w : Block σ.part t => (σ.deg w s).toNat)
    hleftcap hrightcap hleftsum hrightsum hcount hleftdeg hrightdeg).2
    v (childInBlock σ t b) hS hSc a ha
    (by simpa only [state_degree_toNat_cast] using had) hτ
  rw [childInBlock_card] at hh
  convert hh.trans (kappa_tail_exp_le h.p_pos (h.child_sizes t b).2.2
    (h.child_sizes t b).2.1 hc.le hbad) using 1
  congr 1
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq]
  apply iff_of_eq
  congr 3
  ext w
  simp only [Finset.mem_inter]


theorem sampled_point_tail_sparse {V : Type u} [Fintype V] {n : ℕ}
    {θ T φ p U c : ℝ} {y : Local.CoarseData V n} {σ : FineState.State V n}
    (h : SparseVerified θ T φ p U y σ) (hρ : CoarseKernel.rho p σ = y) (hc : 0 < c)
    (hg : ∀ s, GraphCarrierConclusion c U (Block σ.part s) p)
    (hb : ∀ s t, BipartiteCarrierConclusion c U (Block σ.part s) (Block σ.part t) p)
    (v : V) (t : History (n+1)) (b : Bool) (a : ℤ)
    (ha : 0 ≤ a) (had : a ≤ σ.deg v t)
    (hbad : (p*Fintype.card V)^((4:ℝ)/7) < |(a:ℝ)-p*(child σ t b).card|) :
    (componentLaw σ).real {F | (sampleNext σ F).deg v (append t b) = a} ≤
      Real.exp (-c*(p*Fintype.card V)^((1:ℝ)/7)) := by
  let x : Block σ.part (σ.part v) := ⟨v,rfl⟩
  by_cases hst : σ.part v = t
  · subst t
    change (componentLaw σ).real {F | (sampleNext σ F).deg x (append (σ.part v) b) = a} ≤ _
    rw [internal_degree_real σ (σ.part v) x b a]
    exact internal_point_tail_sparse h hρ hc (σ.part v) (hg _) x b a ha had hbad
  · change (componentLaw σ).real {F | (sampleNext σ F).deg x (append t b) = a} ≤ _
    rw [cross_degree_real σ (σ.part v) t hst x b a]
    exact bipartite_point_tail_sparse h hρ hc (σ.part v) t (hb _ _) x b a ha had hbad

/-- S2 has uniformly superpolynomially small failure probability from original
local admissibility, rho-fiber equality and R1/R2 only. The threshold precedes
all varying carriers, densities, coarse data, tilts and actual fine states. -/
theorem uniform_regularity_failure_sparse {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      (K σ).real {τ | ¬ CoarseKernel.Regular p τ.part τ.deg} ≤ (N:ℝ)^(-A) := by
  obtain ⟨U,hU,N₁,h₁⟩ := uniform_inputs_sparse.{u} n hθlo hθhi hT hφ hφ1 hCf
  obtain ⟨c,r₀,hc,_hr₀,hg,hb⟩ := carrier_neighborhood_tail_sparse.{u,u,u} θ U hθlo hθhi hU
  obtain ⟨N₂,h₂⟩ := KernelEdgeSplitting.Numerics.uniform_block_log hT r₀
  obtain ⟨N₃,h₃⟩ := Numerics.union_absorption_sparse n hθlo hθhi hT hc hA
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have hn1 := ((le_max_left N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn2 := ((le_max_right N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn3 := (le_max_right (max N₁ N₂) N₃).trans hN
  have h := h₁ N hn1 V hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have hs (s : History (n+1)) : r₀ ≤ Fintype.card (Block σ.part s) := by
    rw [block_card hρ]
    exact (h₂ N hn2 (y.sizes s)
      (by simpa only [hcard] using (h.parent_sizes s).1)
      (by simpa only [hcard] using (h.parent_sizes s).2.1)).1
  have hd (s : History (n+1)) : SparseDensityWindow θ U (Fintype.card (Block σ.part s)) p := by
    simpa only [SparseDensityWindow, block_card hρ] using h.density s
  have hg' (s : History (n+1)) : GraphCarrierConclusion c U (Block σ.part s) p :=
    (hg (Block σ.part s) (hs s) p (hd s)).2.2
  have hb' (s t : History (n+1)) :
      BipartiteCarrierConclusion c U (Block σ.part s) (Block σ.part t) p :=
    (hb (Block σ.part s) (Block σ.part t) (hs t) p (hd t)).2.2
  have hp := K_regularity_failure_le σ p
    (Real.exp (-c*(p*Fintype.card V)^((1:ℝ)/7))) (Real.exp_nonneg _)
    (sampled_point_tail_sparse h hρ hc hg' hb')
  rw [hcard] at hp
  exact hp.trans (h₃ N hn3 p hlo hhi)



end MajorityDynamics.GraphProcess.KernelSplitting

