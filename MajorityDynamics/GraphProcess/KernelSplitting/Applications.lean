import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Inputs
import MajorityDynamics.Probability.NeighborhoodTail.CarrierMain

/-! The C.2 point estimates for the actual internal and cross component laws.
Every capacity, sum, size and normalized degree input is derived from the actual
state and its already verified original parameter regime. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting
open Universal BlockDecomposition KernelInputs
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Probability.NeighborhoodTail
variable {V : Type*} [Fintype V] {n : ℕ}

/-- An actual internal component satisfies the C.2 point bound at every integer
value outside the unchanged global regularity window. -/
theorem internal_point_tail {θ T φ p U c : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ)
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
theorem bipartite_point_tail {θ T φ p U c : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ)
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

end MajorityDynamics.GraphProcess.KernelSplitting
