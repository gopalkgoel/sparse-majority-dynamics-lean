import MajorityDynamics.Literature.FKMFormal.Graph
import MajorityDynamics.Probability.RandomGraph.Basic
import MajorityDynamics.Probability.FixedDegreeSampling.Basic

/-! Identification of the supplied finite Bernoulli weights with Mathlib's
actual Erdős–Rényi law, including the degenerate endpoint p = 1. -/
noncomputable section
open Finset MeasureTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Literature.FKMAdapters
open MajorityDynamics.Paper

variable {n : ℕ}

def encode (G : Graph n) : MD.Edge n → Bool := fun e => decide (e.val ∈ G.edgeSet)

def decode (y : MD.Edge n → Bool) : Graph n :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬ e.IsDiag, y ⟨e,h⟩ = true}

@[simp] theorem mem_decode (y : MD.Edge n → Bool) (e : MD.Edge n) :
    e.val ∈ (decode y).edgeSet ↔ y e = true := by
  simp [decode, SimpleGraph.edgeSet_fromEdgeSet, e.property]

@[simp] theorem encode_decode (y : MD.Edge n → Bool) : encode (decode y) = y := by
  funext e
  simp [encode]

@[simp] theorem decode_encode (G : Graph n) : decode (encode G) = G := by
  apply SimpleGraph.edgeSet_injective
  ext e
  simp only [decode, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq,
    encode, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨_, h⟩, _⟩; exact h
  · intro h
    have he := G.edgeSet_subset_compl_diagSet h
    exact ⟨⟨he,h⟩,he⟩

def graphEquiv : (MD.Edge n → Bool) ≃ Graph n where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

def sampleGraph (x : MD.Ω n) : Graph n := decode (fun e => x (.inr e))

@[simp] theorem sampleGraph_adj (x : MD.Ω n) (u v : Fin n) :
    (sampleGraph x).Adj u v ↔ MD.adj x u v := by
  by_cases h : u = v
  · subst v; simp [MD.adj]
  · simp [sampleGraph, decode, SimpleGraph.fromEdgeSet_adj, MD.adj, MD.edge, h,
      Sym2.mk_isDiag_iff]

/-- Summing out the unused initial-opinion coordinates costs no conditioning factor. -/
theorem marginal (p : ℝ) (F : (MD.Edge n → Bool) → ℝ) :
    MD.E (MD.q n p) (fun x => F (fun e => x (.inr e))) =
      ∑ y, MD.wt (fun _ : MD.Edge n => p) y * F y := by
  unfold MD.E
  rw [← (Equiv.sumArrowEquivProdArrow (Fin n) (MD.Edge n) Bool).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin n → Bool, ∑ y : MD.Edge n → Bool,
    MD.wt (MD.q n p) (Sum.elim a y) * F y) = _
  have hsplit (a : Fin n → Bool) (y : MD.Edge n → Bool) :
      MD.wt (MD.q n p) (Sum.elim a y) =
        MD.wt (fun _ : Fin n => (1/2 : ℝ)) a * MD.wt (fun _ : MD.Edge n => p) y :=
    Fintype.prod_sum_type _
  simp_rw [hsplit, mul_assoc, ← mul_sum]
  rw [← sum_mul, MD.sum_wt, one_mul]

lemma edge_card (G : Graph n) :
    (univ.filter fun e : MD.Edge n => encode G e = true).card = G.edgeSet.ncard := by
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun e _ => e.val)
  · intro e he
    simpa [encode] using he
  · intro e f _ _ h; exact Subtype.ext h
  · intro e he
    exact ⟨⟨e,G.edgeSet_subset_compl_diagSet he⟩, by simpa [encode] using he, rfl⟩

lemma card_edges : Fintype.card (MD.Edge n) = n.choose 2 := by
  change Fintype.card {e : Sym2 (Fin n) // ¬e.IsDiag} = n.choose 2
  convert Sym2.card_diagSet_compl (α := Fin n) using 1
  · exact Fintype.card_congr (Equiv.refl _)
  · simp

lemma singleton_weight (p : unitInterval) (G : Graph n) :
    graphLaw n p {G} = ENNReal.ofReal (MD.wt (fun _ : MD.Edge n => (p:ℝ)) (encode G)) := by
  rw [graphLaw, SimpleGraph.binomialRandom_singleton]
  have hc := edge_card G
  have hn : (univ.filter fun e : MD.Edge n => ¬ encode G e = true).card =
      n.choose 2 - G.edgeSet.ncard := by
    have h := card_filter_add_card_filter_not (s := univ) (fun e : MD.Edge n => encode G e = true)
    rw [hc, card_univ, card_edges] at h
    omega
  simp only [MD.wt, prod_ite, prod_const, hc, hn]
  rw [ENNReal.ofReal_mul (pow_nonneg p.property.1 _), ENNReal.ofReal_pow p.property.1,
    ENNReal.ofReal_pow (sub_nonneg.mpr p.property.2)]
  have hp : ENNReal.ofReal (p:ℝ) = (unitInterval.toNNReal p : ℝ≥0∞) := by
    exact ENNReal.ofReal_eq_coe_nnreal p.property.1
  have hq : ENNReal.ofReal (1-(p:ℝ)) = (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) := by
    rw [← unitInterval.coe_symm_eq]
    exact ENNReal.ofReal_eq_coe_nnreal (unitInterval.symm p).property.1
  rw [hp, hq]
  simp [Nat.card_eq_fintype_card]


/-- Exact equality of event probabilities, with no restriction p < 1. -/
theorem event_probability (p : unitInterval) (A : Set (Graph n)) :
    graphLaw n p A = ENNReal.ofReal (MD.Pr (MD.q n p) (fun x => sampleGraph x ∈ A)) := by
  unfold MD.Pr
  rw [show MD.E (MD.q n p) (fun x => if sampleGraph x ∈ A then (1:ℝ) else 0) =
      ∑ y, MD.wt (fun _ : MD.Edge n => (p:ℝ)) y * (if decode y ∈ A then 1 else 0) from
        marginal p (fun y => if decode y ∈ A then 1 else 0)]
  rw [← graphEquiv.symm.sum_comp]
  change graphLaw n p A = ENNReal.ofReal
    (∑ G : Graph n, MD.wt (fun _ : MD.Edge n => (p:ℝ)) (encode G) *
      (if decode (encode G) ∈ A then 1 else 0))
  simp only [decode_encode, mul_ite, mul_one, mul_zero, ← sum_filter]
  rw [ENNReal.ofReal_sum_of_nonneg (fun G _ => MD.wt_nonneg (fun _ => p.property) _)]
  simp_rw [← singleton_weight]
  rw [MeasureTheory.sum_measure_singleton]
  congr 1
  ext G
  simp

end MajorityDynamics.Literature.FKMAdapters
