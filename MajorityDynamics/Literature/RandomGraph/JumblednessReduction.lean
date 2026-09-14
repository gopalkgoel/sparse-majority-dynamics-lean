import MajorityDynamics.Literature.RandomGraph.OrderedPairs
import MajorityDynamics.Literature.RandomGraph.MaximumDegree

open Finset MajorityDynamics.Paper
noncomputable section
namespace MajorityDynamics.Literature.RandomGraph
attribute [local instance] Classical.propDecidable

lemma orderedEdgeCount_comm {N : ℕ} (G : Graph N) (U W : Finset (Fin N)) :
    orderedEdgeCount G U W = orderedEdgeCount G W U := by
  unfold orderedEdgeCount
  apply Finset.card_equiv (Equiv.prodComm _ _)
  intro x
  simp [and_comm, G.adj_comm]

lemma orderedEdgeCount_le_sum_degree {N : ℕ} (G : Graph N) (U W : Finset (Fin N)) :
    orderedEdgeCount G U W ≤ ∑ i ∈ U, G.degree i := by
  have he : orderedEdgeCount G U W = ∑ i ∈ U, (W.filter (G.Adj i)).card := by
    simp only [orderedEdgeCount, card_eq_sum_ones, sum_filter, sum_product]
  rw [he]
  apply sum_le_sum
  intro i _
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply card_le_card
  intro j hj
  exact (G.mem_neighborFinset i j).mpr (mem_filter.mp hj).2

lemma orderedEdgeCount_le_degreeBound {N : ℕ} (G : Graph N) (p : unitInterval)
    (hG : DegreeBound G p) (U W : Finset (Fin N)) :
    (orderedEdgeCount G U W : ℝ) ≤ 2 * ((p : ℝ) * N) * U.card := by
  have h := orderedEdgeCount_le_sum_degree G U W
  have hr : (orderedEdgeCount G U W : ℝ) ≤ ∑ i ∈ U, (G.degree i : ℝ) := by
    exact_mod_cast h
  have hs := sum_le_sum (s := U) (fun i _ => hG i)
  have hs' : (∑ i ∈ U, (G.degree i : ℝ)) ≤ U.card * (2 * (p : ℝ) * N) := by
    simpa using hs
  nlinarith

lemma ordered_discrepancy_unbalanced {N : ℕ} (G : Graph N) (p : unitInterval)
    (hG : DegreeBound G p) (U W : Finset (Fin N))
    (hlarge : (p : ℝ) * N * U.card ≤ W.card) :
    |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card| ≤
      2 * Real.sqrt ((p : ℝ) * N * U.card * W.card) := by
  have hp0 := p.property.1
  let d : ℝ := (p : ℝ) * N
  let s : ℝ := Real.sqrt (d * U.card * W.card)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = d * U.card * W.card := Real.sq_sqrt (by positivity)
  have hu : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hdu : d * U.card ≤ s := by
    change d * U.card ≤ (W.card : ℝ) at hlarge
    nlinarith [mul_le_mul_of_nonneg_left hlarge (mul_nonneg hd hu)]
  have hW : (W.card : ℝ) ≤ N := by exact_mod_cast (show W.card ≤ N by simpa using card_le_univ W)
  have hmean : (p : ℝ) * U.card * W.card ≤ d * U.card := by
    dsimp [d]
    nlinarith [mul_le_mul_of_nonneg_left hW (mul_nonneg p.property.1 hu)]
  have he := orderedEdgeCount_le_degreeBound G p hG U W
  change (orderedEdgeCount G U W : ℝ) ≤ 2 * d * U.card at he
  change |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card| ≤ 2 * s
  apply abs_le.mpr
  constructor <;> nlinarith [show (0 : ℝ) ≤ orderedEdgeCount G U W by positivity,
    show 0 ≤ (p : ℝ) * U.card * W.card by positivity]

lemma ordered_discrepancy_empty {N : ℕ} (G : Graph N) (p : unitInterval)
    (U W : Finset (Fin N)) (h : U = ∅ ∨ W = ∅) :
    |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card| = 0 := by
  rcases h with rfl | rfl <;> simp [orderedEdgeCount]

lemma diagonal_bias_le_sqrt {N : ℕ} (p : unitInterval) (U W : Finset (Fin N))
    (hd : 1 ≤ (p : ℝ) * N) :
    (p : ℝ) * (U ∩ W).card ≤ Real.sqrt ((p : ℝ) * N * U.card * W.card) := by
  have hU : ((U ∩ W).card : ℝ) ≤ U.card := by exact_mod_cast card_le_card inter_subset_left
  have hW : ((U ∩ W).card : ℝ) ≤ W.card := by exact_mod_cast card_le_card inter_subset_right
  have hm : ((U ∩ W).card : ℝ) ^ 2 ≤ (U.card : ℝ) * W.card := by
    nlinarith [mul_le_mul hU hW (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hs := Real.sq_sqrt (show 0 ≤ (p : ℝ) * N * U.card * W.card by positivity)
  have hb := mul_le_mul_of_nonneg_right hd (show (0 : ℝ) ≤ U.card * W.card by positivity)
  have hp := p.property.2
  have hc : 0 ≤ ((U ∩ W).card : ℝ) := Nat.cast_nonneg _
  have hpc : (p : ℝ) * (U ∩ W).card ≤ (U ∩ W).card := by nlinarith
  nlinarith [Real.sqrt_nonneg ((p : ℝ) * N * U.card * W.card)]

end MajorityDynamics.Literature.RandomGraph
