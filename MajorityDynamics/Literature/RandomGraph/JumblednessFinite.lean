import MajorityDynamics.Literature.RandomGraph.PairTails
import MajorityDynamics.Literature.RandomGraph.SubsetUnion
import MajorityDynamics.Literature.RandomGraph.JumblednessLimit

noncomputable section
open Finset MeasureTheory MajorityDynamics.Paper
namespace MajorityDynamics.Literature.RandomGraph
attribute [local instance] Classical.propDecidable

def pairBad {N : ℕ} (p : unitInterval) (U W : Finset (Fin N)) : Set (Graph N) :=
  {G | DegreeBound G p ∧ 256 * Real.sqrt ((p : ℝ) * N * U.card * W.card) <
    |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card|}

lemma pairBad_comm {N : ℕ} (p : unitInterval) (U W : Finset (Fin N)) :
    pairBad p U W = pairBad p W U := by
  ext G
  have hs : (p : ℝ) * N * U.card * W.card = (p : ℝ) * N * W.card * U.card := by ring
  have hm : (p : ℝ) * U.card * W.card = (p : ℝ) * W.card * U.card := by ring
  simp only [pairBad, Set.mem_ofPred_eq, hs, hm, orderedEdgeCount_comm G U W]

lemma pairBad_empty_left {N : ℕ} (p : unitInterval) (W : Finset (Fin N)) :
    pairBad p ∅ W = ∅ := by ext G; simp [pairBad, orderedEdgeCount]

lemma pairBad_empty_right {N : ℕ} (p : unitInterval) (U : Finset (Fin N)) :
    pairBad p U ∅ = ∅ := by rw [pairBad_comm]; exact pairBad_empty_left p U

lemma pairBad_bound_sorted {N : ℕ} (p : unitInterval) (hp : 0 < (p : ℝ))
    (hd : 1 ≤ (p : ℝ) * N) (U W : Finset (Fin N))
    (hU : U.Nonempty) (hW : W.Nonempty) :
    graphLaw N p (pairBad p U W) ≤
      ENNReal.ofReal (4 * Real.exp (-8 * subsetEntropy N W.card)) := by
  by_cases hbal : (W.card : ℝ) ≤ (p : ℝ) * N * U.card
  · refine (measure_mono (show pairBad p U W ⊆
        {G | 256 * Real.sqrt ((p : ℝ) * N * U.card * W.card) <
          |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card|}
        from fun _ h => h.2)).trans ?_
    exact pair_failure_balanced U W p hp hU.card_pos hW.card_pos hd hbal
  · have he : pairBad p U W = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro G hG
      have hb := ordered_discrepancy_unbalanced G p hG.1 U W (le_of_not_ge hbal)
      have hs := Real.sqrt_nonneg ((p : ℝ) * N * U.card * W.card)
      have hf := hG.2
      linarith
    rw [he, measure_empty]
    exact zero_le

lemma pairBad_bound {N : ℕ} (p : unitInterval) (hp : 0 < (p : ℝ))
    (hd : 1 ≤ (p : ℝ) * N) (U W : Finset (Fin N))
    (hU : U.Nonempty) (hW : W.Nonempty) :
    graphLaw N p (pairBad p U W) ≤ ENNReal.ofReal
      (4 * Real.exp (-8 * subsetEntropy N (↑(max U.card W.card : ℕ)))) := by
  rcases le_total U.card W.card with h | h
  · simpa only [max_eq_right h] using pairBad_bound_sorted p hp hd U W hU hW
  · rw [max_eq_left h, pairBad_comm]
    exact pairBad_bound_sorted p hp hd W U hW hU

lemma discrepancy_scale {N : ℕ} (p : unitInterval) (U W : Finset (Fin N)) :
    (256 * Real.sqrt ((p : ℝ) * N)) * Real.sqrt ((U.card : ℝ) * W.card) =
      256 * Real.sqrt ((p : ℝ) * N * U.card * W.card) := by
  rw [show (p : ℝ) * N * U.card * W.card =
    ((p : ℝ) * N) * ((U.card : ℝ) * W.card) by ring,
    Real.sqrt_mul (mul_nonneg p.property.1 (Nat.cast_nonneg N))]
  ring

/-- Finite failure estimate, uniform over the density parameter. -/
theorem jumbledness_failure_le {N : ℕ} (hN : 2 ≤ N) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hd : 1 ≤ (p : ℝ) * N) :
    graphLaw N p {G | Jumbled G p (256 * Real.sqrt ((p : ℝ) * N))}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) * Real.exp (-((p : ℝ) * N) / 3) +
        4 * (N : ℝ) ^ 2 * Real.exp (-6 * Real.log (N : ℝ))) := by
  have hcover : {G : Graph N | Jumbled G p (256 * Real.sqrt ((p : ℝ) * N))}ᶜ ⊆
      {G | DegreeBound G p}ᶜ ∪ ⋃ U, ⋃ W, pairBad p U W := by
    intro G hG
    by_cases hg : DegreeBound G p
    · apply Or.inr
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Jumbled, not_forall, not_le] at hG
      obtain ⟨U, W, hfail⟩ := hG
      rw [discrepancy_scale] at hfail
      exact Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨W, hg, hfail⟩⟩
    · exact Or.inl hg
  refine (measure_mono hcover).trans ((measure_union_le _ _).trans ?_)
  have hdeg := maximumDegree_failure hN p hp
  have hpairs := measure_subset_pairs_union_le (graphLaw N p) (pairBad p)
    (by norm_num : (0 : ℝ) ≤ 4) (pairBad_empty_left p) (pairBad_empty_right p)
    (pairBad_bound p hp hd)
  refine (add_le_add hdeg hpairs).trans_eq ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]

end MajorityDynamics.Literature.RandomGraph
