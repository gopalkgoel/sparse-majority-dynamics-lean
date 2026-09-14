import MajorityDynamics.Literature.RandomGraph.EdgeTails
import MajorityDynamics.Literature.RandomGraph.JumblednessReduction

noncomputable section
open MeasureTheory ProbabilityTheory
open MajorityDynamics.Paper
open scoped unitInterval

namespace MajorityDynamics.Literature.RandomGraph
attribute [local instance] Classical.propDecidable

lemma pair_failure_balanced {N : ℕ} (U W : Finset (Fin N))
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hu : 0 < U.card) (hw : 0 < W.card)
    (hd : 1 ≤ (p : ℝ) * N) (hbal : (W.card : ℝ) ≤ (p : ℝ) * N * U.card) :
    graphLaw N p {G | 256 * Real.sqrt ((p : ℝ) * N * U.card * W.card) <
        |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card|} ≤
      ENNReal.ofReal (4 * Real.exp (-8 * subsetEntropy N W.card)) := by
  let s : ℝ := Real.sqrt ((p : ℝ) * N * U.card * W.card)
  let μ₁ : ℝ := ((lowerEdges U W).card : ℝ) * p
  let μ₂ : ℝ := ((lowerEdges W U).card : ℝ) * p
  let A : Set (Graph N) := {G | μ₁ + 48 * s ≤ (edgeCount (lowerEdges U W) G : ℝ)}
  let B : Set (Graph N) := {G | μ₂ + 48 * s ≤ (edgeCount (lowerEdges W U) G : ℝ)}
  let C : Set (Graph N) := {G | (edgeCount (lowerEdges U W) G : ℝ) ≤ μ₁ - 48 * s}
  let D : Set (Graph N) := {G | (edgeCount (lowerEdges W U) G : ℝ) ≤ μ₂ - 48 * s}
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hdiag := diagonal_bias_le_sqrt p U W hd
  change (p : ℝ) * (U ∩ W).card ≤ s at hdiag
  have hmean : μ₁ + μ₂ + (p : ℝ) * (U ∩ W).card = (p : ℝ) * U.card * W.card := by
    have hc : ((lowerEdges U W).card : ℝ) + (lowerEdges W U).card + (U ∩ W).card =
        (U.card : ℝ) * W.card := by exact_mod_cast card_lowerEdges_add U W
    dsimp [μ₁, μ₂]
    nlinarith
  have hcover : {G : Graph N | 256 * s <
      |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card|} ⊆ A ∪ B ∪ C ∪ D := by
    intro G hG
    by_contra hn
    simp only [Set.mem_union, not_or, A, B, C, D, Set.mem_ofPred_eq, not_le] at hn
    have hc : (orderedEdgeCount G U W : ℝ) =
        (edgeCount (lowerEdges U W) G : ℝ) + (edgeCount (lowerEdges W U) G : ℝ) := by
      exact_mod_cast orderedEdgeCount_split U W G
    change 256 * s < |(orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card| at hG
    rcases lt_or_ge ((orderedEdgeCount G U W : ℝ) - (p : ℝ) * U.card * W.card) 0 with hsign | hsign
    · rw [abs_of_neg hsign] at hG
      linarith [hn.1.2, hn.2]
    · rw [abs_of_nonneg hsign] at hG
      linarith [hn.1.1.1, hn.1.1.2, mul_nonneg p.property.1 (Nat.cast_nonneg (U ∩ W).card)]
  have hcard₂ : (lowerEdges W U).card ≤ U.card * W.card := by
    simpa [Nat.mul_comm] using card_lowerEdges_le W U
  have hA := edgeFamily_upper_entropy U W (lowerEdges U W) (lowerEdges_subset U W)
    (card_lowerEdges_le U W) p hp hu hw hbal 48 (by norm_num)
  have hB := edgeFamily_upper_entropy U W (lowerEdges W U) (lowerEdges_subset W U)
    hcard₂ p hp hu hw hbal 48 (by norm_num)
  have hC := edgeFamily_lower_entropy U W (lowerEdges U W) (lowerEdges_subset U W)
    (card_lowerEdges_le U W) p hp hu hw 48 (by norm_num)
  have hD := edgeFamily_lower_entropy U W (lowerEdges W U) (lowerEdges_subset W U)
    hcard₂ p hp hu hw 48 (by norm_num)
  norm_num only [show (48 : ℝ) / 6 = 8 by norm_num] at hA hB
  have hsum := (measure_union_le (A ∪ B ∪ C) D).trans
    (add_le_add ((measure_union_le (A ∪ B) C).trans
      (add_le_add ((measure_union_le A B).trans (add_le_add hA hB)) hC)) hD)
  refine (measure_mono hcover).trans (hsum.trans ?_)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num only [ENNReal.ofReal_ofNat]
  simp only [neg_mul] 
  ring_nf
  exact le_rfl

end MajorityDynamics.Literature.RandomGraph
