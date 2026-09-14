import MajorityDynamics.Literature.RandomGraph.SubsetCounting
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Finset.Powerset

/-! Finite union bounds over all pairs of nonempty vertex subsets, grouped by
their two cardinalities. Intersecting subsets are included. -/

namespace MajorityDynamics.Literature.RandomGraph
open Finset MeasureTheory
open scoped ENNReal

lemma choose_pair_entropy_product {N u w : ℕ}
    (hu : 0 < u) (hw : 0 < w) (huN : u ≤ N) (hwN : w ≤ N)
    {A : ℝ} (hA : 0 ≤ A) :
    (N.choose u : ℝ) * (N.choose w : ℝ) *
        (A * Real.exp (-8 * subsetEntropy N (↑(max u w : ℕ)))) ≤
      A * Real.exp (-6 * Real.log N) := by
  have hcount : (N.choose u : ℝ) * (N.choose w : ℝ) ≤
      Real.exp (2 * subsetEntropy N (↑(max u w : ℕ))) := by
    rcases le_total u w with h | h
    · simpa [max_eq_right h, subsetEntropy, mul_assoc] using
        choose_mul_choose_le_exp_entropy hu h hwN
    · rw [max_eq_left h, mul_comm (N.choose u : ℝ)]
      simpa [subsetEntropy, mul_assoc] using choose_mul_choose_le_exp_entropy hw h huN
  have hlog : Real.log (N : ℝ) ≤ subsetEntropy N (↑(max u w : ℕ)) :=
    log_le_subsetEntropy (by exact_mod_cast (show 1 ≤ max u w by omega))
      (by exact_mod_cast (max_le huN hwN))
  calc
    _ ≤ Real.exp (2 * subsetEntropy N (↑(max u w : ℕ))) *
        (A * Real.exp (-8 * subsetEntropy N (↑(max u w : ℕ)))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = A * Real.exp (-6 * subsetEntropy N (↑(max u w : ℕ))) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA

lemma measure_subset_pairs_fixed_size_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {N : ℕ} (bad : Finset (Fin N) → Finset (Fin N) → Set Ω)
    {A : ℝ} (hA : 0 ≤ A)
    (hpair : ∀ U W, U.Nonempty → W.Nonempty →
      μ (bad U W) ≤ ENNReal.ofReal (A *
        Real.exp (-8 * subsetEntropy N (↑(max U.card W.card : ℕ)))))
    {u w : ℕ} (hu : 0 < u) (hw : 0 < w) (huN : u ≤ N) (hwN : w ≤ N) :
    μ (⋃ U ∈ (univ : Finset (Fin N)).powersetCard u, ⋃ W ∈ (univ : Finset (Fin N)).powersetCard w, bad U W) ≤
      ENNReal.ofReal (A * Real.exp (-6 * Real.log N)) := by
  have hsum : μ (⋃ U ∈ (univ : Finset (Fin N)).powersetCard u, ⋃ W ∈ (univ : Finset (Fin N)).powersetCard w, bad U W) ≤
      ∑ U ∈ (univ : Finset (Fin N)).powersetCard u, ∑ W ∈ (univ : Finset (Fin N)).powersetCard w,
        ENNReal.ofReal (A * Real.exp (-8 * subsetEntropy N (↑(max u w : ℕ)))) := by
    refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun U hU => ?_)
    refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun W hW => ?_)
    have hUc : U.card = u := (mem_powersetCard.mp hU).2
    have hWc : W.card = w := (mem_powersetCard.mp hW).2
    simpa only [hUc, hWc] using hpair U W
      (card_pos.mp (hUc.symm ▸ hu)) (card_pos.mp (hWc.symm ▸ hw))
  simp only [sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ N.choose w),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ N.choose u)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using choose_pair_entropy_product hu hw huN hwN hA

/-- A fixed-pair exponential bound gives a bound for all subset pairs. The
cardinality grouping costs at most `N²`; no disjointness or symmetry of the
two subsets is assumed. Events involving an empty subset must be empty. -/
theorem measure_subset_pairs_union_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {N : ℕ} (bad : Finset (Fin N) → Finset (Fin N) → Set Ω)
    {A : ℝ} (hA : 0 ≤ A)
    (hempty_left : ∀ W, bad ∅ W = ∅) (hempty_right : ∀ U, bad U ∅ = ∅)
    (hpair : ∀ U W, U.Nonempty → W.Nonempty →
      μ (bad U W) ≤ ENNReal.ofReal (A *
        Real.exp (-8 * subsetEntropy N (↑(max U.card W.card : ℕ))))) :
    μ (⋃ U, ⋃ W, bad U W) ≤
      ENNReal.ofReal (A * (N : ℝ) ^ 2 * Real.exp (-6 * Real.log N)) := by
  classical
  have hcover : (⋃ U, ⋃ W, bad U W) ⊆
      ⋃ u ∈ Icc 1 N, ⋃ w ∈ Icc 1 N,
        ⋃ U ∈ (univ : Finset (Fin N)).powersetCard u,
          ⋃ W ∈ (univ : Finset (Fin N)).powersetCard w, bad U W := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨U, W, hx⟩ := hx
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simp [hempty_left] at hx
    rcases W.eq_empty_or_nonempty with rfl | hW
    · simp [hempty_right] at hx
    refine ⟨U.card, ?_, W.card, ?_, U, ?_, W, ?_, hx⟩
    · exact mem_Icc.mpr ⟨hU.card_pos, by simpa using card_le_univ U⟩
    · exact mem_Icc.mpr ⟨hW.card_pos, by simpa using card_le_univ W⟩
    · simp
    · simp
  have hsum : μ (⋃ u ∈ Icc 1 N, ⋃ w ∈ Icc 1 N,
        ⋃ U ∈ (univ : Finset (Fin N)).powersetCard u,
          ⋃ W ∈ (univ : Finset (Fin N)).powersetCard w, bad U W) ≤
      ∑ u ∈ Icc 1 N, ∑ w ∈ Icc 1 N,
        ENNReal.ofReal (A * Real.exp (-6 * Real.log N)) := by
    refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun u hu => ?_)
    refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun w hw => ?_)
    exact measure_subset_pairs_fixed_size_le μ bad hA hpair
      (mem_Icc.mp hu).1 (mem_Icc.mp hw).1 (mem_Icc.mp hu).2 (mem_Icc.mp hw).2
  refine (measure_mono hcover).trans (hsum.trans ?_)
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  apply le_of_eq
  congr 1
  ring

end MajorityDynamics.Literature.RandomGraph
