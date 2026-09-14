import MajorityDynamics.Probability.RandomOpinionsReduction.Law
import MajorityDynamics.Probability.RandomOpinionsReduction.AntiConcentration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.RandomOpinionsReduction

theorem plusCount_le {N : ℕ} (c : Paper.Coloring N) : Paper.plusCount c ≤ N := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin N)

theorem plusCount_real_probability (N a : ℕ) :
    (uniformColoringLaw N).real {c | Paper.plusCount c = a} =
      (N.choose a : ℝ) / (2 : ℝ)^N := by
  simp [measureReal_def, plusCount_probability]

theorem card_small_interval (S : Finset ℕ) (x r : ℝ) (hr : 0 ≤ r)
    (hS : ∀ a ∈ S, |(a : ℝ) - x| < r) : (S.card : ℝ) ≤ 2*r+1 := by
  classical
  obtain h | h := S.eq_empty_or_nonempty
  · simp [h]; linarith
  have hlo := (abs_lt.mp (hS _ (S.min'_mem h))).1
  have hhi := (abs_lt.mp (hS _ (S.max'_mem h))).2
  have hle : S.min' h ≤ S.max' h := S.min'_le _ (S.max'_mem h)
  have hc : S.card ≤ S.max' h - S.min' h + 1 := by
    calc S.card ≤ (Finset.Icc (S.min' h) (S.max' h)).card := by
           apply Finset.card_le_card
           intro a ha
           exact Finset.mem_Icc.mpr ⟨S.min'_le a ha, S.le_max' a ha⟩
         _ = _ := by simp [Nat.card_Icc]; omega
  have hc' : (S.card : ℝ) ≤ (S.max' h : ℝ) - S.min' h + 1 := by
    exact_mod_cast hc
  linarith

theorem small_ball {N : ℕ} (hN : 0 < N) (x r : ℝ) (hr : 0 ≤ r) :
    (uniformColoringLaw N).real {c | |(Paper.plusCount c : ℝ) - x| < r} ≤
      (2*r+1) * (2 / Real.sqrt N) := by
  classical
  let S := (Finset.range (N+1)).filter (fun a : ℕ => |(a : ℝ)-x| < r)
  have he : {c : Paper.Coloring N | |(Paper.plusCount c : ℝ) - x| < r} =
      ⋃ a ∈ S, {c | Paper.plusCount c = a} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hc
      exact ⟨Paper.plusCount c, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (plusCount_le c)), hc⟩, rfl⟩
    · rintro ⟨a, ha, hca⟩
      simpa [hca] using (Finset.mem_filter.mp ha).2
  rw [he]
  calc
    _ ≤ ∑ a ∈ S, (uniformColoringLaw N).real {c | Paper.plusCount c = a} :=
      measureReal_biUnion_finset_le S _
    _ ≤ ∑ _a ∈ S, (2 / Real.sqrt (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [plusCount_real_probability]
      exact binomial_point_bound hN a
    _ = (S.card : ℝ) * (2 / Real.sqrt N) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (card_small_interval S x r hr (fun a ha => (Finset.mem_filter.mp ha).2)) (by positivity)

def plusBit (b : Bool) : ℝ := if b then 0 else 1

theorem plusCount_sum {N : ℕ} (c : Paper.Coloring N) :
    (Paper.plusCount c : ℝ) = ∑ v, plusBit (c v) := by
  classical
  simp only [Paper.plusCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro v _
  cases c v <;> simp [plusBit]

theorem fairBit_integral (f : Bool → ℝ) :
    ∫ b, f b ∂fairBitLaw = (f false + f true) / 2 := by
  rw [integral_fintype (Integrable.of_finite)]
  simp [measureReal_def, fairBitLaw_singleton]
  ring

theorem plusCount_mean (N : ℕ) :
    ∫ c, (Paper.plusCount c : ℝ) ∂uniformColoringLaw N = (N : ℝ)/2 := by
  simp_rw [plusCount_sum]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have h (v : Fin N) : ∫ c : Paper.Coloring N, plusBit (c v) ∂uniformColoringLaw N = 1/2 := by
    rw [uniformColoringLaw, integral_comp_eval (.of_discrete), fairBit_integral]
    norm_num [plusBit]
  simp_rw [h]
  simp
  ring

theorem plusCount_variance (N : ℕ) :
    variance (fun c => (Paper.plusCount c : ℝ)) (uniformColoringLaw N) = (N : ℝ)/4 := by
  have he : (fun c : Paper.Coloring N => (Paper.plusCount c : ℝ)) =
      ∑ v : Fin N, (fun c => plusBit (c v)) := by
    funext c
    simpa using plusCount_sum c
  rw [he, uniformColoringLaw, variance_sum_pi (fun _ => MemLp.of_discrete)]
  have hv : variance plusBit fairBitLaw = 1/4 := by
    rw [variance_eq_sub (MemLp.of_discrete), fairBit_integral, fairBit_integral]
    norm_num [plusBit]
  simp [hv]
  ring

theorem upper_tail {N : ℕ} (hN : 0 < N) {A : ℝ} (hA : 0 < A) :
    (uniformColoringLaw N).real {c | A * Real.sqrt N < |(Paper.plusCount c : ℝ) - (N : ℝ)/2|} ≤
      1 / (4 * A^2) := by
  have h := meas_ge_le_variance_div_sq (μ := uniformColoringLaw N)
    (X := fun c => (Paper.plusCount c : ℝ)) MemLp.of_discrete
    (show 0 < A * Real.sqrt N from mul_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN)))
  rw [plusCount_mean, plusCount_variance] at h
  have he : ((N : ℝ)/4) / (A*Real.sqrt N)^2 = 1/(4*A^2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [he] at h
  have h' := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal (by positivity)] at h'
  exact (measureReal_mono (μ := uniformColoringLaw N) (s₂ :=
    {c | A * Real.sqrt N ≤ |(Paper.plusCount c : ℝ) - (N : ℝ)/2|})
    (s₁ := {c | A * Real.sqrt N < |(Paper.plusCount c : ℝ) - (N : ℝ)/2|})
    (by intro c hc; exact le_of_lt (show A * Real.sqrt N <
      |(Paper.plusCount c : ℝ) - (N : ℝ)/2| from hc))).trans h'

end MajorityDynamics.Probability.RandomOpinionsReduction
