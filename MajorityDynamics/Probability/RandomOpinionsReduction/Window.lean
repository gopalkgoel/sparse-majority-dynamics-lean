import MajorityDynamics.Probability.RandomOpinionsReduction.Bias

noncomputable section
open MeasureTheory
namespace MajorityDynamics.Probability.RandomOpinionsReduction

def goodBias (N : ℕ) (A : ℝ) : Set (Paper.Coloring N) :=
  {c | A⁻¹ * Real.sqrt N ≤ |(Paper.plusCount c : ℝ) - (N : ℝ)/2| ∧
    |(Paper.plusCount c : ℝ) - (N : ℝ)/2| ≤ A * Real.sqrt N}

theorem bad_bias_bound {N : ℕ} (hN : 0 < N) {A : ℝ} (hA : 1 < A) :
    (uniformColoringLaw N).real (goodBias N A)ᶜ ≤ 5/A + 2/Real.sqrt N := by
  have hAp : 0 < A := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hl := small_ball hN ((N : ℝ)/2) (A⁻¹ * Real.sqrt N) (by positivity)
  have hu := upper_tail hN hAp
  have he : (goodBias N A)ᶜ =
      {c | |(Paper.plusCount c : ℝ) - (N : ℝ)/2| < A⁻¹*Real.sqrt N} ∪
      {c | A*Real.sqrt N < |(Paper.plusCount c : ℝ) - (N : ℝ)/2|} := by
    ext c
    simp only [goodBias, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union,
      not_and_or, not_le]
  rw [he]
  have hi : 1/(4*A^2) ≤ 1/A := by
    apply (div_le_div_iff₀ (by positivity) hAp).mpr
    nlinarith
  have hh : (2*(A⁻¹*Real.sqrt N)+1)*(2/Real.sqrt N) = 4/A+2/Real.sqrt N := by
    field_simp
    ring
  rw [hh] at hl
  have hid : 4/A+1/A = 5/A := by ring
  exact (measureReal_union_le _ _).trans (by linarith)

/-- The constants and threshold depend only on ε, before any graph density or coloring. -/
theorem random_bias_window (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 < A ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      uniformColoringLaw N (goodBias N A)ᶜ ≤ ENNReal.ofReal ε := by
  let A : ℝ := max 2 (10/ε)
  have hA : 1 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAp : 0 < A := by linarith
  have hAe : 10 ≤ A*ε := (div_le_iff₀ hε).mp (le_max_right _ _)
  obtain ⟨M, hM⟩ := exists_nat_gt ((4/ε)^2)
  refine ⟨A, hA, max 1 M, le_max_left _ _, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hsq := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN1)
  have hsbound : 4/ε ≤ Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ), show (0 : ℝ) < 4/ε by positivity]
  have hse : 4 ≤ Real.sqrt N * ε := (div_le_iff₀ hε).mp hsbound
  have ha : 5/A ≤ ε/2 := (div_le_iff₀ hAp).mpr (by nlinarith)
  have hb : 2/Real.sqrt N ≤ ε/2 := (div_le_iff₀ hs).mpr (by nlinarith)
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  exact (bad_bias_bound hN1 hA).trans (by linarith)

end MajorityDynamics.Probability.RandomOpinionsReduction
