import MajorityDynamics.Probability.RandomOpinionsReduction.Bias
import MajorityDynamics.Probability.RandomOpinionsReduction.Dynamics

noncomputable section
namespace MajorityDynamics.Probability.RandomOpinionsReduction

def majorityOrientation {N : ℕ} (c : Paper.Coloring N) : Paper.Coloring N :=
  if (N : ℝ)/2 ≤ (Paper.plusCount c : ℝ) then c else flip c

theorem majorityOrientation_count {N : ℕ} (c : Paper.Coloring N) :
    (Paper.plusCount (majorityOrientation c) : ℝ) =
      |(Paper.plusCount c : ℝ) - (N : ℝ)/2| + (N : ℝ)/2 := by
  unfold majorityOrientation
  split_ifs with h
  · rw [abs_of_nonneg (by linarith)]
    ring
  · rw [plusCount_flip, Nat.cast_sub (plusCount_le c), abs_of_nonpos (by linarith)]
    ring

theorem half_floor_bounds (N : ℕ) :
    ((N/2 : ℕ) : ℝ) ≤ (N : ℝ)/2 ∧ (N : ℝ)/2 ≤ ((N/2 : ℕ) : ℝ)+1 := by
  have he : ((N%2 : ℕ) : ℝ) + 2*((N/2 : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.mod_add_div N 2
  have hm : (N%2 : ℕ) < 2 := Nat.mod_lt N (by omega)
  have hm' : ((N%2 : ℕ) : ℝ) < 2 := by exact_mod_cast hm
  constructor <;> nlinarith [show (0 : ℝ) ≤ (N%2 : ℕ) by positivity]

theorem exact_majority_bias {N : ℕ} (hN : 1 ≤ N) {A : ℝ}
    (c : Paper.Coloring N)
    (hlo : A⁻¹ * Real.sqrt N ≤ |(Paper.plusCount c : ℝ) - (N : ℝ)/2|)
    (hhi : |(Paper.plusCount c : ℝ) - (N : ℝ)/2| ≤ A * Real.sqrt N) :
    ∃ τ : ℝ, A⁻¹ ≤ τ ∧ τ ≤ A+1 ∧ Paper.initialBias N τ (majorityOrientation c) := by
  let m := Paper.plusCount (majorityOrientation c)
  have hm := majorityOrientation_count c
  have hf := half_floor_bounds N
  have hmf : N/2 ≤ m := by
    have : ((N/2 : ℕ) : ℝ) ≤ m := by
      dsimp [m]
      linarith [abs_nonneg ((Paper.plusCount c : ℝ) - (N : ℝ)/2)]
    exact_mod_cast this
  let d := m-N/2
  have hd : (d : ℝ) = (m : ℝ)-((N/2 : ℕ) : ℝ) := Nat.cast_sub hmf
  have hs : 1 ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hN)
  have hsp : 0 < Real.sqrt N := by linarith
  refine ⟨(d : ℝ)/Real.sqrt N, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hsp).mpr
    rw [hd]
    dsimp [m]
    linarith
  · apply (div_le_iff₀ hsp).mpr
    rw [hd]
    dsimp [m]
    nlinarith
  · unfold Paper.initialBias
    rw [div_mul_cancel₀ _ hsp.ne', Nat.floor_natCast]
    dsimp [d, m]
    omega

theorem densityRange_mono {θ T U : ℝ} {N : ℕ} {p : unitInterval}
    (hT : 0 < T) (hTU : T ≤ U) (h : Paper.densityRange θ T N p) :
    Paper.densityRange θ U N p := by
  have hi : U⁻¹ ≤ T⁻¹ := inv_anti₀ hT hTU
  have hn : 0 ≤ (N : ℝ)^(-θ) := Real.rpow_nonneg (by positivity) _
  exact ⟨(mul_le_mul_of_nonneg_right hi hn).trans_lt h.1,
    h.2.trans_le (mul_le_mul_of_nonneg_right hTU hn)⟩

end MajorityDynamics.Probability.RandomOpinionsReduction
