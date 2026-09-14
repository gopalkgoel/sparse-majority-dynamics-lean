import MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency

noncomputable section
open Filter Topology
namespace MajorityDynamics.GraphProcess.RowGamma.Numerics

/-- The fourth power of the logarithm is eventually below the square-root scale. -/
theorem eventually_log_four_le_sqrt :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      2 ≤ N ∧ 0 < Real.log (N : ℝ) ∧
      (Real.log (N : ℝ)) ^ 4 ≤ Real.sqrt (N : ℝ) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (2 : ℕ)).and
      (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))))
  refine ⟨N₀, fun N hN => ?_⟩
  have hN2 := (hN₀ N hN).1
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  refine ⟨hN2, hlog, ?_⟩
  have h := (hN₀ N hN).2.le
  change (Real.log (N : ℝ)) ^ (4 : ℝ) / (N : ℝ) ^ ((1 : ℝ)/2) ≤ 1 at h
  have hp := (div_le_one (Real.rpow_pos_of_pos hNp (1/2))).mp h
  rw [← Real.rpow_natCast (Real.log (N : ℝ)) 4]
  convert hp using 1 <;> norm_num [Real.sqrt_eq_rpow]
  rfl

/-- The clipped-square Hoeffding tail beats every fixed polynomial, even after
multiplication by an arbitrary fixed nonnegative union-bound coefficient. -/
theorem eventually_clipped_tail (C A : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      C * (2 * Real.exp (-2 * (N : ℝ) / (Real.log (N : ℝ)) ^ 4)) ≤
        (N : ℝ) ^ (-A) := by
  obtain ⟨N₁, h₁⟩ := eventually_log_four_le_sqrt
  obtain ⟨N₂, h₂⟩ :=
    Probability.ConditionedBinomialFourier.HighFrequency.exp_eventually_le
      2 (1/2) A (2 * (C+1)) (by norm_num) (by norm_num) (by positivity)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  obtain ⟨hN2, hlog, hsmall⟩ := h₁ N ((le_max_left _ _).trans hN)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hratio : Real.sqrt (N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 4 := by
    apply (le_div_iff₀ (by positivity : 0 < (Real.log (N : ℝ)) ^ 4)).mpr
    calc
      _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall hs.le
      _ = (N : ℝ) := Real.mul_self_sqrt hNp.le
  have hexp : Real.exp (-2 * (N : ℝ) / (Real.log (N : ℝ)) ^ 4) ≤
      Real.exp (-2 * (N : ℝ) ^ ((1 : ℝ)/2)) := by
    apply Real.exp_le_exp.mpr
    rw [← Real.sqrt_eq_rpow]
    calc
      _ = -2 * ((N : ℝ) / (Real.log (N : ℝ)) ^ 4) := by ring
      _ ≤ -2 * Real.sqrt (N : ℝ) := by linarith
  have he := h₂ N ((le_max_right _ _).trans hN)
  have hm := (le_div_iff₀ (by positivity : 0 < 2*(C+1))).mp he
  calc
    _ = (2*C) * Real.exp (-2 * (N : ℝ) / (Real.log (N : ℝ)) ^ 4) := by ring
    _ ≤ (2*C) * Real.exp (-2 * (N : ℝ) ^ ((1:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (2*(C+1)) * Real.exp (-2 * (N : ℝ) ^ ((1:ℝ)/2)) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (N : ℝ)^(-A) := by nlinarith only [hm]

/-- One extra polynomial power absorbs a factor of two. -/
theorem absorb_two {N : ℕ} (hN : 2 ≤ N) (A : ℝ) :
    2 * (N : ℝ)^(-(A+1)) ≤ (N : ℝ)^(-A) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hid : (N : ℝ)^(-(A+1)) = (N : ℝ)^(-A) / (N : ℝ) := by
    rw [show -(A+1) = -A-1 by ring, Real.rpow_sub hNp, Real.rpow_one]
  rw [hid]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hN2 (Real.rpow_nonneg hNp.le (-A))
  nlinarith only [hh]

/-- The eventual regularity lower bound is at least one half. -/
theorem half_lower {N : ℕ} (hN : 2 ≤ N) :
    (1 : ℝ) / 2 ≤ 1 - (N : ℝ)^(-(1 : ℝ)) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.rpow_neg hNp.le, Real.rpow_one]
  have hh : (N : ℝ)⁻¹ ≤ 1/2 := (inv_le_comm₀ hNp (by norm_num)).mpr (by norm_num; exact hN)
  linarith

end MajorityDynamics.GraphProcess.RowGamma.Numerics

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.Numerics.eventually_log_four_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.Numerics.eventually_log_four_le_sqrt

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.Numerics.eventually_clipped_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.Numerics.eventually_clipped_tail

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.Numerics.absorb_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.Numerics.absorb_two

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.Numerics.half_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.Numerics.half_lower
