import MajorityDynamics.Probability.NeighborhoodBulk.Basic
import MajorityDynamics.Combinatorics.DegreeRatios.LogBounds
import MajorityDynamics.Literature.DegreeEnumeration.Consequences

noncomputable section
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Combinatorics.DegreeRatios

theorem count_log_control {P M c K : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hrel : RelativeApproximation (1 / 2) P (M * c))
    (hlo : Real.exp (-K) ≤ c) (hhi : c ≤ Real.exp K) :
    0 < P ∧ |Real.log P - Real.log M| ≤ K + 1 := by
  obtain ⟨ε, hε, rfl⟩ := hrel
  have hep : 0 < 1 + ε := by linarith [(abs_le.mp hε).1]
  refine ⟨mul_pos (mul_pos hM hc) hep, ?_⟩
  have hlogc : |Real.log c| ≤ K := by
    apply abs_le.mpr
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-K)) hlo
    · simpa only [Real.log_exp] using Real.log_le_log hc hhi
  have he : |Real.log (1 + ε)| ≤ 1 := by
    have hh := abs_log_one_sub_le (x := -ε) (by simpa using hε)
    simp only [sub_neg_eq_add, abs_neg] at hh
    linarith
  rw [Real.log_mul (mul_pos hM hc).ne' hep.ne', Real.log_mul hM.ne' hc.ne']
  convert (abs_add_le (Real.log c) (Real.log (1 + ε))).trans (add_le_add hlogc he) using 1
  congr 1
  ring

theorem count_ratio_log_control {P Q M N A B : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hN : 0 < N)
    (hPM : |Real.log P - Real.log M| ≤ A) (hQN : |Real.log Q - Real.log N| ≤ B) :
    |Real.log (P / Q) - Real.log (M / N)| ≤ A + B := by
  rw [Real.log_div hP.ne' hQ.ne', Real.log_div hM.ne' hN.ne']
  convert (abs_sub (Real.log P - Real.log M) (Real.log Q - Real.log N)).trans
    (add_le_add hPM hQN) using 1
  congr 1
  ring

theorem multiplicative_of_log_bound {P Q K : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (h : |Real.log P - Real.log Q| ≤ K) :
    Real.exp (-K) * Q ≤ P ∧ P ≤ Real.exp K * Q := by
  have hlo : -K + Real.log Q ≤ Real.log P := by linarith [(abs_le.mp h).1]
  have hhi : Real.log P ≤ K + Real.log Q := by linarith [(abs_le.mp h).2]
  constructor
  · simpa only [Real.exp_add, Real.exp_log hP, Real.exp_log hQ] using Real.exp_le_exp.mpr hlo
  · simpa only [Real.exp_add, Real.exp_log hP, Real.exp_log hQ] using Real.exp_le_exp.mpr hhi

theorem profile_ratio_log_control {P M r B c w z A D E : ℝ}
    (hP : 0 < P) (hr : 0 < r) (hB : 0 < B) (hc : 0 < c)
    (hmodel : M = r * B / c)
    (hcount : |Real.log P - Real.log M| ≤ A)
    (hratio : |Real.log r + z| ≤ D)
    (hprofile : |Real.log B - z - w| ≤ E) :
    Real.exp (-(A + D + E)) * (Real.exp w / c) ≤ P ∧
      P ≤ Real.exp (A + D + E) * (Real.exp w / c) := by
  apply multiplicative_of_log_bound hP (div_pos (Real.exp_pos w) hc)
  have hsum := (abs_add_le (Real.log P - Real.log M)
    ((Real.log r + z) + (Real.log B - z - w))).trans
    (add_le_add hcount ((abs_add_le _ _).trans (add_le_add hratio hprofile)))
  rw [hmodel, Real.log_div (mul_pos hr hB).ne' hc.ne', Real.log_mul hr.ne' hB.ne'] at hsum
  rw [Real.log_div (Real.exp_pos w).ne' hc.ne', Real.log_exp]
  have hid : Real.log P - (w - Real.log c) =
      Real.log P - (Real.log r + Real.log B - Real.log c) +
        (Real.log r + z + (Real.log B - z - w)) := by ring
  rw [hid]
  simpa only [add_assoc] using hsum

end MajorityDynamics.Probability.NeighborhoodBulk
