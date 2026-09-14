import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
namespace MajorityDynamics.GraphProcess.AutomaticGraphicality

/-- The paper's κ bound controls each degree by twice the global mean degree. -/
theorem degree_upper {N p a d : ℝ} (hp : 0 ≤ p) (ha : a ≤ N)
    (hx : 1 ≤ p * N) (hreg : |d - p * a| ≤ (p * N) ^ (4 / 7 : ℝ)) :
    d ≤ 2 * p * N := by
  have hr := Real.rpow_le_self_of_one_le hx (by norm_num : (4 / 7 : ℝ) ≤ 1)
  have hd := (abs_le.mp hreg).2
  have ha' := mul_le_mul_of_nonneg_left ha hp
  linarith

/-- Count regularity gives a positive lower bound for every ordered count. -/
theorem count_lower {N T p a b m : ℝ} (hN : 0 < N) (hT : 1 < T)
    (hp : 0 < p) (hx : 4 * T ^ 6 ≤ p * N)
    (ha : N / T ≤ a) (hb : N / T ≤ b)
    (hm : |m - p * a * b| ≤ T * N ^ 2 * p / Real.sqrt (p * N)) :
    p * N ^ 2 / (2 * T ^ 2) ≤ m := by
  have hT0 : 0 < T := by linarith
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT0
  have hx0 : 0 < p * N := mul_pos hp hN
  have hs0 : 0 < Real.sqrt (p * N) := Real.sqrt_pos.mpr hx0
  have hs : 2 * T ^ 3 ≤ Real.sqrt (p * N) := by
    have he := Real.sq_sqrt hx0.le
    have ht3 : 0 ≤ T ^ 3 := by positivity
    nlinarith [sq_nonneg (Real.sqrt (p * N) - 2 * T ^ 3)]
  have hab : N ^ 2 / T ^ 2 ≤ a * b := by
    have hnt : 0 ≤ N / T := le_of_lt (div_pos hN hT0)
    have hprod := mul_le_mul ha hb hnt (hnt.trans ha)
    rw [← div_pow, pow_two]
    exact hprod
  have hab' := mul_le_mul_of_nonneg_left hab hp.le
  have hcenter : p * N ^ 2 / T ^ 2 ≤ p * a * b := by
    simpa only [mul_div_assoc, mul_assoc] using hab'
  have herr : T * N ^ 2 * p / Real.sqrt (p * N) ≤ p * N ^ 2 / (2 * T ^ 2) := by
    apply (div_le_iff₀ hs0).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * T ^ 2)).mpr
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ p * N ^ 2 by positivity)
    convert hh using 1; ring
  have heq : p * N ^ 2 / T ^ 2 = 2 * (p * N ^ 2 / (2 * T ^ 2)) := by field_simp
  have hdev := (abs_le.mp hm).1
  linarith

/-- The small-density regime pays for the internal graphicality criterion. -/
theorem internal_bound {N T p δ : ℝ} (hT : 0 < T) (hp : 0 ≤ p)
    (hN : 0 ≤ N) (hx : 1 ≤ p * N) (hpSmall : p ≤ 1 / (12 * T ^ 2))
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 2 * p * N) :
    δ * (δ + 1) ≤ p * N ^ 2 / (2 * T ^ 2) := by
  have hδ1 : δ + 1 ≤ 3 * (p * N) := by linarith
  have hb := mul_le_mul hδ hδ1 (by linarith : 0 ≤ δ + 1) (by positivity : 0 ≤ 2 * p * N)
  have hp' := (le_div_iff₀ (show 0 < 12 * T ^ 2 by positivity)).mp hpSmall
  have hb' := mul_le_mul_of_nonneg_right hp' (show 0 ≤ p * N ^ 2 by positivity)
  apply le_trans hb
  apply (le_div_iff₀ (show 0 < 2 * T ^ 2 by positivity)).mpr
  nlinarith [hb']

/-- The same regime also pays for the cross-block graphicality criterion. -/
theorem cross_bound {N T p δ ε : ℝ} (hT : 0 < T) (hp : 0 ≤ p)
    (hN : 0 ≤ N) (hpSmall : p ≤ 1 / (12 * T ^ 2))
    (_hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε)
    (hδ : δ ≤ 2 * p * N) (hε : ε ≤ 2 * p * N) :
    δ * ε ≤ p * N ^ 2 / (2 * T ^ 2) := by
  have hb := mul_le_mul hδ hε hε0 (by positivity : 0 ≤ 2 * p * N)
  have hp' := (le_div_iff₀ (show 0 < 12 * T ^ 2 by positivity)).mp hpSmall
  have hb' := mul_le_mul_of_nonneg_right hp' (show 0 ≤ p * N ^ 2 by positivity)
  apply le_trans hb
  apply (le_div_iff₀ (show 0 < 2 * T ^ 2 by positivity)).mpr
  nlinarith [mul_nonneg (show 0 ≤ p ^ 2 * N ^ 2 by positivity) (show 0 ≤ T ^ 2 by positivity)]

end MajorityDynamics.GraphProcess.AutomaticGraphicality
