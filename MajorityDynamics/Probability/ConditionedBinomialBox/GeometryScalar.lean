import Mathlib.Tactic

noncomputable section

namespace MajorityDynamics.Probability.ConditionedBinomialBox.GeometryScalar

set_option maxHeartbeats 800000 in
/-- Scalar support and central-window estimates for a bounded drift of the
binomial mean. The variable `c` is an arbitrary real center, so this helper
does not impose any sign condition on the constraint matrix. -/
theorem coordinate_bounds {T K p N s η q c : ℝ}
    (hT : 1 < T) (hK : 0 ≤ K) (hp : 0 < p) (hN : 0 < N)
    (hs0 : 0 < s) (hs2 : s^2 = p*N)
    (hs : 2*T*(K+2) ≤ s) (hpSmall : p ≤ 1/(4*T^2))
    (hηlo : N/T ≤ η) (hηhi : η ≤ T*N)
    (hc : |c-p*η| ≤ K*s)
    (hq : |q-p| ≤ T*p/s) (hqlo : p/2 ≤ q) :
    0 < c ∧ c+1+s ≤ η ∧
    ∀ x : ℝ, c ≤ x → x ≤ c+1+s →
      |x-η*q| ≤ 2*T*(K+T^2+2)*Real.sqrt (η*q) := by
  have hT0 : 0 < T := by linarith
  have hη0 : 0 < η := (div_pos hN hT0).trans_le hηlo
  have hq0 : 0 < q := (half_pos hp).trans_le hqlo
  have hs1 : 1 ≤ s := by nlinarith
  have hpQuarter : p ≤ 1/4 := by
    apply hpSmall.trans
    apply (div_le_div_iff₀ (by positivity : 0 < 4*T^2) (by norm_num : (0:ℝ)<4)).mpr
    nlinarith
  have hscale : s^2/T ≤ p*η := by
    calc
      s^2/T = p*(N/T) := by rw [hs2]; ring
      _ ≤ p*η := mul_le_mul_of_nonneg_left hηlo hp.le
  have hlarge : 2*(K+2)*s ≤ p*η := by
    apply le_trans _ hscale
    apply (le_div_iff₀ hT0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs hs0.le]
  have hcLower := (abs_le.mp hc).1
  have hcUpper := (abs_le.mp hc).2
  have hcpos : 0 < c := by nlinarith
  have hcSupport : c+1+s ≤ η := by
    have hpη : p*η ≤ η/4 := by nlinarith [mul_le_mul_of_nonneg_right hpQuarter hη0.le]
    nlinarith
  refine ⟨hcpos, hcSupport, ?_⟩
  intro x hcx hxc
  have hxdev : |x-p*η| ≤ (K+2)*s := by
    rw [abs_le]
    constructor <;> nlinarith
  have htilt : |p*η-η*q| ≤ T^2*s := by
    rw [show p*η-η*q = η*(p-q) by ring, abs_mul, abs_of_pos hη0, abs_sub_comm]
    calc
      η*|q-p| ≤ η*(T*p/s) := mul_le_mul_of_nonneg_left hq hη0.le
      _ ≤ (T*N)*(T*p/s) := mul_le_mul_of_nonneg_right hηhi (by positivity)
      _ = T^2*s := by
        rw [← mul_div_assoc]
        apply (div_eq_iff hs0.ne').mpr
        calc
          T*N*(T*p) = T^2*(p*N) := by ring
          _ = T^2*s^2 := by rw [hs2]
          _ = T^2*s*s := by ring
  have hdev : |x-η*q| ≤ (K+T^2+2)*s := by
    have hh := abs_sub_le x (p*η) (η*q)
    nlinarith
  have hmean : s^2/(2*T) ≤ η*q := by
    calc
      s^2/(2*T) = (N/T)*(p/2) := by rw [hs2]; ring
      _ ≤ η*q := mul_le_mul hηlo hqlo (by positivity) hη0.le
  have hmu0 : 0 ≤ η*q := by positivity
  have hroot := Real.sqrt_nonneg (η*q)
  have hroot2 := Real.sq_sqrt hmu0
  have hscaleMu : s^2 ≤ 2*T*(η*q) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*T)).mp hmean
    nlinarith only [hh]
  have hsroot : s ≤ 2*T*Real.sqrt (η*q) := by
    have hh := mul_nonneg hmu0 (show 0 ≤ (2*T)^2-2*T by nlinarith)
    have hsq : s^2 ≤ (2*T*Real.sqrt (η*q))^2 := by
      calc
        s^2 ≤ 2*T*(η*q) := hscaleMu
        _ ≤ (2*T)^2*(η*q) := by nlinarith only [hh]
        _ = (2*T*Real.sqrt (η*q))^2 := by simp only [mul_pow, hroot2]
    exact (sq_le_sq₀ hs0.le (by positivity)).mp hsq
  apply hdev.trans
  have hh := mul_le_mul_of_nonneg_left hsroot (show 0 ≤ K+T^2+2 by positivity)
  nlinarith only [hh]

end MajorityDynamics.Probability.ConditionedBinomialBox.GeometryScalar
