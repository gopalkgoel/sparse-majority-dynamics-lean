import MajorityDynamics.Idealized.CriticalDay.FlexibleStopping
import MajorityDynamics.GraphProcess.LocalTransition.Basic

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Binomial.Approximation (SparseRange scale)

/-- The stopped gain dominates both the cleanup lead and the terminal sampling
error. This estimate is uniform in the stopping response. -/
theorem terminal_lead_budget_sparse (θ T r ζ C : ℝ)
    (hθ : θ < 1) (hT : 0 < T) (hr : 0 < r) (hr1 : r ≤ 1)
    (hζ : 0 < ζ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      1 ≤ scale N p → ∀ a : ℝ, scale N p^r ≤ a*scale N p →
      C*GraphProcess.LocalTransition.sizeScale N ≤ (ζ*min a 1/2)*N ∧
      (N:ℝ)/scale N p*Real.log N ≤ (ζ*min a 1/2)*N := by
  let K := max C 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  filter_upwards [eventually_ge_atTop (1:ℕ),
    sparse_scale_rpow_log_small θ T r (ζ/(2*K)) 1 hθ hT hr (by positivity)]
    with N hN hlog
  intro p hp hs a ha
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 < scale N p := lt_of_lt_of_le zero_lt_one hs
  have hpow : 0 < scale N p^r := Real.rpow_pos_of_pos hs0 _
  have hm : scale N p^r ≤ min a 1*scale N p := by
    rw [min_mul_of_nonneg _ _ hs0.le,one_mul]
    exact le_min ha (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hs hr1)
  have hm0 : 0 < min a 1 := (mul_pos_iff_of_pos_right hs0).mp (hpow.trans_le hm)
  have hl0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hh := (div_le_iff₀ hpow).mp (hlog p hp)
  simp only [pow_one] at hh
  have hh' : K*Real.log N ≤ (ζ/2)*min a 1*scale N p := by
    have hh1 := mul_le_mul_of_nonneg_left hh hK.le
    have hh2 := mul_le_mul_of_nonneg_left hm (half_pos hζ).le
    have he : K*(ζ/(2*K)) = ζ/2 := by field_simp
    rw [← mul_assoc,he] at hh1
    nlinarith only [hh1,hh2]
  have hlead : K*((N:ℝ)/scale N p*Real.log N) ≤ (ζ*min a 1/2)*N := by
    have hhN := mul_le_mul_of_nonneg_left hh' (div_nonneg hn.le hs0.le)
    calc
      _ = ((N:ℝ)/scale N p)*(K*Real.log N) := by ring
      _ ≤ ((N:ℝ)/scale N p)*((ζ/2)*min a 1*scale N p) := hhN
      _ = _ := by field_simp
  have hsize : GraphProcess.LocalTransition.sizeScale N ≤ (N:ℝ)/scale N p*Real.log N := by
    have hsn : scale N p ≤ Real.sqrt N := Real.sqrt_le_sqrt
      (by simpa using mul_le_mul_of_nonneg_right p.property.2.le hn.le)
    have hsq := Real.sq_sqrt hn.le
    have hprod := mul_le_mul_of_nonneg_left hsn (Real.sqrt_nonneg N)
    have hdiv : Real.sqrt N ≤ (N:ℝ)/scale N p := (le_div_iff₀ hs0).mpr (by nlinarith)
    exact mul_le_mul_of_nonneg_right hdiv hl0
  constructor
  · exact (mul_le_mul_of_nonneg_left hsize hC.le).trans
      ((mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)).trans hlead)
  · have hh : (N:ℝ)/scale N p*Real.log N ≤ K*((N:ℝ)/scale N p*Real.log N) := by
      simpa using mul_le_mul_of_nonneg_right (le_max_right C 1)
        (show 0 ≤ (N:ℝ)/scale N p*Real.log N by positivity)
    exact hh.trans hlead

end MajorityDynamics.Idealized.CriticalDay
