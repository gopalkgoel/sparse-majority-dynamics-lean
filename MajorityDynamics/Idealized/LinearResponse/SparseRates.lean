import MajorityDynamics.Idealized.LinearResponse.Rates
import MajorityDynamics.Idealized.Process.SparseMain
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.LinearResponse
open Binomial.Approximation

/-- A conservative rate uniform over all finitely many pre-stopping levels. -/
def sparseResponseRate (θ : ℝ) : ℝ := (1-θ)/16

/-- Small-response condition replacing a fixed subcritical density exponent. -/
def ResponseSmall (θ : ℝ) (N : ℕ) (p : ℝ) (n : ℕ) : Prop :=
  betaScale N p n * Real.sqrt (p*N) ≤ (N:ℝ)^(-((1-θ)/4))

theorem sparseResponseRate_pos {θ : ℝ} (hθ : θ < 1) : 0 < sparseResponseRate θ := by
  unfold sparseResponseRate
  linarith

theorem sqrt_pN_lower_sparse {N : ℕ} (hN : 0 < N) {θ T : ℝ} (hT : 0 < T) {p : Binomial.Probability}
    (hp : SparseRange θ T N p) :
    (Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2) ≤ Real.sqrt ((p : ℝ) * N) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hlo := mul_le_mul_of_nonneg_right hp.1.le hN0.le
  have hpow : (N:ℝ)^(-θ)*N = (N:ℝ)^(1-θ) := by
    rw [← Real.rpow_add_one hN0.ne']
    congr 1
    ring
  rw [mul_assoc,hpow] at hlo
  have hhalf : Real.sqrt ((N:ℝ)^(1-θ)) = (N:ℝ)^((1-θ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have h := Real.sqrt_le_sqrt hlo
  rwa [Real.sqrt_mul (inv_nonneg.mpr hT.le), Real.sqrt_inv,hhalf] at h

theorem eventually_basic_sparse (θ T : ℝ) (_hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 2 ≤ Real.log (N : ℝ) ∧
      ∀ p : Binomial.Probability, SparseRange θ T N p →
        1 ≤ Real.sqrt ((p : ℝ) * N) ∧ Real.sqrt ((p : ℝ) * N) ≤ N ∧ (p : ℝ) ≤ 1 / 8 := by
  have hT0 : 0 < T := by linarith
  have hlog : ∀ᶠ N : ℕ in atTop, 2 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
    RowLimits.density_scale_lower_power_sparse θ T 1 0 hθhi hT0 zero_lt_one,
    sparseRange_small_parameters θ T hT0] with N hN hlog hscale hsmall
  refine ⟨hN, hlog, ?_⟩
  intro p hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by simpa [scale] using hscale p hp, ?_, (hsmall p hp).1⟩
  apply (Real.sqrt_le_left hN0.le).mpr
  have hh := mul_le_mul_of_nonneg_right p.property.2.le hN0.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [hh, hN1, hN0]

theorem eventually_small_sparse (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) (n m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      Real.sqrt (p : ℝ) * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ (-sparseResponseRate θ) ∧
      (p : ℝ) * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ (-sparseResponseRate θ) ∧
      Real.log (N : ℝ) ^ m / Real.sqrt ((p : ℝ) * N) ≤ (N : ℝ) ^ (-sparseResponseRate θ) ∧
      betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ m ≤
        (N : ℝ) ^ (-sparseResponseRate θ) := by
  have hT0 : 0 < T := by linarith
  have hκθ : sparseResponseRate θ < (1/2:ℝ)/2 := by unfold sparseResponseRate; linarith
  have hκθ' : sparseResponseRate θ < (1/2:ℝ) := by unfold sparseResponseRate; linarith
  have hκc : sparseResponseRate θ < (1-θ)/2 := by unfold sparseResponseRate; linarith
  have hκa : sparseResponseRate θ < (1-θ)/4 := by unfold sparseResponseRate; linarith
  have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  filter_upwards [eventually_gt_atTop (0:ℕ),
    eventually_poly_log_le (Real.sqrt T) ((1/2:ℝ)/2) (sparseResponseRate θ) m hsT hκθ,
    eventually_poly_log_le T (1/2) (sparseResponseRate θ) m hT0.le hκθ',
    eventually_poly_log_le (Real.sqrt T) ((1-θ)/2) (sparseResponseRate θ) m hsT hκc,
    eventually_poly_log_le 1 ((1-θ)/4) (sparseResponseRate θ) m zero_le_one hκa]
      with N hN h1 h2 h3 h4
  simp only [one_mul] at h4
  intro p hp hsub
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) ^ m := pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) m
  have hslo := sqrt_pN_lower_sparse hN hT0 hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- √p ≤ √T N^{-θ/2}
    have hsqrt : Real.sqrt (p : ℝ) ≤ Real.sqrt T * (N : ℝ) ^ (-((1/2:ℝ) / 2)) := by
      have h := Real.sqrt_le_sqrt hp.2.le
      rw [Real.sqrt_mul hT0.le, Real.sqrt_eq_rpow ((N : ℝ) ^ (-(1/2:ℝ))), ← Real.rpow_mul hN0.le] at h
      rwa [show -(1/2:ℝ) * (1 / 2) = -((1/2:ℝ) / 2) by ring] at h
    calc
      _ ≤ Real.sqrt T * (N : ℝ) ^ (-((1/2:ℝ) / 2)) * Real.log (N : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hsqrt hlog
      _ ≤ _ := h1
  · calc
      (p : ℝ) * Real.log (N : ℝ) ^ m ≤ T * (N : ℝ) ^ (-(1/2:ℝ)) * Real.log (N : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hp.2.le hlog
      _ ≤ _ := h2
  · have hinv : Real.log (N : ℝ) ^ m / Real.sqrt ((p : ℝ) * N) ≤
        Real.sqrt T * (N : ℝ) ^ (-((1 - θ) / 2)) * Real.log (N : ℝ) ^ m := by
      have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
      have hlo0 : 0 < (Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2) := by positivity
      have hspos : 0 < Real.sqrt ((p : ℝ) * N) := lt_of_lt_of_le hlo0 hslo
      rw [div_le_iff₀ hspos, Real.rpow_neg hN0.le]
      have hkey : Real.sqrt T * ((N : ℝ) ^ ((1 - θ) / 2))⁻¹ *
          ((Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2)) = 1 := by
        rw [mul_mul_mul_comm, mul_inv_cancel₀ hsT0.ne',
          inv_mul_cancel₀ (Real.rpow_pos_of_pos hN0 _).ne', mul_one]
      calc
        Real.log (N : ℝ) ^ m = Real.log (N : ℝ) ^ m *
            (Real.sqrt T * ((N : ℝ) ^ ((1 - θ) / 2))⁻¹ *
              ((Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2))) := by rw [hkey, mul_one]
        _ ≤ Real.log (N : ℝ) ^ m *
            (Real.sqrt T * ((N : ℝ) ^ ((1 - θ) / 2))⁻¹ * Real.sqrt ((p : ℝ) * N)) := by
          apply mul_le_mul_of_nonneg_left _ hlog
          apply mul_le_mul_of_nonneg_left hslo
          positivity
        _ = _ := by ring
    exact hinv.trans h3
  · exact (mul_le_mul_of_nonneg_right hsub hlog).trans h4

end MajorityDynamics.Idealized.LinearResponse
