import MajorityDynamics.Combinatorics.DegreeRatios.Uniform
import MajorityDynamics.Binomial.SparseLogBudget

noncomputable section
open Filter Topology
namespace MajorityDynamics.Combinatorics.DegreeRatios

/-- Independent lower and upper exponents; constants precede the density. -/
def SparseDensityWindow (θ T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  T⁻¹ * (n : ℝ)^(-θ) < p ∧ p < T * (n : ℝ)^(-(1/2 : ℝ))

/-- The logarithmic error budget only needs `n*p² ≤ log n`, not `≤ 1`. -/
def SparseLargeParameters (T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  64 * T ≤ (n : ℝ) ∧ 1 ≤ Real.log (n : ℝ) ∧
  0 < p ∧ p ≤ 1 / 16 ∧ (n : ℝ) * p ^ 2 ≤ Real.log n ∧
  2 * (relativeConstant T + 1) * (Real.log (n : ℝ) + 1) ≤ Real.sqrt (p * n)

theorem eventually_sparse_large_parameters (θ T : ℝ)
    (_hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      SparseLargeParameters T n p := by
  have hT0 : 0 < T := by linarith
  have hK : 0 < relativeConstant T + 1 := by dsimp [relativeConstant]; positivity
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hup : Tendsto (fun n : ℕ => T * (n : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hn).const_mul T
  have hlog := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop (max 1 (T^2))
  filter_upwards [hn.eventually_ge_atTop (64*T), hlog, eventually_ge_atTop (1 : ℕ),
    hup.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/16)),
    Binomial.Approximation.sparseRange_scale_log_power θ T
      (8*(relativeConstant T+1)) 3 hθhi hT0 (by positivity)]
    with n hsize hlogs hn1 hu hscale
  intro p hp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : 1 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlogs
  have hlogT : T^2 ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hlogs
  have hp0 : 0 < p := (by positivity : 0 < T⁻¹*(n : ℝ)^(-θ)).trans hp.1
  have hp16 : p ≤ 1/16 := (hp.2.trans hu).le
  let prob : Binomial.Probability := ⟨p,hp0,by linarith⟩
  have hdensity : Binomial.Approximation.SparseRange θ T n prob := hp
  have hs := hscale prob hdensity
  change 8*(relativeConstant T+1)*Real.log (n : ℝ)^3 ≤ Real.sqrt (p*n) at hs
  have hsmall : p*Real.sqrt n ≤ T := by
    calc
      _ ≤ T*(n : ℝ)^(-(1/2 : ℝ))*Real.sqrt n :=
        mul_le_mul_of_nonneg_right hp.2.le (Real.sqrt_nonneg _)
      _ = T := by
        rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hn0]
        norm_num
  have hh := (sq_le_sq₀ (by positivity : 0 ≤ p*Real.sqrt n) hT0.le).mpr hsmall
  rw [mul_pow, Real.sq_sqrt hn0.le] at hh
  have hsparse : (n : ℝ)*p^2 ≤ Real.log n := by nlinarith
  refine ⟨hsize,hlog,hp0,hp16,hsparse,?_⟩
  have hpow : Real.log (n : ℝ) ≤ Real.log (n : ℝ)^3 := by
    have hh : (1 : ℝ) ≤ Real.log (n : ℝ)^2 := by nlinarith [sq_nonneg (Real.log (n : ℝ)-1)]
    have hm := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ Real.log (n : ℝ))
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hpow hK.le
  have hh1 := mul_le_mul_of_nonneg_left hlog hK.le
  nlinarith

end MajorityDynamics.Combinatorics.DegreeRatios
