import MajorityDynamics.Idealized.CriticalDay.StoppingBudgets
import MajorityDynamics.Idealized.RowLimits.SparseGeometry
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Binomial.Approximation LinearResponse

/-- The terminal window need not use a fixed quarter power. Any t with
1 ≤ t and t³ ≤ s works, provided t/s ≤ a ≤ t. -/
theorem flexible_stopping_error {s t a e l : ℝ}
    (ht : 1 ≤ t) (hs : t^3 ≤ s) (ha : 0 < a)
    (halo : t ≤ a*s) (hahi : a ≤ t) (he : 0 ≤ e) (hl : 0 ≤ l) :
    ((1+a+a^2)/s*l+a*e)/min a 1 ≤ 3*l/t+t*e := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := (pow_pos ht0 3).trans_le hs
  have hmin : 0 < min a 1 := lt_min ha zero_lt_one
  apply (div_le_iff₀ hmin).mpr
  rcases le_total a 1 with ha1 | h1a
  · rw [min_eq_left ha1]
    have hnum : 1+a+a^2 ≤ 3 := by nlinarith
    have hr : (1+a+a^2)/s ≤ 3/t*a := by
      apply (div_le_iff₀ hs0).mpr
      apply hnum.trans
      have hh := mul_le_mul_of_nonneg_left halo (show 0 ≤ 3/t by positivity)
      have hid : 3/t*t = 3 := by field_simp
      rw [hid] at hh
      nlinarith only [hh]
    have herr : a*e ≤ t*e*a := by
      have hh := mul_le_mul_of_nonneg_right ht (mul_nonneg ha.le he)
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hr hl
    convert add_le_add hh herr using 1
    ring
  · rw [min_eq_right h1a, mul_one]
    have ht2 : t ≤ t^2 := by nlinarith
    have hnum : 1+a+a^2 ≤ 3*t^2 := by nlinarith
    have hr : (1+a+a^2)/s ≤ 3/t := by
      apply (div_le_iff₀ hs0).mpr
      apply hnum.trans
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3/t by positivity)
      have hid : 3/t*t^3 = 3*t^2 := by field_simp
      rwa [hid] at hh
    have hh := add_le_add (mul_le_mul_of_nonneg_right hr hl)
      (mul_le_mul_of_nonneg_right hahi he)
    convert hh using 1
    ring

theorem scale_rpow_sparse_bounds {N : ℕ} {p : Binomial.Probability} {θ T r : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hr : 0 ≤ r) (hp : SparseRange θ T N p) :
    (T⁻¹)^(r/2)*(N:ℝ)^((1-θ)*r/2) ≤ scale N p ^ r ∧
    scale N p ^ r ≤ T^(r/2)*(N:ℝ)^(r/4) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ (p:ℝ)*N := mul_nonneg p.property.1.le hn.le
  have he (a : ℝ) : (N:ℝ)^(-a)*N = (N:ℝ)^(1-a) := by
    rw [← Real.rpow_add_one hn.ne']
    congr 1
    ring
  have hlo := mul_le_mul_of_nonneg_right hp.1.le hn.le
  have hhi := mul_le_mul_of_nonneg_right hp.2.le hn.le
  rw [mul_assoc, he] at hlo hhi
  have hid : scale N p ^ r = ((p:ℝ)*N)^(r/2) := by
    rw [scale, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    congr 1
    ring
  rw [hid]
  have hl := Real.rpow_le_rpow (by positivity) hlo (by linarith : 0 ≤ r/2)
  have hu := Real.rpow_le_rpow hx hhi (by linarith : 0 ≤ r/2)
  rw [Real.mul_rpow (inv_nonneg.mpr hT.le) (Real.rpow_nonneg hn.le _),
    ← Real.rpow_mul hn.le] at hl
  rw [Real.mul_rpow hT.le (Real.rpow_nonneg hn.le _),
    ← Real.rpow_mul hn.le] at hu
  constructor
  · convert hl using 1
    congr 2
    ring
  · convert hu using 1
    congr 2
    ring

/-- Every positive power of the degree scale beats fixed logarithmic losses. -/
theorem sparse_scale_rpow_log_small (θ T r ε : ℝ) (k : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      Real.log N ^ k / scale N p ^ r ≤ ε := by
  have hpow : 0 < (1-θ)*r/2 := by positivity
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hpow).comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hb := hh.bound (show 0 < ε*(T⁻¹)^(r/2) by positivity)
  filter_upwards [eventually_ge_atTop (1:ℕ),hb] with N hN hb
  intro p hp
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hb' : Real.log N ^ k ≤ ε*(T⁻¹)^(r/2)*(N:ℝ)^((1-θ)*r/2) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, norm_pow,
      Real.norm_of_nonneg hl, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)] using hb
  have hlo := (scale_rpow_sparse_bounds (by omega) hT hr.le hp).1
  have hs : 0 < scale N p ^ r := Real.rpow_pos_of_pos
    (Real.sqrt_pos.mpr (mul_pos p.property.1 hn)) _
  apply (div_le_iff₀ hs).mpr
  exact hb'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlo hε.le)

/-- Any inherited polynomial error can be paid by choosing the terminal
amplification exponent sufficiently small, after that error rate is known. -/
theorem sparse_polynomial_amplification (θ T r δ C ε : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hgap : r/4 < δ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ e : ℝ, e ≤ C*(N:ℝ)^(-δ) → scale N p ^ r * e ≤ ε := by
  have ht : Tendsto (fun N : ℕ => C*T^(r/2)*(N:ℝ)^(-(δ-r/4))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (sub_pos.mpr hgap)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (C*T^(r/2))
  filter_upwards [eventually_ge_atTop (1:ℕ), ht.eventually (eventually_lt_nhds hε)]
    with N hN ht
  intro p hp e he
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hs := (scale_rpow_sparse_bounds (by omega) hT hr.le hp).2
  calc
    _ ≤ scale N p ^ r * (C*(N:ℝ)^(-δ)) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    _ ≤ (T^(r/2)*(N:ℝ)^(r/4))*(C*(N:ℝ)^(-δ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = C*T^(r/2)*(N:ℝ)^(-(δ-r/4)) := by
      rw [show -(δ-r/4) = r/4+(-δ) by ring, Real.rpow_add hn]
      ring
    _ ≤ ε := ht.le

end MajorityDynamics.Idealized.CriticalDay
