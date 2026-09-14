import MajorityDynamics.Idealized.CriticalDay.StoppingScales
import MajorityDynamics.Binomial.SparseLogBudget

/-! The stopping rule pays every fixed logarithmic loss, including the
amplification of the inherited faithful error by the terminal response. -/
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Binomial.Approximation LinearResponse

theorem sparse_quarter_scale_log (θ T ε : ℝ) (k : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      Real.log N ^ k / (scale N p) ^ (1 / 4 : ℝ) ≤ ε := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    sparseRange_scale_log_power θ T (ε⁻¹ ^ 4) (4 * k) hθ hT (by positivity)]
    with N hN hscale
  intro p hp
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < scale N p := Real.sqrt_pos.mpr (mul_pos p.property.1 hn)
  have ht : 0 < scale N p ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hs _
  have ht4 : (scale N p ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = scale N p := by
    rw [← Real.rpow_mul_natCast hs.le]
    norm_num
  have hl : 0 ≤ Real.log N ^ k := pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _
  have hpow : (Real.log N ^ k) ^ 4 ≤ (ε * scale N p ^ (1 / 4 : ℝ)) ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left (hscale p hp) (pow_nonneg hε.le 4)
    rw [show 4 * k = k * 4 by omega, pow_mul] at hh
    have he : ε ^ 4 * (ε⁻¹ ^ 4 * (Real.log N ^ k) ^ 4) = (Real.log N ^ k) ^ 4 := by
      field_simp
    rw [he] at hh
    simpa only [mul_pow, ht4] using hh
  apply (div_le_iff₀ ht).mpr
  exact (pow_le_pow_iff_left₀ hl (mul_nonneg hε.le ht.le) (by norm_num : (4 : ℕ) ≠ 0)).mp hpow

/-- The upper sparse endpoint supplies p*t^4 <= 1. This controls the
sqrt(p) part of the inherited error even after multiplication by t. -/
theorem stopping_inherited_error {t p C l e : ℝ} (ht : 1 ≤ t)
    (hp : 0 ≤ p) (hpt : p * t ^ 4 ≤ 1) (hC : 0 ≤ C) (hl : 0 ≤ l)
    (he : e ≤ C * (Real.sqrt p + 1 / t ^ 3) * l) :
    t * e ≤ 2 * C * l / t := by
  have ht0 : 0 < t := by linarith
  have hroot : Real.sqrt p * t ^ 2 ≤ 1 := by
    have heq : (Real.sqrt p * t ^ 2) ^ 2 = p * t ^ 4 := by
      rw [mul_pow, Real.sq_sqrt hp]
      ring
    have hh : (Real.sqrt p * t ^ 2) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa [heq] using hpt
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)).mp hh
  have hfirst : t * Real.sqrt p ≤ 1 / t := by
    apply (le_div_iff₀ ht0).mpr
    nlinarith only [hroot]
  have hsecond : t * (1 / t ^ 3) ≤ 1 / t := by
    have heq : t * (1 / t ^ 3) = 1 / t ^ 2 := by field_simp
    rw [heq]
    apply div_le_div_of_nonneg_left (by norm_num) ht0
    nlinarith
  calc
    t * e ≤ t * (C * (Real.sqrt p + 1 / t ^ 3) * l) :=
      mul_le_mul_of_nonneg_left he ht0.le
    _ = C * l * (t * Real.sqrt p + t * (1 / t ^ 3)) := by ring
    _ ≤ C * l * (1 / t + 1 / t) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (mul_nonneg hC hl)
    _ = _ := by ring

theorem uniform_inherited_error_budget (θ T C ε : ℝ) (k : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      let t := scale N p ^ (1 / 4 : ℝ)
      ∀ e : ℝ, e ≤ C * (Real.sqrt (p : ℝ) + 1 / t ^ 3) * Real.log N ^ k →
        t * e ≤ ε := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    sparseRange_scale_log_power θ T 1 0 hθ hT zero_lt_one,
    sparseRange_small_parameters θ T hT,
    sparse_quarter_scale_log θ T (ε / (2 * C + 1)) k hθ hT (by positivity)]
    with N hN hs hsmall hlog
  intro p hp
  dsimp only
  intro e he
  have hs1 : 1 ≤ scale N p := by simpa using hs p hp
  have hs0 : 0 < scale N p := zero_lt_one.trans_le hs1
  have ht : 1 ≤ scale N p ^ (1 / 4 : ℝ) := Real.one_le_rpow hs1 (by norm_num)
  have ht4 : (scale N p ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = scale N p := by
    rw [← Real.rpow_mul_natCast hs0.le]
    norm_num
  have hpt : (p : ℝ) * (scale N p ^ (1 / 4 : ℝ)) ^ (4 : ℕ) ≤ 1 := by
    rw [ht4]
    exact (hsmall p hp).2
  have hl : 0 ≤ Real.log N ^ k := pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _
  calc
    _ ≤ 2 * C * Real.log N ^ k / scale N p ^ (1 / 4 : ℝ) :=
      stopping_inherited_error ht p.property.1.le hpt hC hl he
    _ = 2 * C * (Real.log N ^ k / scale N p ^ (1 / 4 : ℝ)) := by ring
    _ ≤ 2 * C * (ε / (2 * C + 1)) :=
      mul_le_mul_of_nonneg_left (hlog p hp) (by positivity)
    _ ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (show 0 < 2 * C + 1 by positivity)).mpr
      nlinarith

theorem stopping_window_log_error {t a e l : ℝ} (ht : 1 ≤ t) (ha : 0 < a)
    (halo : 1 ≤ a * t ^ 3) (hahi : a ≤ t) (he : 0 ≤ e) (hl : 0 < l) :
    ((1 + a + a ^ 2) / t ^ 4 * l + a * e) / min a 1 ≤
      3 * l / t + t * e := by
  have hh := mul_le_mul_of_nonneg_right
    (stopping_window_error ht ha halo hahi (div_nonneg he hl.le)) hl.le
  have hleft : ((1 + a + a ^ 2) / t ^ 4 + a * (e / l)) / min a 1 * l =
      ((1 + a + a ^ 2) / t ^ 4 * l + a * e) / min a 1 := by
    field_simp [hl.ne']
  have hright : (3 / t + t * (e / l)) * l = 3 * l / t + t * e := by
    field_simp [hl.ne']
  rwa [hleft, hright] at hh

/-- All terminal centering errors, relative to the useful signal, are
uniformly small under the explicit inherited-error budget. The separate
trajectory induction must establish that budget for its actual errors. -/
theorem uniform_terminal_error_budget (θ T C ε : ℝ) (k : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      let t := scale N p ^ (1 / 4 : ℝ)
      ∀ a e : ℝ, 0 < a → 1 ≤ a * t ^ 3 → a ≤ t → 0 ≤ e →
      e ≤ C * (Real.sqrt (p : ℝ) + 1 / t ^ 3) * Real.log N ^ k →
      ((1 + a + a ^ 2) / t ^ 4 * Real.log N ^ k + a * e) / min a 1 ≤ ε := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    sparseRange_scale_log_power θ T 1 0 hθ hT zero_lt_one,
    sparse_quarter_scale_log θ T (ε / 6) k hθ hT (by positivity),
    uniform_inherited_error_budget θ T C (ε / 2) k hθ hT hC (by positivity)]
    with N hN hs hlog herr
  intro p hp
  dsimp only
  intro a e ha halo hahi he heB
  have hs1 : 1 ≤ scale N p := by simpa using hs p hp
  have ht : 1 ≤ scale N p ^ (1 / 4 : ℝ) := Real.one_le_rpow hs1 (by norm_num)
  have hl : 0 < Real.log N ^ k := pow_pos (Real.log_pos (by exact_mod_cast hN)) _
  have hh := stopping_window_log_error ht ha halo hahi he hl
  have h1 := mul_le_mul_of_nonneg_left (hlog p hp) (by norm_num : (0 : ℝ) ≤ 3)
  rw [← mul_div_assoc] at h1
  have h2 := herr p hp e heB
  nlinarith only [hh, h1, h2]

end MajorityDynamics.Idealized.CriticalDay
