import MajorityDynamics.Binomial.StirlingEstimate
import MajorityDynamics.Analysis.DiscreteApproximation

/-! # Uniform point estimates on a real-centered lattice window

We compare consecutive point probabilities, choosing the common normalizer at
the floor of the center. This avoids a separate asymptotic theorem for Gamma
at real arguments: its positive value is absorbed in the free normalizer.
-/

noncomputable section

namespace MajorityDynamics.Binomial.Approximation
open Analysis

theorem pointMass_pos {m k : ℕ} (hkm : k ≤ m) (q : Probability) : 0 < pointMass m k q := by
  rw [pointMass, ProbabilityTheory.binomial_real_singleton]
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm
  exact mul_pos (mul_pos hc (pow_pos q.property.1 _))
    (pow_pos (sub_pos.mpr q.property.2) _)

theorem log_pointMass {m k : ℕ} (hkm : k ≤ m) (q : Probability) :
    Real.log (pointMass m k q) = Real.log (m.factorial : ℝ) -
      Real.log (k.factorial : ℝ) - Real.log ((m - k).factorial : ℝ) +
      k * Real.log (q : ℝ) + (m - k : ℕ) * Real.log (1 - (q : ℝ)) := by
  rw [pointMass, ProbabilityTheory.binomial_real_singleton]
  change Real.log ((m.choose k : ℝ) * (q : ℝ) ^ k * (1 - (q : ℝ)) ^ (m - k)) = _
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm
  have hp := q.property.1
  have hpc := sub_pos.mpr q.property.2
  rw [Real.log_mul (mul_pos hc (pow_pos hp _)).ne' (pow_pos hpc _).ne',
    Real.log_mul hc.ne' (pow_pos hp _).ne', Real.log_pow, Real.log_pow,
    Nat.cast_choose ℝ hkm, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem log_pointMass_succ {m k : ℕ} (hkm : k < m) (q : Probability) :
    Real.log (pointMass m (k + 1) q) - Real.log (pointMass m k q) =
      Real.log ((m : ℝ) - k) - Real.log ((k : ℝ) + 1) + logOdds q := by
  have hs : m - k = (m - (k + 1)) + 1 := by omega
  have hfac (j : ℕ) : Real.log ((j + 1).factorial : ℝ) =
      Real.log ((j : ℝ) + 1) + Real.log (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.log_mul (by positivity) (by positivity)]
  rw [log_pointMass (by omega) q, log_pointMass hkm.le q, hfac k]
  have hr : Real.log ((m - k).factorial : ℝ) =
      Real.log ((m : ℝ) - k) + Real.log ((m - (k + 1)).factorial : ℝ) := by
    rw [hs, hfac]
    congr 2
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  rw [hr, Nat.cast_sub (by omega), Nat.cast_sub hkm.le, Nat.cast_add, Nat.cast_one]
  dsimp [logOdds]
  ring

def windowSlope (m : ℕ) (μ : ℝ) (q : Probability) : ℝ :=
  (q : ℝ) * ((m : ℝ) - μ) / ((1 - (q : ℝ)) * μ)

theorem windowSlope_pos {m : ℕ} {μ : ℝ} (hμ : 0 < μ) (hm : μ < m)
    (q : Probability) : 0 < windowSlope m μ q :=
  div_pos (mul_pos q.property.1 (sub_pos.mpr hm))
    (mul_pos (sub_pos.mpr q.property.2) hμ)

theorem log_windowSlope {m : ℕ} {μ : ℝ} (hμ : 0 < μ) (hm : μ < m)
    (q : Probability) : Real.log (windowSlope m μ q) =
      logOdds q + Real.log ((m : ℝ) - μ) - Real.log μ := by
  rw [windowSlope, Real.log_div (mul_pos q.property.1 (sub_pos.mpr hm)).ne'
    (mul_pos (sub_pos.mpr q.property.2) hμ).ne',
    Real.log_mul q.property.1.ne' (sub_pos.mpr hm).ne',
    Real.log_mul (sub_pos.mpr q.property.2).ne' hμ.ne']
  dsimp [logOdds]
  ring

def firstShape (μ κ : ℝ) (k : ℕ) : ℝ :=
  κ ^ ((k : ℝ) - μ) * (factorial μ * μ ^ ((k : ℝ) - μ) / factorial k)

theorem firstShape_pos {μ κ : ℝ} (hμ : 0 < μ) (hκ : 0 < κ) (k : ℕ) :
    0 < firstShape μ κ k := by
  have hΓ := Real.Gamma_pos_of_pos (show 0 < μ + 1 by linarith)
  dsimp [firstShape, factorial]
  exact mul_pos (Real.rpow_pos_of_pos hκ _) (div_pos
    (mul_pos hΓ (Real.rpow_pos_of_pos hμ _))
    (Real.Gamma_pos_of_pos (by positivity)))

theorem log_firstShape {μ κ : ℝ} (hμ : 0 < μ) (hκ : 0 < κ) (k : ℕ) :
    Real.log (firstShape μ κ k) =
      ((k : ℝ) - μ) * (Real.log κ + Real.log μ) + Real.log (factorial μ) -
        Real.log (k.factorial : ℝ) := by
  have hΓ : 0 < factorial μ := Real.Gamma_pos_of_pos (by linarith)
  have hk : 0 < factorial k := Real.Gamma_pos_of_pos (by positivity)
  rw [firstShape, Real.log_mul (Real.rpow_pos_of_pos hκ _).ne'
    (div_pos (mul_pos hΓ (Real.rpow_pos_of_pos hμ _)) hk).ne',
    Real.log_div (mul_pos hΓ (Real.rpow_pos_of_pos hμ _)).ne' hk.ne',
    Real.log_mul hΓ.ne' (Real.rpow_pos_of_pos hμ _).ne',
    Real.log_rpow hκ, Real.log_rpow hμ,
    show factorial k = (k.factorial : ℝ) from Real.Gamma_nat_eq_factorial k]
  ring

theorem log_firstShape_succ {μ κ : ℝ} (hμ : 0 < μ) (hκ : 0 < κ) (k : ℕ) :
    Real.log (firstShape μ κ (k + 1)) - Real.log (firstShape μ κ k) =
      Real.log κ + Real.log μ - Real.log ((k : ℝ) + 1) := by
  rw [log_firstShape hμ hκ, log_firstShape hμ hκ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem complement_log_error {m k : ℕ} {μ L : ℝ}
    (_hL : 0 ≤ L) (hm : 0 < (m : ℝ) - μ) (hsmall : L ≤ ((m : ℝ) - μ) / 2)
    (hk : |(k : ℝ) - μ| ≤ L) :
    |Real.log ((m : ℝ) - k) - Real.log ((m : ℝ) - μ)| ≤ 2 * L / ((m : ℝ) - μ) := by
  have hx : |(μ - k) / ((m : ℝ) - μ)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hm, abs_sub_comm]
    apply (div_le_iff₀ hm).mpr
    linarith
  have hmk : 0 < (m : ℝ) - k := by
    have := (abs_le.mp hk).2
    linarith
  have hlog : Real.log ((m : ℝ) - k) - Real.log ((m : ℝ) - μ) =
      Real.log (1 + (μ - k) / ((m : ℝ) - μ)) := by
    rw [← Real.log_div hmk.ne' hm.ne']
    congr 1
    field_simp
    ring
  rw [hlog]
  apply (abs_log_one_add_le hx).trans
  rw [abs_div, abs_of_pos hm, abs_sub_comm]
  exact (mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hm).mpr hk)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

theorem first_window_estimate (m : ℕ) (μ L : ℝ) (q : Probability)
    (hμ : 0 < μ) (hm : μ < m) (hL : 1 ≤ L)
    (hcomp : L ≤ ((m : ℝ) - μ) / 2)
    (hsmall : 4 * L ^ 2 / ((m : ℝ) - μ) ≤ 1) :
    ∃ N : ℝ, 0 < N ∧ ∀ k : ℕ, |(k : ℝ) - μ| ≤ L →
      |pointMass m k q - N * firstShape μ (windowSlope m μ q) k| ≤
        (8 * L ^ 2 / ((m : ℝ) - μ)) * |N * firstShape μ (windowSlope m μ q) k| := by
  have hd : 0 < (m : ℝ) - μ := sub_pos.mpr hm
  have hL0 : 0 ≤ L := by linarith
  have hκ := windowSlope_pos hμ hm q
  have hinside (k : ℕ) (hk : |(k : ℝ) - μ| ≤ L) : k < m := by
    have := (abs_le.mp hk).2
    have : (k : ℝ) < m := by linarith
    exact_mod_cast this
  obtain ⟨N, hN, hNerr⟩ := window_relative_error (fun k => pointMass m k q)
    (firstShape μ (windowSlope m μ q)) μ L (2 * L / ((m : ℝ) - μ)) hμ.le hL
    (by positivity) (by convert hsmall using 1; ring)
    (fun k hk => pointMass_pos (hinside k hk).le q)
    (fun k _ => firstShape_pos hμ hκ k) (by
      intro k hk _
      have heq : (Real.log (pointMass m (k + 1) q) -
          Real.log (firstShape μ (windowSlope m μ q) (k + 1))) -
          (Real.log (pointMass m k q) - Real.log (firstShape μ (windowSlope m μ q) k)) =
          Real.log ((m : ℝ) - k) - Real.log ((m : ℝ) - μ) := by
        have h1 := log_pointMass_succ (hinside k hk) q
        have h2 := log_firstShape_succ hμ hκ k
        rw [log_windowSlope hμ hm q] at h2
        linarith
      rw [heq]
      exact complement_log_error hL0 hd hcomp hk)
  refine ⟨N, hN, ?_⟩
  intro k hk
  convert hNerr k hk using 1
  ring

def gaussianShape (μ κ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(((k : ℝ) - μ - μ * Real.log κ) ^ 2) / (2 * μ))

theorem log_gaussianShape_succ {μ κ : ℝ} (hμ : μ ≠ 0) (k : ℕ) :
    Real.log (gaussianShape μ κ (k + 1)) - Real.log (gaussianShape μ κ k) =
      Real.log κ - ((k : ℝ) - μ + 1 / 2) / μ := by
  simp only [gaussianShape, Real.log_exp, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem success_log_error {k : ℕ} {μ L : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (hsmall : L ≤ μ / 2) (hk : |((k + 1 : ℕ) : ℝ) - μ| ≤ L) :
    |Real.log ((k : ℝ) + 1) - Real.log μ - (((k : ℝ) + 1 - μ) / μ)| ≤
      2 * (L / μ) ^ 2 := by
  have hx : |((k : ℝ) + 1 - μ) / μ| ≤ L / μ := by
    rw [abs_div, abs_of_pos hμ]
    exact (div_le_div_iff_of_pos_right hμ).mpr (by simpa only [Nat.cast_add, Nat.cast_one] using hk)
  have hhalf : L / μ ≤ 1 / 2 := (div_le_iff₀ hμ).mpr (by linarith)
  have hlog : Real.log ((k : ℝ) + 1) - Real.log μ =
      Real.log (1 + ((k : ℝ) + 1 - μ) / μ) := by
    rw [← Real.log_div (by positivity) hμ.ne']
    congr 1
    field_simp
    ring
  rw [hlog]
  apply (log_one_add_linear_error (hx.trans hhalf)).trans
  have := div_nonneg hL hμ.le
  have hsq := mul_self_le_mul_self (abs_nonneg (((k : ℝ) + 1 - μ) / μ)) hx
  nlinarith [sq_abs (((k : ℝ) + 1 - μ) / μ)]

def gaussianStepError (m : ℕ) (μ L : ℝ) : ℝ :=
  2 * L / ((m : ℝ) - μ) + 2 * (L / μ) ^ 2 + 1 / (2 * μ)

/-- Consecutive logarithmic discrepancy from the matching Gaussian shape. -/
theorem gaussian_log_step_error (m : ℕ) (μ L : ℝ) (q : Probability)
    (hμ : 0 < μ) (hm : μ < m) (hL0 : 0 ≤ L)
    (hcomp : L ≤ ((m : ℝ) - μ) / 2) (hsucc : L ≤ μ / 2)
    (k : ℕ) (hk : |(k : ℝ) - μ| ≤ L) (hk1 : |(k + 1 : ℕ) - μ| ≤ L) :
    |(Real.log (pointMass m (k + 1) q) - Real.log (gaussianShape μ (windowSlope m μ q) (k + 1))) -
      (Real.log (pointMass m k q) - Real.log (gaussianShape μ (windowSlope m μ q) k))| ≤
        gaussianStepError m μ L := by
  have hd : 0 < (m : ℝ) - μ := sub_pos.mpr hm
  have hkb := (abs_le.mp hk).2
  have hkm : k < m := by exact_mod_cast (show (k : ℝ) < m by linarith)
  have heq : (Real.log (pointMass m (k + 1) q) -
      Real.log (gaussianShape μ (windowSlope m μ q) (k + 1))) -
      (Real.log (pointMass m k q) - Real.log (gaussianShape μ (windowSlope m μ q) k)) =
      (Real.log ((m : ℝ) - k) - Real.log ((m : ℝ) - μ)) -
      (Real.log ((k : ℝ) + 1) - Real.log μ - (((k : ℝ) + 1 - μ) / μ)) - 1 / (2 * μ) := by
    have h1 := log_pointMass_succ hkm q
    have h2 := log_gaussianShape_succ (κ := windowSlope m μ q) hμ.ne' k
    rw [log_windowSlope hμ hm q] at h2
    have he : ((k : ℝ) - μ + 1 / 2) / μ = ((k : ℝ) + 1 - μ) / μ - 1 / (2 * μ) := by ring
    rw [he] at h2
    linarith
  rw [heq]
  calc
    _ ≤ |Real.log ((m : ℝ) - k) - Real.log ((m : ℝ) - μ)| +
        |Real.log ((k : ℝ) + 1) - Real.log μ - (((k : ℝ) + 1 - μ) / μ)| + |1 / (2 * μ)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ gaussianStepError m μ L := by
      rw [abs_of_pos (by positivity : 0 < 1 / (2 * μ))]
      exact add_le_add (add_le_add (complement_log_error hL0 hd hcomp hk)
        (success_log_error hμ hL0 hsucc hk1)) le_rfl

theorem gaussian_window_estimate (m : ℕ) (μ L : ℝ) (q : Probability)
    (hμ : 0 < μ) (hm : μ < m) (hL : 1 ≤ L)
    (hcomp : L ≤ ((m : ℝ) - μ) / 2) (hsucc : L ≤ μ / 2)
    (hsmall : 2 * L * gaussianStepError m μ L ≤ 1) :
    ∃ N : ℝ, 0 < N ∧ ∀ k : ℕ, |(k : ℝ) - μ| ≤ L →
      |pointMass m k q - N * gaussianShape μ (windowSlope m μ q) k| ≤
        (4 * L * gaussianStepError m μ L) * |N * gaussianShape μ (windowSlope m μ q) k| := by
  have hd : 0 < (m : ℝ) - μ := sub_pos.mpr hm
  have hL0 : 0 ≤ L := by linarith
  apply window_relative_error _ _ μ L _ hμ.le hL (by unfold gaussianStepError; positivity) hsmall
  · intro k hk
    have hkb := (abs_le.mp hk).2
    have hkm : k ≤ m := by exact_mod_cast (show (k : ℝ) ≤ m by linarith)
    exact pointMass_pos hkm q
  · intro k _
    exact Real.exp_pos _
  · exact gaussian_log_step_error m μ L q hμ hm hL0 hcomp hsucc

end MajorityDynamics.Binomial.Approximation
