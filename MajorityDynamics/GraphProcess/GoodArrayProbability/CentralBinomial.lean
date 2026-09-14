import MajorityDynamics.Probability.FixedSizeExponential.PointMass

noncomputable section

namespace MajorityDynamics.GraphProcess.GoodArrayProbability

open Binomial Binomial.Approximation
open MajorityDynamics.Probability.FixedSizeExponential

/-- The exact entropy loss is at most its elementary quadratic upper bound. -/
theorem central_log_comparison {m k : ℕ} (hk : 0 < k) (hkm : k < m)
    (q : Binomial.Probability) :
    Real.log (pointMass m k (centralProbability hk hkm)) -
      ((k : ℝ) - m * (q : ℝ)) ^ 2 / (m * (q : ℝ) * (1 - (q : ℝ))) ≤
      Real.log (pointMass m k q) := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast hk.trans hkm
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hr : 0 < ((m - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkm
  have hq := q.property.1
  have hqc := sub_pos.mpr q.property.2
  have hself : 1 - (k : ℝ) / m = ((m - k : ℕ) : ℝ) / m := by
    rw [Nat.cast_sub hkm.le]
    field_simp
  have hleft := Real.log_le_sub_one_of_pos
    (div_pos (div_pos hkR hm) hq)
  have hright := Real.log_le_sub_one_of_pos
    (div_pos (div_pos hr hm) hqc)
  rw [Real.log_div (div_pos hkR hm).ne' hq.ne'] at hleft
  rw [Real.log_div (div_pos hr hm).ne' hqc.ne'] at hright
  have hl := mul_le_mul_of_nonneg_left hleft hkR.le
  have hr' := mul_le_mul_of_nonneg_left hright hr.le
  have halg : (k : ℝ) * ((k : ℝ) / m / (q : ℝ) - 1) +
      (m - k : ℕ) * (((m - k : ℕ) : ℝ) / m / (1 - (q : ℝ)) - 1) =
      ((k : ℝ) - m * (q : ℝ)) ^ 2 / (m * (q : ℝ) * (1 - (q : ℝ))) := by
    rw [Nat.cast_sub hkm.le]
    field_simp
    ring
  rw [log_pointMass hkm.le, log_pointMass hkm.le]
  simp only [centralProbability]
  rw [hself]
  linarith

/-- A central window with a fixed sufficiently large mean lies strictly inside
the binomial support. The bound on `k` also controls its square-root prefactor. -/
theorem central_window_interior (A : ℝ) (_hA : 0 ≤ A) (m : ℕ)
    (q : Binomial.Probability) (k : ℕ) (hq : (q : ℝ) ≤ 1/2)
    (hμ : 4*A^2 + 1 ≤ (m : ℝ)*(q : ℝ))
    (hwindow : |(k : ℝ)-(m : ℝ)*(q : ℝ)| ≤
      A*Real.sqrt ((m : ℝ)*(q : ℝ))) :
    0 < k ∧ k < m ∧ (k : ℝ) ≤ 2*((m : ℝ)*(q : ℝ)) := by
  let μ : ℝ := m * (q : ℝ)
  have hμpos : 0 < μ := by dsimp [μ]; nlinarith [sq_nonneg A]
  have hsqrt := Real.sq_sqrt hμpos.le
  have hsqrt0 := Real.sqrt_nonneg μ
  have hsmall : A * Real.sqrt μ ≤ μ / 2 := by
    have : 4*A^2 ≤ μ := by dsimp [μ]; linarith
    nlinarith [sq_nonneg (Real.sqrt μ - 2*A)]
  have hbounds := abs_le.mp hwindow
  change - (A * Real.sqrt μ) ≤ (k : ℝ) - μ ∧
    (k : ℝ) - μ ≤ A * Real.sqrt μ at hbounds
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmean : 2*μ ≤ (m : ℝ) := by dsimp [μ]; nlinarith
  have hkpos : 0 < (k : ℝ) := by linarith
  have hklt : (k : ℝ) < m := by linarith
  exact ⟨by exact_mod_cast hkpos, by exact_mod_cast hklt, by dsimp [μ] at *; linarith⟩

/-- A uniform central-window lower bound for the actual binomial singleton mass.
The constants depend only on the window width; the support restrictions are
consequences, not hypotheses. -/
theorem central_binomial_lower (A : ℝ) (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 1 ≤ L ∧
      ∀ (m : ℕ) (q : Binomial.Probability) (k : ℕ),
      (q : ℝ) ≤ 1/2 → L ≤ (m : ℝ)*(q : ℝ) →
      |(k : ℝ)-(m : ℝ)*(q : ℝ)| ≤ A*Real.sqrt ((m : ℝ)*(q : ℝ)) →
      c / Real.sqrt ((m : ℝ)*(q : ℝ)) ≤ pointMass m k q := by
  refine ⟨centralAtomConstant * Real.exp (-2*A^2) / 2, by
    exact div_pos (mul_pos centralAtomConstant_pos (Real.exp_pos _)) (by norm_num),
    4*A^2+1, by nlinarith [sq_nonneg A], ?_⟩
  intro m q k hq hμ hwindow
  obtain ⟨hk, hkm, hkbound⟩ := central_window_interior A hA m q k hq hμ hwindow
  let μ : ℝ := m * (q : ℝ)
  have hμpos : 0 < μ := by dsimp [μ]; nlinarith [sq_nonneg A]
  have hsqrt := Real.sq_sqrt hμpos.le
  have hsqrtpos := Real.sqrt_pos.mpr hμpos
  have hsquare : ((k : ℝ)-μ)^2 ≤ A^2*μ := by
    have hsq := sq_le_sq₀ (abs_nonneg ((k : ℝ)-μ))
      (mul_nonneg hA (Real.sqrt_nonneg μ)) |>.mpr hwindow
    rw [sq_abs, mul_pow, hsqrt] at hsq
    exact hsq
  have hqc : 0 < 1-(q : ℝ) := sub_pos.mpr q.property.2
  have hloss : ((k : ℝ)-μ)^2 / (μ*(1-(q : ℝ))) ≤ 2*A^2 := by
    apply (div_le_iff₀ (mul_pos hμpos hqc)).mpr
    have hhalf : 1/2 ≤ 1-(q : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left hhalf (mul_nonneg (sq_nonneg A) hμpos.le)
    nlinarith
  have hlog : Real.log (pointMass m k (centralProbability hk hkm)) - 2*A^2 ≤
      Real.log (pointMass m k q) := by
    have := central_log_comparison hk hkm q
    change Real.log (pointMass m k (centralProbability hk hkm)) -
      ((k : ℝ)-μ)^2 / (μ*(1-(q : ℝ))) ≤ _ at this
    linarith
  have hcompare : pointMass m k (centralProbability hk hkm) * Real.exp (-2*A^2) ≤
      pointMass m k q := by
    have := Real.exp_le_exp.mpr hlog
    rw [Real.exp_sub, Real.exp_log (pointMass_pos hkm.le _),
      Real.exp_log (pointMass_pos hkm.le _)] at this
    simpa [Real.exp_neg, div_eq_mul_inv] using this
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkroot : Real.sqrt (k : ℝ) ≤ 2*Real.sqrt μ := by
    have hksq := Real.sq_sqrt hkR.le
    have hknonneg := Real.sqrt_nonneg (k : ℝ)
    change (k : ℝ) ≤ 2*μ at hkbound
    nlinarith
  have hself : centralAtomConstant / (2*Real.sqrt μ) ≤
      pointMass m k (centralProbability hk hkm) := by
    exact (div_le_div_of_nonneg_left centralAtomConstant_pos.le
      (Real.sqrt_pos.mpr hkR) hkroot).trans
      (central_binomial_point_mass_lower hk hkm)
  have := mul_le_mul_of_nonneg_right hself (Real.exp_pos (-2*A^2)).le
  calc
    (centralAtomConstant * Real.exp (-2*A^2) / 2) / Real.sqrt μ =
        (centralAtomConstant / (2*Real.sqrt μ)) * Real.exp (-2*A^2) := by ring
    _ ≤ pointMass m k (centralProbability hk hkm) * Real.exp (-2*A^2) := this
    _ ≤ pointMass m k q := hcompare

end MajorityDynamics.GraphProcess.GoodArrayProbability
