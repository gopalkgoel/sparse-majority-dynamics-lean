import MajorityDynamics.Idealized.LinearResponse.Rates

/-!
# Range-free error budgets for the small-tilt response

The proof of `linear_response_spec` packages every analytic error as a power of
`N`, using the proportional density hypothesis only through `eventually_small`.
For a density which may move across critical windows, the natural formulation
instead keeps the three dimensionless quantities

* `sqrt p * log N ^ k`,
* `log N ^ k / sqrt (pN)`, and
* `a * log N ^ (k + 2)`, where `a = betaScale N p n * sqrt (pN)`,

explicit.  The lemmas below isolate the algebra needed to substitute such a
direct budget into the finite-tilt proof.
-/

noncomputable section

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Binomial.Approximation

/-- The scale identity used in the uniform response argument:
`p / (betaScale N p n * sqrt (pN)) <= sqrt p` whenever `sqrt (pN) >= 1`.
It has no proportional-density hypothesis. -/
theorem p_div_responseScale_le_sqrt {N : ℕ} (hN : 0 < N) (p : ℝ) (hp : 0 < p)
    (n : ℕ) (hs1 : 1 ≤ Real.sqrt (p * N)) :
    p / (betaScale N p n * Real.sqrt (p * N)) ≤ Real.sqrt p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hs : 0 < Real.sqrt (p * N) := lt_of_lt_of_le zero_lt_one hs1
  have hS₀eq : Real.sqrt (p * N) = Real.sqrt p * Real.sqrt N :=
    Real.sqrt_mul hp.le N
  have h1 : Real.sqrt (p * N) / Real.sqrt N ≤
      betaScale N p n * Real.sqrt (p * N) := by
    unfold betaScale
    rw [div_mul_eq_mul_div, ← pow_succ]
    exact div_le_div_of_nonneg_right
      (le_self_pow₀ hs1 (Nat.succ_ne_zero n)) hsqrtN.le
  have h2 : 0 < Real.sqrt (p * N) / Real.sqrt N := div_pos hs hsqrtN
  calc
    p / (betaScale N p n * Real.sqrt (p * N)) ≤
        p / (Real.sqrt (p * N) / Real.sqrt N) :=
      div_le_div_of_nonneg_left hp.le h2 h1
    _ = Real.sqrt p := by
      rw [hS₀eq, div_div_eq_mul_div, mul_div_mul_right _ _ hsqrtN.ne', Real.div_sqrt]

/-- Direct, range-free form of the normalized A.2 remainder estimate.

The finite-tilt error has shape `(p + A * a^2 * l^2) * l^k`.  After dividing
by the response signal `tau * a`, it is controlled by a budget for
`sqrt p * l^k` and a budget for `a * l^(k+2)`. -/
theorem normalized_finiteTilt_error
    {p a l A τ ε : ℝ} {k : ℕ}
    (hp : 0 ≤ p) (ha : 0 < a) (hl : 0 ≤ l) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hpa : p / a ≤ Real.sqrt p)
    (hpBudget : Real.sqrt p * l ^ k ≤ ε)
    (haBudget : a * l ^ (k + 2) ≤ ε) :
    (p + A * a ^ 2 * l ^ 2) * l ^ k / (τ * a) ≤ (1 + A) * ε := by
  have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hden : 0 < τ * a := mul_pos hτpos ha
  have hlk : 0 ≤ l ^ k := pow_nonneg hl k
  have hpa' : p * l ^ k / a ≤ ε := by
    calc
      p * l ^ k / a = (p / a) * l ^ k := by ring
      _ ≤ Real.sqrt p * l ^ k := mul_le_mul_of_nonneg_right hpa hlk
      _ ≤ ε := hpBudget
  have haa : A * a ^ 2 * l ^ 2 * l ^ k / a ≤ A * ε := by
    have ha0 : a ≠ 0 := ha.ne'
    calc
      A * a ^ 2 * l ^ 2 * l ^ k / a = A * (a * l ^ (k + 2)) := by
        rw [pow_add]
        field_simp
      _ ≤ A * ε := mul_le_mul_of_nonneg_left haBudget hA
  have hnum : (p + A * a ^ 2 * l ^ 2) * l ^ k / a ≤ (1 + A) * ε := by
    calc
      (p + A * a ^ 2 * l ^ 2) * l ^ k / a =
          p * l ^ k / a + A * a ^ 2 * l ^ 2 * l ^ k / a := by ring
      _ ≤ ε + A * ε := add_le_add hpa' haa
      _ = (1 + A) * ε := by ring
  calc
    (p + A * a ^ 2 * l ^ 2) * l ^ k / (τ * a) =
        ((p + A * a ^ 2 * l ^ 2) * l ^ k / a) / τ := by ring
    _ ≤ (p + A * a ^ 2 * l ^ 2) * l ^ k / a := by
      exact div_le_self
        (div_nonneg (mul_nonneg (add_nonneg hp (by positivity)) hlk) ha.le) hτ
    _ ≤ (1 + A) * ε := hnum

/-- A more convenient specialization in which the scale inequality is supplied
by `p_div_responseScale_le_sqrt`. -/
theorem normalized_finiteTilt_error_at_responseScale
    {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 0 < p) (n : ℕ)
    (hs1 : 1 ≤ Real.sqrt (p * N)) {l A τ ε : ℝ} {k : ℕ}
    (hl : 0 ≤ l) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hpBudget : Real.sqrt p * l ^ k ≤ ε)
    (haBudget :
      (betaScale N p n * Real.sqrt (p * N)) * l ^ (k + 2) ≤ ε) :
    (p + A * (betaScale N p n * Real.sqrt (p * N)) ^ 2 * l ^ 2) * l ^ k /
        (τ * (betaScale N p n * Real.sqrt (p * N))) ≤ (1 + A) * ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (p * N) := lt_of_lt_of_le zero_lt_one hs1
  have ha : 0 < betaScale N p n * Real.sqrt (p * N) := by
    unfold betaScale
    positivity
  exact normalized_finiteTilt_error hp.le ha hl hA hτ
    (p_div_responseScale_le_sqrt hN p hp n hs1) hpBudget haBudget

end MajorityDynamics.Idealized.LinearResponse
