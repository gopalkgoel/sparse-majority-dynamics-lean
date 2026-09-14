import MajorityDynamics.Probability.FixedSizeExponential.Main
import MajorityDynamics.Literature.BinomialChernoff

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

/-- Literal hypergeometric atom; all coefficients are cast before division. -/
def hypergeomMass (M H d t : ℕ) : ℝ :=
  (H.choose t : ℝ) * ((M-H).choose (d-t) : ℝ) / (M.choose d : ℝ)

theorem hypergeomMass_nonneg (M H d t : ℕ) : 0 ≤ hypergeomMass M H d t := by
  unfold hypergeomMass
  positivity

theorem hypergeomMass_zero_left {M H d t : ℕ} (ht : H < t) :
    hypergeomMass M H d t = 0 := by
  simp [hypergeomMass, Nat.choose_eq_zero_of_lt ht]

theorem hypergeomMass_zero_right {M H d t : ℕ} (ht : M-H < d-t) :
    hypergeomMass M H d t = 0 := by
  simp [hypergeomMass, Nat.choose_eq_zero_of_lt ht]

/-- Exact Bernoulli atom factorization, before any estimate. -/
theorem hypergeomMass_mul_binomial {M H d t : ℕ} (hH : H ≤ M)
    (hd : d ≤ M) (htd : t ≤ d) (htH : t ≤ H) (hrest : d-t ≤ M-H)
    (q : unitInterval) :
    hypergeomMass M H d t * (binomial M q).real {d} =
      (binomial H q).real {t} * (binomial (M-H) q).real {d-t} := by
  have hc : (M.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hd).ne'
  have hpow : M-d = (H-t) + (M-H-(d-t)) := by omega
  have hdadd : d = t + (d-t) := by omega
  simp only [hypergeomMass, binomial_real_singleton]
  rw [hpow, pow_add, show (q : ℝ)^d = q^t*q^(d-t) by rw [← pow_add, ← hdadd]]
  field_simp [hc]

/-- A singleton binomial mass is controlled by its nearer one-sided tail. -/
theorem binomial_atom_chernoff {H t : ℕ} (q : unitInterval)
    (hμ : 0 < (H : ℝ) * q) :
    (binomial H q).real {t} ≤
      Real.exp (-((|(t : ℝ) - H*q|)^2) /
        (2 * ((H : ℝ)*q) + 2*|(t : ℝ)-H*q|/3)) := by
  let μ : ℝ := H*q
  let r : ℝ := |(t : ℝ)-μ|
  have hr : 0 ≤ r := abs_nonneg _
  obtain ⟨hu,hl⟩ := Literature.binomial_chernoff H q hμ r hr
  by_cases ht : μ ≤ (t : ℝ)
  · have heq : μ+r = t := by dsimp [r]; rw [abs_of_nonneg (sub_nonneg.mpr ht)]; ring
    exact (measureReal_mono (by intro k hk; rw [Set.mem_singleton_iff.mp hk]; exact heq.le) ).trans hu
  · have ht' : (t : ℝ) ≤ μ := le_of_not_ge ht
    have heq : μ-r = t := by dsimp [r]; rw [abs_of_nonpos (sub_nonpos.mpr ht')]; ring
    have hatom : (binomial H q).real {t} ≤ Real.exp (-(r^2)/(2*μ)) :=
      (measureReal_mono (by intro k hk; rw [Set.mem_singleton_iff.mp hk]; exact heq.ge)).trans hl
    apply hatom.trans
    apply Real.exp_le_exp.mpr
    have hden : 0 < 2*μ := by dsimp [μ]; positivity
    apply (div_le_div_iff₀ hden (by linarith : 0 < 2*μ+2*r/3)).mpr
    nlinarith [mul_nonneg (sq_nonneg r) hr]

/-- Finite hypergeometric Chernoff bound obtained by conditioning on the central
Bernoulli total. No without-replacement concentration result is imported. -/
theorem hypergeomMass_chernoff {M H d t : ℕ} (hH : H ≤ M)
    (hd0 : 0 < d) (hdM : d < M) (htd : t ≤ d) (hH0 : 0 < H) :
    hypergeomMass M H d t ≤
      Real.sqrt (d : ℝ) / centralAtomConstant *
      Real.exp (-((|(t : ℝ) - (H : ℝ)*((d : ℝ)/M)|)^2) /
        (2*((H : ℝ)*((d : ℝ)/M)) + 2*|(t : ℝ)-(H : ℝ)*((d : ℝ)/M)|/3)) := by
  by_cases htH : t ≤ H
  swap
  · rw [hypergeomMass_zero_left (by omega)]
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) centralAtomConstant_pos.le) (Real.exp_pos _).le
  by_cases hrest : d-t ≤ M-H
  swap
  · rw [hypergeomMass_zero_right (by omega)]
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) centralAtomConstant_pos.le) (Real.exp_pos _).le
  let q := centralProbability hd0 hdM
  have hq : 0 < (H : ℝ) * (closedProbability q : ℝ) := by
    have : 0 < (H : ℝ) := by exact_mod_cast hH0
    exact mul_pos this q.property.1
  have hatom := binomial_atom_chernoff (t := t) (closedProbability q) hq
  have hsplit := hypergeomMass_mul_binomial hH hdM.le htd htH hrest (closedProbability q)
  have hsecond : (binomial (M-H) (closedProbability q)).real {d-t} ≤ 1 := measureReal_le_one
  have hmass : 0 ≤ (binomial H (closedProbability q)).real {t} := measureReal_nonneg
  have hprod : hypergeomMass M H d t * (binomial M (closedProbability q)).real {d} ≤
      (binomial H (closedProbability q)).real {t} := by
    rw [hsplit]
    exact mul_le_of_le_one_right hmass hsecond
  have hcentral := central_binomial_point_mass_lower hd0 hdM
  change centralAtomConstant / Real.sqrt (d : ℝ) ≤
    (binomial M (closedProbability q)).real {d} at hcentral
  have hbound := (mul_le_mul_of_nonneg_left hcentral (hypergeomMass_nonneg M H d t)).trans hprod
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd0)
  have hc := centralAtomConstant_pos
  have hbound' := hbound.trans hatom
  change hypergeomMass M H d t * (centralAtomConstant / Real.sqrt (d : ℝ)) ≤ _ at hbound'
  apply (le_div_iff₀ (div_pos hc hsd)).mpr at hbound'
  dsimp [q, centralProbability, closedProbability] at hbound'
  have heq (E : ℝ) : E / (centralAtomConstant / Real.sqrt (d : ℝ)) =
      Real.sqrt (d : ℝ) / centralAtomConstant * E := by field_simp
  rwa [heq] at hbound'

end MajorityDynamics.Probability.HypergeometricTiltTail
