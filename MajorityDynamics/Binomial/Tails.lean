import MajorityDynamics.Binomial.Basic
import MajorityDynamics.Literature.BinomialChernoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Binomial truncation bounds from the cited scalar Chernoff inequality -/

noncomputable section
open MeasureTheory Set

namespace MajorityDynamics.Binomial

theorem two_sided_tail (m : ℕ) (q : Probability) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    (ProbabilityTheory.binomial m (closedProbability q)).real
      {k : ℕ | t ≤ |(k : ℝ) - (m : ℝ) * (q : ℝ)|} ≤
        2 * Real.exp (-(t ^ 2) / (2 * ((m : ℝ) * (q : ℝ)) + 2 * t / 3)) := by
  have hμ : 0 < (m : ℝ) * (q : ℝ) := mul_pos (by exact_mod_cast hm) q.property.1
  obtain ⟨hu, hl⟩ := Literature.binomial_chernoff m (closedProbability q) hμ t ht
  have hd : 0 < 2 * ((m : ℝ) * (q : ℝ)) := by positivity
  have hl' : Real.exp (-(t ^ 2) / (2 * ((m : ℝ) * (q : ℝ)))) ≤
      Real.exp (-(t ^ 2) / (2 * ((m : ℝ) * (q : ℝ)) + 2 * t / 3)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (sq_nonneg t) hd (by linarith)
  have hevent : {k : ℕ | t ≤ |(k : ℝ) - (m : ℝ) * (q : ℝ)|} =
      {k : ℕ | (m : ℝ) * (q : ℝ) + t ≤ (k : ℝ)} ∪
        {k : ℕ | (k : ℝ) ≤ (m : ℝ) * (q : ℝ) - t} := by
    ext k
    simp only [mem_ofPred_eq, mem_union, le_abs]
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; linarith
      · right; linarith
  rw [hevent]
  apply (measureReal_union_le _ _).trans
  have h := add_le_add hu (hl.trans hl')
  simpa only [closedProbability, ← two_mul] using h

/-- A displaced reference center loses half the radius. -/
theorem centered_tail (m : ℕ) (q : Probability) (hm : 0 < m) (c R : ℝ)
    (hR : 0 ≤ R) (hcenter : |(m : ℝ) * (q : ℝ) - c| ≤ R / 2) :
    (ProbabilityTheory.binomial m (closedProbability q)).real
      {k : ℕ | R ≤ |(k : ℝ) - c|} ≤
        2 * Real.exp (-((R / 2) ^ 2) / (2 * ((m : ℝ) * (q : ℝ)) + R / 3)) := by
  have hsub : {k : ℕ | R ≤ |(k : ℝ) - c|} ⊆
      {k : ℕ | R / 2 ≤ |(k : ℝ) - (m : ℝ) * (q : ℝ)|} := by
    intro k hk
    have htri := abs_sub_le (k : ℝ) ((m : ℝ) * (q : ℝ)) c
    change R ≤ |(k : ℝ) - c| at hk
    change R / 2 ≤ |(k : ℝ) - (m : ℝ) * (q : ℝ)|
    linarith
  apply (measureReal_mono hsub).trans
  simpa only [show 2 * (R / 2) / 3 = R / 3 by ring] using
    two_sided_tail m q hm (R / 2) (by positivity)

/-- Polynomial observables can be truncated by a deterministic bound and
the probability of the discarded event. -/
theorem tail_moment_le (m : ℕ) (q : Probability) (f : ℕ → ℝ) (E : Set ℕ)
    (H : ℝ) (_hH : 0 ≤ H) (hf : ∀ k ∈ E, |f k| ≤ H) :
    |∫ k in E, f k ∂ProbabilityTheory.binomial m (closedProbability q)| ≤
      H * (ProbabilityTheory.binomial m (closedProbability q)).real E := by
  have hE : MeasurableSet E := Set.to_countable E |>.measurableSet
  have hfi := ProbabilityTheory.integrable_binomial (n := m) (p := closedProbability q) f
  calc
    _ ≤ ∫ k in E, |f k| ∂ProbabilityTheory.binomial m (closedProbability q) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _k in E, H ∂ProbabilityTheory.binomial m (closedProbability q) := by
      apply integral_mono_ae hfi.abs.integrableOn (integrable_const H)
      filter_upwards [ae_restrict_mem hE] with k hk
      exact hf k hk
    _ = _ := by rw [setIntegral_const]; simp [smul_eq_mul, mul_comm]

/-- On a standard-deviation-sized logarithmic window, the discarded mass
has a Gaussian-in-logarithm bound, uniformly in all binomial parameters. -/
theorem centered_tail_scaled (m : ℕ) (q : Probability) (hm : 0 < m)
    (c s l C : ℝ) (hs : 0 < s) (hl : 0 ≤ l) (hC : 0 < C)
    (hcenter : |(m : ℝ) * (q : ℝ) - c| ≤ s * l / 2)
    (hmean : (m : ℝ) * (q : ℝ) ≤ C * s ^ 2) (hlscale : l ≤ s) :
    (ProbabilityTheory.binomial m (closedProbability q)).real
      {k : ℕ | s * l ≤ |(k : ℝ) - c|} ≤
        2 * Real.exp (-(l ^ 2) / (8 * C + 4)) := by
  apply (centered_tail m q hm c (s * l) (mul_nonneg hs.le hl) hcenter).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div]
  apply neg_le_neg
  have hμ : 0 < (m : ℝ) * (q : ℝ) := mul_pos (by exact_mod_cast hm) q.property.1
  have hd : 0 < 2 * ((m : ℝ) * (q : ℝ)) + s * l / 3 := by positivity
  have hden : 2 * ((m : ℝ) * (q : ℝ)) + s * l / 3 ≤ (2 * C + 1) * s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlscale hs.le]
  have hratio := div_le_div_of_nonneg_left (sq_nonneg (s * l / 2)) hd hden
  have heq : (s * l / 2) ^ 2 / ((2 * C + 1) * s ^ 2) = l ^ 2 / (8 * C + 4) := by
    field_simp
    ring
  rwa [heq] at hratio

end MajorityDynamics.Binomial
