import MajorityDynamics.Probability.FixedSizeExponential.Basic
import MajorityDynamics.Binomial.WindowPointEstimate

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The central conditioning atom

The Bernoulli comparison loses the probability of the event that the total is
`s`.  This file proves the needed *point-mass* lower bound from the checked
Stirling estimate already present in `Binomial/StirlingEstimate.lean`; no tail
bound or unproved local-limit theorem is used.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace MajorityDynamics.Probability.FixedSizeExponential

open MajorityDynamics.Binomial MajorityDynamics.Binomial.Approximation

/-- The positive constant retained in the central atom estimate. -/
def centralAtomConstant : ℝ :=
  Real.exp (-1 - Real.log 2 - (1 / 2 : ℝ) * Real.log 2)

theorem centralAtomConstant_pos : 0 < centralAtomConstant := by
  unfold centralAtomConstant
  positivity

/-- The self-centered Bernoulli parameter, with both endpoint restrictions proved. -/
def centralProbability {n s : ℕ} (hs0 : 0 < s) (hsn : s < n) : SuccessProbability :=
  ⟨(s : ℝ) / n,
    div_pos (by exact_mod_cast hs0) (by exact_mod_cast hs0.trans hsn),
    (div_lt_one (by exact_mod_cast hs0.trans hsn : (0 : ℝ) < n)).mpr
      (by exact_mod_cast hsn)⟩

/-- Exact cancellation of the entropy terms at q=s/n. -/
theorem binomialLogMain_self {n s : ℕ} (hs0 : 0 < s) (hsn : s < n) :
    binomialLogMain n s (centralProbability hs0 hsn) =
      -Real.log (Real.sqrt Real.pi) +
        (1 / 2 : ℝ) *
          (Real.log (2 * (n : ℝ)) - Real.log (2 * (s : ℝ)) -
            Real.log (2 * (n - s : ℕ))) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast hs0.trans hsn
  have hs : 0 < (s : ℝ) := by exact_mod_cast hs0
  have hr : 0 < ((n - s : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hsn
  have hq1 : 1 - (s : ℝ) / n = ((n - s : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hsn.le]
    field_simp
  simp only [binomialLogMain, stirlingMain, centralProbability]
  rw [hq1, Real.log_div hs.ne' hn.ne', Real.log_div hr.ne' hn.ne',
    Real.log_div hn.ne' (Real.exp_pos 1).ne',
    Real.log_div hs.ne' (Real.exp_pos 1).ne',
    Real.log_div hr.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Nat.cast_sub hsn.le]
  ring

/-- A central point-mass lower bound, with a universal positive constant. -/
theorem central_binomial_point_mass_lower {n s : ℕ} (hs0 : 0 < s)
    (hsn : s < n) :
    centralAtomConstant / Real.sqrt (s : ℝ) ≤
      pointMass n s (centralProbability hs0 hsn) := by
  let q := centralProbability hs0 hsn
  have hn : 0 < (n : ℝ) := by exact_mod_cast (lt_trans hs0 hsn)
  have hs : 0 < (s : ℝ) := by exact_mod_cast hs0
  have hr : 0 < ((n - s : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hsn)
  have hpi : Real.sqrt Real.pi ≤ 2 := by
    have hsq : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hnonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
    nlinarith [Real.pi_le_four]
  have hlogpi : Real.log (Real.sqrt Real.pi) ≤ Real.log 2 :=
    Real.log_le_log (Real.sqrt_pos.mpr Real.pi_pos) hpi
  have hlogratio :
      0 ≤ Real.log (2 * (n : ℝ)) - Real.log (2 * ((n - s : ℕ) : ℝ)) := by
    apply sub_nonneg.mpr
    apply Real.log_le_log
    · positivity
    · have hsub : ((n - s : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n s
      linarith
  have hmain :
      -Real.log 2 - (1 / 2 : ℝ) * Real.log (2 * (s : ℝ)) ≤
        binomialLogMain n s q := by
    change _ ≤ binomialLogMain n s (centralProbability hs0 hsn)
    rw [binomialLogMain_self hs0 hsn]
    linarith
  have herr := log_pointMass_error (m := n) (k := s) hs0 hsn q
  have herr' :
      |Real.log (pointMass n s q) - binomialLogMain n s q| ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr (lt_trans hs0 hsn))
    have hr1 : (1 : ℝ) ≤ (n - s : ℕ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hsn))
    have hsn1 : (1 : ℝ) ≤ s := by exact_mod_cast (Nat.succ_le_iff.mpr hs0)
    have h1 : (1 : ℝ) / (12 * n) ≤ 1 / 12 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have h2 : (1 : ℝ) / (12 * s) ≤ 1 / 12 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have h3 : (1 : ℝ) / (12 * (n - s : ℕ)) ≤ 1 / 12 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have hlog :
      -1 - Real.log 2 - (1 / 2 : ℝ) * Real.log (2 * (s : ℝ)) ≤
        Real.log (pointMass n s q) := by
    have hpm := (abs_le.mp herr').1
    linarith
  have hpmpos : 0 < pointMass n s q := pointMass_pos hsn.le q
  have hexp :
      Real.exp (-1 - Real.log 2 - (1 / 2 : ℝ) * Real.log (2 * (s : ℝ))) ≤
        pointMass n s q := by
    rw [← Real.exp_log hpmpos]
    exact Real.exp_le_exp.mpr hlog
  have hsqrt : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hs
  have hlogsqrt : Real.log (Real.sqrt (s : ℝ)) = (1 / 2 : ℝ) * Real.log s :=
    by rw [Real.log_sqrt hs.le]; ring
  have hsqrt_exp : Real.exp ((1 / 2 : ℝ) * Real.log (s : ℝ)) = Real.sqrt s := by
    rw [← hlogsqrt, Real.exp_log hsqrt]
  have heq :
      centralAtomConstant / Real.sqrt (s : ℝ) =
        Real.exp (-1 - Real.log 2 - (1 / 2 : ℝ) * Real.log (2 * (s : ℝ))) := by
    unfold centralAtomConstant
    rw [← hsqrt_exp]
    rw [← Real.exp_sub]
    congr 1
    rw [Real.log_mul (by norm_num) hs.ne']
    ring
  rw [heq]
  exact hexp

/-- The density range is eventually valid for the literal real `p` and
integer `s`, including the strict endpoint restrictions used by the law. -/
theorem eventually_sparse_validity :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ, SparseDensity θ T n p →
        ∀ s : ℕ, PrescribedSizeRange T p n s →
          0 < p ∧ p < 1 ∧ 0 < s ∧ s < n ∧ 2 * s ≤ n := by
  intro θ T hθlo hθhi hT
  have hθ : 0 < θ := by linarith
  have hT0 : 0 < T := by linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ => T * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hθ).comp hnat).const_mul T
  have hsmall : Tendsto (fun n : ℕ => 2 * T * (T * (n : ℝ) ^ (-θ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hupper.const_mul (2 * T)
  have hevent1 := hupper.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hevent2 := hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℕ)).and (hevent1.and hevent2))
  refine ⟨n₀, ?_⟩
  intro n hn p hp s hs
  obtain ⟨hn1, huppern, hsmalln⟩ := hn₀ n hn
  obtain ⟨hplo, hphi⟩ := hp
  obtain ⟨hslo, hshi⟩ := hs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT0
  have hp0 : 0 < p :=
    (mul_pos hTinv (Real.rpow_pos_of_pos hnR _)).trans hplo
  have hp1 : p < 1 := hphi.trans huppern
  have hs0 : 0 < s := by
    have hpos : (0 : ℝ) < s := (mul_pos (mul_pos hTinv hp0) hnR).trans_le hslo
    exact_mod_cast hpos
  have hTp : 2 * T * p < 1 := by
    calc
      2 * T * p < 2 * T * (T * (n : ℝ) ^ (-θ)) :=
        mul_lt_mul_of_pos_left hphi (by positivity)
      _ < 1 := hsmalln
  have hsreal : 2 * (s : ℝ) < (n : ℝ) := by
    calc
      2 * (s : ℝ) ≤ 2 * (T * p * n) := by nlinarith [hshi]
      _ = (2 * T * p) * n := by ring
      _ < 1 * n := mul_lt_mul_of_pos_right hTp hnR
      _ = n := by ring
  have hsle : 2 * s ≤ n := by exact_mod_cast (le_of_lt hsreal)
  have hsn : s < n := by nlinarith [hsle, hs0, hn1]
  exact ⟨hp0, hp1, hs0, hsn, hsle⟩

end MajorityDynamics.Probability.FixedSizeExponential
