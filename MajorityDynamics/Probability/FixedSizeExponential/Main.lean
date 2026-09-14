import MajorityDynamics.Probability.FixedSizeExponential.PointMass
import MajorityDynamics.Probability.FixedSizeExponential.Law
import MajorityDynamics.Probability.FixedSizeExponential.Bounds

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proof of Lemma C.5

The proof keeps the conditioning event explicit.  The independent product MGF
is only used after the exact conditional-law bridge and the central atom lower
bound have been established.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.FixedSizeExponential

/-- The conditioning probability is literally a binomial singleton probability. -/
theorem conditioning_event_eq_binomial {n s : ℕ} (q : SuccessProbability) (hs : s ≤ n) :
    (bitProductMeasure n q).real (fixedSizeEventSet n s) =
      (ProbabilityTheory.binomial n (closedProbability q)).real {s} := by
  rw [bitProductMeasure_event_real q hs, ProbabilityTheory.binomial_real_singleton]
  rfl

/-- Reusable comparison in the literal binomial-point-mass form. -/
theorem binomial_conditioning_comparison {n s : ℕ} (q : SuccessProbability) (hs : s ≤ n)
    (f : Bit n → ℝ) (hf : ∀ ξ, 0 ≤ f ξ) :
    (ProbabilityTheory.binomial n (closedProbability q)).real {s} *
      fixedSizeExpectation n s f ≤ ∫ ξ, f ξ ∂bitProductMeasure n q := by
  rw [← conditioning_event_eq_binomial q hs]
  exact conditional_expectation_mul_le q hs f hf

set_option maxHeartbeats 1200000 in
/-- Lemma C.5, `lem:nice_deg_cute`, with the literal real-density and
integer-size quantifiers. -/
theorem fixed_size_exponential : FixedSizeExponentialTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨nvalid, hvalid⟩ := eventually_sparse_validity θ T hθlo hθhi hT
  obtain ⟨nweight, hweight⟩ := eventually_weight_regime θ T hθlo hθhi hT
  let C₀ : ℝ := centralAtomConstant
  let C₁ : ℝ := Real.sqrt T / C₀
  let C₂ : ℝ := T ^ 3
  have hC₀ : 0 < C₀ := centralAtomConstant_pos
  have hC₁ : 0 < C₁ := div_pos (Real.sqrt_pos.mpr (by linarith)) hC₀
  have hC₂ : 0 < C₂ := by positivity
  refine ⟨C₁, C₂, hC₁, hC₂, max nvalid nweight, ?_⟩
  intro n hn p hp a ha s hs
  have hv := hvalid n (le_trans (le_max_left _ _) hn) p hp s hs
  have hw := hweight n (le_trans (le_max_right _ _) hn) p hp
  obtain ⟨hp0, hp1, hs0, hsn, hsle⟩ := hv
  obtain ⟨hslo, hshi⟩ := hs
  obtain ⟨_, _, hlog, hlogsq, hweight1⟩ := hw
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hs0.trans hsn
  have hpn : 0 < p * n := mul_pos hp0 hnR
  have hq0 : 0 < (s : ℝ) / n := by positivity
  have hq1 : (s : ℝ) / n < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact_mod_cast hsn
  let q : SuccessProbability := ⟨(s : ℝ) / n, hq0, hq1⟩
  have hqT : (q : ℝ) ≤ T * p := by
    dsimp [q]
    apply (div_le_iff₀ hnR).2
    exact hshi
  have hsq := weighted_square_bound hp0 q.property.1.le hqT hpn (by linarith) a ha
  have hqsum : (q : ℝ) * ∑ i, a i =
      fixedSizeExpectation n s (bitLinear a) := by
    symm
    exact fixedSize_mean hs0 (le_of_lt hsn) a
  have hcond := conditional_expectation_mul_le q (le_of_lt hsn)
    (fun ξ => Real.exp (bitLinear a ξ)) (fun ξ => (Real.exp_pos _).le)
  have ha1 : ∀ i, |a i| ≤ 1 := fun i => (ha i).trans hweight1
  have hprod := bitProduct_mgf_bound q a ha1
  have hmass_formula := bitProductMeasure_event_real q (le_of_lt hsn)
  have hpoint_formula :
      (n.choose s : ℝ) * (q : ℝ) ^ s * (1 - (q : ℝ)) ^ (n - s) =
        MajorityDynamics.Binomial.Approximation.pointMass n s q := by
    rw [MajorityDynamics.Binomial.Approximation.pointMass,
      ProbabilityTheory.binomial_real_singleton]
    rfl
  have hcentral :
      C₀ / Real.sqrt (s : ℝ) ≤
        MajorityDynamics.Binomial.Approximation.pointMass n s q := by
    exact central_binomial_point_mass_lower hs0 hsn
  have hmass : C₀ / Real.sqrt (s : ℝ) ≤
      (bitProductMeasure n q).real (fixedSizeEventSet n s) := by
    rw [hmass_formula, hpoint_formula]
    exact hcentral
  have hE0 : 0 ≤ fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) :=
    integral_nonneg (fun ξ => (Real.exp_pos _).le)
  have hscaled :
      (C₀ / Real.sqrt (s : ℝ)) *
          fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
        ∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q := by
    exact (mul_le_mul_of_nonneg_right hmass hE0).trans hcond
  have hden : 0 < C₀ / Real.sqrt (s : ℝ) :=
    div_pos hC₀ (Real.sqrt_pos.mpr (by exact_mod_cast hs0))
  have hEdiv :
      fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
        (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) /
          (C₀ / Real.sqrt (s : ℝ)) := by
    apply (le_div_iff₀ hden).2
    simpa [mul_comm] using hscaled
  have hEbound :
      fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
        (Real.sqrt (s : ℝ) / C₀) *
          (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) := by
    calc
      _ ≤ (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) /
          (C₀ / Real.sqrt (s : ℝ)) := hEdiv
      _ = (Real.sqrt (s : ℝ) / C₀) *
          (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) := by
            field_simp [hC₀.ne', (Real.sqrt_pos.mpr (by exact_mod_cast hs0 : (0 : ℝ) < s)).ne']
  have hprod' :
      (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) ≤
        Real.exp ((q : ℝ) * ∑ i, a i + C₂ * (Real.log (n : ℝ)) ^ 2) := by
    apply hprod.trans
    apply Real.exp_le_exp.mpr
    dsimp [C₂]
    linarith
  have hsqrt : Real.sqrt (s : ℝ) ≤ Real.sqrt T * Real.sqrt (p * n) := by
    calc
      Real.sqrt (s : ℝ) ≤ Real.sqrt (T * p * n) := by
        apply Real.sqrt_le_sqrt
        exact hshi
      _ = Real.sqrt T * Real.sqrt (p * n) := by
        rw [mul_assoc, Real.sqrt_mul (by linarith : 0 ≤ T)]
  have hfactor :
      (Real.sqrt (s : ℝ) / C₀) *
          (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) ≤
        C₁ * Real.sqrt (p * n) *
          Real.exp ((q : ℝ) * ∑ i, a i + C₂ * (Real.log (n : ℝ)) ^ 2) := by
    calc
      _ ≤ (Real.sqrt T * Real.sqrt (p * n) / C₀) *
          (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) := by
            exact mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hsqrt (by linarith))
              (integral_nonneg (fun ξ => (Real.exp_pos _).le))
      _ ≤ _ := by
        calc
          _ ≤ (Real.sqrt T * Real.sqrt (p * n) / C₀) *
              Real.exp ((q : ℝ) * ∑ i, a i + C₂ * (Real.log (n : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left hprod' (by positivity)
          _ = C₁ * Real.sqrt (p * n) *
              Real.exp ((q : ℝ) * ∑ i, a i + C₂ * (Real.log (n : ℝ)) ^ 2) := by
            dsimp [C₁]
            ring
  refine ⟨hp0, hp1, hs0, hsn, ?_, ?_⟩
  · have hfinal := hEbound.trans hfactor
    rw [hqsum] at hfinal
    exact hfinal
  · exact fixedSize_mean hs0 (le_of_lt hsn) a

/-- The form used by the two independent pieces in Theorem C.2: the positive
`square-root prefactor` and the positive constant are absorbed into a larger
uniform multiple of `(log n)^2`. -/
theorem fixed_size_exponential_corollary :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ,
        SparseDensity θ T n p → ∀ a : Fin n → ℝ,
        FixedSizeWeightBound T n p a → ∀ s : ℕ,
        PrescribedSizeRange T p n s →
          fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
            Real.exp (fixedSizeExpectation n s (bitLinear a) + C * (Real.log n) ^ 2) := by
  intro θ T hθlo hθhi hT
  obtain ⟨C₁, C₂, hC₁, hC₂, n₀, hmain⟩ := fixed_size_exponential θ T hθlo hθhi hT
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp
    (hlog.eventually (eventually_ge_atTop (max 2 (Real.log C₁))))
  refine ⟨C₂ + 2, by linarith, max n₀ n₁, ?_⟩
  intro n hn p hp a ha s hs
  have hN := hmain n (le_trans (le_max_left _ _) hn) p hp a ha s hs
  obtain ⟨hp0, hp1, hs0, hsn, hbound, hmean⟩ := hN
  have hlogn : max 2 (Real.log C₁) ≤ Real.log (n : ℝ) :=
    hn₁ n (le_trans (le_max_right _ _) hn)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hs0.trans hsn
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by linarith [le_max_left 2 (Real.log C₁)]
  have hsqrt : Real.sqrt (p * n) ≤ Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact (mul_le_mul_of_nonneg_right hp1.le hnR.le).trans_eq (one_mul _)
  have hlogsqrt : Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) = Real.sqrt (n : ℝ) := by
    rw [show (1 / 2 : ℝ) * Real.log (n : ℝ) = Real.log (Real.sqrt n) by
      rw [Real.log_sqrt hnR.le]; ring, Real.exp_log (Real.sqrt_pos.mpr hnR)]
  have habsorb : C₁ * Real.sqrt (p * n) ≤
      Real.exp (2 * (Real.log (n : ℝ)) ^ 2) := by
    calc
      C₁ * Real.sqrt (p * n) ≤ C₁ * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt hC₁.le
      _ = Real.exp (Real.log C₁ + (1 / 2 : ℝ) * Real.log (n : ℝ)) := by
        rw [Real.exp_add, Real.exp_log hC₁, hlogsqrt]
      _ ≤ Real.exp (2 * (Real.log (n : ℝ)) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hlog1, le_trans (le_max_right 2 _) hlogn]
  calc
    fixedSizeExpectation n s (fun ξ => Real.exp (bitLinear a ξ)) ≤
        C₁ * Real.sqrt (p * n) *
          Real.exp (fixedSizeExpectation n s (bitLinear a) + C₂ * (Real.log n) ^ 2) := hbound
    _ ≤ Real.exp (2 * (Real.log n) ^ 2) *
          Real.exp (fixedSizeExpectation n s (bitLinear a) + C₂ * (Real.log n) ^ 2) := by
      exact mul_le_mul_of_nonneg_right habsorb (Real.exp_pos _).le
    _ = Real.exp (fixedSizeExpectation n s (bitLinear a) + (C₂ + 2) * (Real.log n) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

end MajorityDynamics.Probability.FixedSizeExponential


namespace MajorityDynamics.Probability.FixedSizeExponential

/-- Literal integer-size wrapper: positivity and the conversion to a natural
size are consequences of the real interval, not additional hypotheses. -/
theorem fixed_size_exponential_int :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ p : ℝ, SparseDensity θ T n p →
        ∀ a : Fin n → ℝ, FixedSizeWeightBound T n p a →
        ∀ s : ℤ, T⁻¹ * p * n ≤ (s : ℝ) → (s : ℝ) ≤ T * p * n →
          0 < p ∧ p < 1 ∧ 0 < s ∧ s < (n : ℤ) ∧
          (s.toNat : ℤ) = s ∧
          (fixedSizeExpectation n s.toNat (fun ξ => Real.exp (bitLinear a ξ)) ≤
            C₁ * Real.sqrt (p * n) *
              Real.exp (fixedSizeExpectation n s.toNat (bitLinear a) +
                C₂ * (Real.log n) ^ 2)) ∧
          fixedSizeExpectation n s.toNat (bitLinear a) =
            (s : ℝ) / n * ∑ i, a i := by
  intro θ T hθlo hθhi hT
  obtain ⟨C₁, C₂, hC₁, hC₂, n₀, hmain⟩ :=
    fixed_size_exponential θ T hθlo hθhi hT
  refine ⟨C₁, C₂, hC₁, hC₂, max n₀ 1, ?_⟩
  intro n hn p hp a ha s hslo hshi
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hTpos : 0 < T := by linarith
  have hppos : 0 < p :=
    (mul_pos (inv_pos.mpr hTpos) (Real.rpow_pos_of_pos hnpos _)).trans hp.1
  have hspos : (0 : ℝ) < s :=
    (mul_pos (mul_pos (inv_pos.mpr hTpos) hppos) hnpos).trans_le hslo
  have hsz : (0 : ℤ) < s := by exact_mod_cast hspos
  have hcast : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hsz.le
  have hcastR : ((s.toNat : ℕ) : ℝ) = (s : ℝ) := by exact_mod_cast hcast
  have hrange : PrescribedSizeRange T p n s.toNat := by
    constructor
    · simpa only [hcastR] using hslo
    · simpa only [hcastR] using hshi
  obtain ⟨hp0, hp1, _, hsn, hbound, hmean⟩ :=
    hmain n ((le_max_left _ _).trans hn) p hp a ha s.toNat hrange
  refine ⟨hp0, hp1, hsz, ?_, hcast, hbound, ?_⟩
  · have : (s.toNat : ℤ) < (n : ℤ) := by exact_mod_cast hsn
    rwa [hcast] at this
  · simpa only [hcastR] using hmean

end MajorityDynamics.Probability.FixedSizeExponential
