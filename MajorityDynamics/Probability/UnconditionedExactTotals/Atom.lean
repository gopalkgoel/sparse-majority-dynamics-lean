import MajorityDynamics.Probability.UnconditionedExactTotals.Law
import MajorityDynamics.Probability.FixedSizeExponential.PointMass

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.UnconditionedExactTotals
open FixedSizeExponential

/-- Transfer C.5's central atom to an arbitrary parameter with integral mean. -/
theorem scalar_atom_lower {N s : ℕ} {q : ℝ} (hq : 0 < q ∧ q < 1)
    (hs0 : 0 < s) (hsN : s < N) (hmean : (s : ℝ) = (N : ℝ) * q) :
    centralAtomConstant / Real.sqrt (s : ℝ) ≤ (binomial N (probability q)).real {s} := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (hs0.trans hsN))
  have heq : probability q = closedProbability (centralProbability hs0 hsN) := by
    apply Subtype.ext
    change (probability q : ℝ) = (s : ℝ) / N
    rw [probability_eq ⟨hq.1.le, hq.2.le⟩, hmean]
    field_simp
  rw [heq]
  exact central_binomial_point_mass_lower hs0 hsN

/-- The real exponent is exactly the product of `d` inverse square roots. -/
theorem inverse_sqrt_pow {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    x ^ (-(d : ℝ) / 2) = ((Real.sqrt x) ^ d)⁻¹ := by
  rw [neg_div, Real.rpow_neg hx, ← Real.rpow_natCast, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx]
  congr 2
  ring

/-- A finite product estimate. No asymptotic or law-identification hypothesis
is left in this bound on the concrete sampling measure. -/
theorem finite_atom_lower {d m : ℕ} {η z : Fin d → ℕ} {q : Fin d → ℝ}
    {K x : ℝ} (hK : 0 < K) (hx : 0 < x)
    (hq : ∀ t, 0 < q t ∧ q t < 1)
    (hz0 : ∀ t, 0 < z t) (hzN : ∀ t, z t < m * η t)
    (hmean : ∀ t, (z t : ℝ) = ((m * η t : ℕ) : ℝ) * q t)
    (hupper : ∀ t, (z t : ℝ) ≤ K ^ 2 * x) :
    (centralAtomConstant / K) ^ d * x ^ (-(d : ℝ) / 2) ≤
      (sumLaw m η q).real {fun t => (z t : ℤ)} := by
  have hC := centralAtomConstant_pos
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hterm (t : Fin d) : (centralAtomConstant / K) / Real.sqrt x ≤
      (binomial (m * η t) (probability (q t))).real {z t} := by
    have hsz : 0 < Real.sqrt (z t : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hz0 t)
    have hsle : Real.sqrt (z t : ℝ) ≤ K * Real.sqrt x := by
      calc
        _ ≤ Real.sqrt (K ^ 2 * x) := Real.sqrt_le_sqrt (hupper t)
        _ = K * Real.sqrt x := by rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK.le]
    calc
      _ = centralAtomConstant / (K * Real.sqrt x) := by rw [div_div]
      _ ≤ centralAtomConstant / Real.sqrt (z t : ℝ) :=
        div_le_div_of_nonneg_left hC.le hsz hsle
      _ ≤ _ := scalar_atom_lower (hq t) (hz0 t) (hzN t) (hmean t)
  have hprod := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin d)))
    (fun t _ => (by positivity : 0 ≤ (centralAtomConstant / K) / Real.sqrt x))
    (fun t _ => hterm t)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow] at hprod
  rw [inverse_sqrt_pow hx.le, ← div_eq_mul_inv]
  refine hprod.trans_eq ?_
  rw [sumLaw_singleton]
  simp only [binomial_real_singleton]

end MajorityDynamics.Probability.UnconditionedExactTotals
