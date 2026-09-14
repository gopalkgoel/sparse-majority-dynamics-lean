import MajorityDynamics.GraphProcess.GoodArrayProbability.CentralBinomial

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialBox

/-- Singleton probabilities of the original product law, on its original natural lattice. -/
theorem atom_product {d : ℕ} (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (x : Fin d → ℕ) :
    (Binomial.law η q).real {x} =
      ∏ i, Binomial.Approximation.pointMass (η i) (x i) (q i) := by
  simp only [measureReal_def, Binomial.law, Measure.pi_singleton,
    ENNReal.toReal_prod, Binomial.Approximation.pointMass]

theorem sqrt_pow_eq_rpow (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    Real.sqrt x ^ d = x ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx]
  congr 1
  ring

/-- The natural product exponent is exactly the original real exponent `-d/2`. -/
theorem coordinate_power (c x : ℝ) (hx : 0 < x) (d : ℕ) :
    (c / Real.sqrt x) ^ d = c ^ d * x ^ (-(d : ℝ) / 2) := by
  rw [div_pow, sqrt_pow_eq_rpow x hx.le d, div_eq_mul_inv,
    ← Real.rpow_neg hx.le]
  congr 2
  ring

/-- A fixed central window and a comparable upper mean imply a uniform actual
product-binomial atom bound. All constants precede every trial count and tilt. -/
theorem central_product_lower (d : ℕ) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 1 ≤ L ∧
      ∀ (s : ℝ), 0 < s → ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
        (x : Fin d → ℕ),
      (∀ i, (q i : ℝ) ≤ 1/2) →
      (∀ i, L ≤ (η i : ℝ) * (q i : ℝ)) →
      (∀ i, (η i : ℝ) * (q i : ℝ) ≤ D*s) →
      (∀ i, |(x i : ℝ) - (η i : ℝ) * (q i : ℝ)| ≤
        A * Real.sqrt ((η i : ℝ) * (q i : ℝ))) →
      c * s ^ (-(d : ℝ) / 2) ≤ (Binomial.law η q).real {x} := by
  obtain ⟨c, hc, L, hL, hpoint⟩ :=
    GraphProcess.GoodArrayProbability.central_binomial_lower A hA
  refine ⟨(c / Real.sqrt D)^d, pow_pos (div_pos hc (Real.sqrt_pos.mpr hD)) _,
    L, hL, ?_⟩
  intro s hs η q x hq hmean hupper hwindow
  have hcoord (i : Fin d) :
      (c / Real.sqrt D) / Real.sqrt s ≤
        Binomial.Approximation.pointMass (η i) (x i) (q i) := by
    have hm : 0 < (η i : ℝ) * (q i : ℝ) := lt_of_lt_of_le (by linarith : 0 < L) (hmean i)
    have hsqrt : Real.sqrt ((η i : ℝ) * (q i : ℝ)) ≤
        Real.sqrt D * Real.sqrt s := by
      rw [← Real.sqrt_mul hD.le]
      exact Real.sqrt_le_sqrt (hupper i)
    calc
      (c / Real.sqrt D) / Real.sqrt s = c / (Real.sqrt D * Real.sqrt s) := by ring
      _ ≤ c / Real.sqrt ((η i : ℝ) * (q i : ℝ)) :=
        div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hm) hsqrt
      _ ≤ _ := hpoint (η i) (q i) (x i) (hq i) (hmean i) (hwindow i)
  rw [atom_product, ← coordinate_power (c / Real.sqrt D) s hs d]
  have hprod := Finset.prod_le_prod (s := Finset.univ)
    (f := fun _ : Fin d => (c / Real.sqrt D) / Real.sqrt s)
    (g := fun i => Binomial.Approximation.pointMass (η i) (x i) (q i))
    (fun _ _ => (div_pos (div_pos hc (Real.sqrt_pos.mpr hD)) (Real.sqrt_pos.mpr hs)).le)
    (fun i _ => hcoord i)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

/-- A lower side-length bound and the atom scale cancel without any loss in `N`. -/
theorem width_point_cancellation (d L : ℕ) (c w s : ℝ) (hc : 0 ≤ c)
    (hw : 0 ≤ w) (hs : 0 < s) (hwidth : w * Real.sqrt s ≤ (L : ℝ)) :
    c * w^d ≤ (L : ℝ)^d * (c * s^(-(d : ℝ)/2)) := by
  have hpow := pow_le_pow_left₀ (mul_nonneg hw (Real.sqrt_nonneg s)) hwidth d
  have hrpos : 0 ≤ c * s^(-(d : ℝ)/2) := mul_nonneg hc (Real.rpow_nonneg hs.le _)
  have hmul := mul_le_mul_of_nonneg_right hpow hrpos
  have hid : (w * Real.sqrt s)^d * (c * s^(-(d : ℝ)/2)) = c * w^d := by
    rw [mul_pow, sqrt_pow_eq_rpow s hs.le d]
    calc
      w^d * s^((d:ℝ)/2) * (c * s^(-(d:ℝ)/2)) =
          c * w^d * (s^((d:ℝ)/2) * s^(-(d:ℝ)/2)) := by ring
      _ = c * w^d := by
        rw [← Real.rpow_add hs]
        have : (d : ℝ)/2 + -(d : ℝ)/2 = 0 := by ring
        rw [this, Real.rpow_zero, mul_one]
  rwa [hid] at hmul

end MajorityDynamics.Probability.ConditionedBinomialBox
