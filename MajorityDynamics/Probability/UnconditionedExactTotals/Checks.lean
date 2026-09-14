import MajorityDynamics.Probability.UnconditionedExactTotals.Main

/-! Exact types, independently expanded specification, and dependency guards.
No paper-assembly module is imported by this package. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.UnconditionedExactTotals

example : UnconditionedExactTotalsTheorem := unconditioned_exact_totals

/-- Expanded literal specification, down to the original point event on the
trial array. The natural-to-integer cast occurs after summing copy counts. -/
example :
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ d : ℕ, 1 ≤ d → ∀ T : ℝ, 1 < T →
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ,
      (T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ)) →
      ∀ η : Fin d → ℤ, (∀ t, T⁻¹ * n < (η t : ℝ) ∧ (η t : ℝ) < T * n) →
      ∀ m : ℤ, (T⁻¹ * n < (m : ℝ) ∧ (m : ℝ) < T * n) → ∀ q : Fin d → ℝ,
      (∀ t, p - T * p / Real.sqrt (p * n) < q t ∧ q t < p + T * p / Real.sqrt (p * n)) →
      ∀ z : Fin d → ℤ, (∀ t, (z t : ℝ) = (m : ℝ) * (η t : ℝ) * q t) →
      0 < p ∧ p < 1 ∧ 1 ≤ m ∧ (m.toNat : ℤ) = m ∧
      (∀ t, 0 < q t ∧ q t < 1 ∧ 1 ≤ η t ∧ ((η t).toNat : ℤ) = η t ∧
        0 < z t ∧ z t < m * η t ∧ ((z t).toNat : ℤ) = z t) ∧
      c * ((n : ℝ) ^ 2 * p) ^ (-(d : ℝ) / 2) ≤
        ((Measure.pi (fun t => Measure.pi (fun _ : Fin m.toNat =>
          Measure.pi (fun _ : Fin (η t).toNat => bernoulliMeasure true false (probability (q t)))))).map
          (fun x t => ((∑ i : Fin m.toNat, count (x t i) : ℕ) : ℤ))).real {z} := by
  simpa only [UnconditionedExactTotalsTheorem, DensityWindow, SizeWindow, TiltWindow,
    sumLaw, trialLaw, bitsLaw, total, copies] using unconditioned_exact_totals

/-- Copy law: all `m` rows are independent, each row is a product-binomial. -/
example {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) :
    (trialLaw m η q).map (fun x (i : Fin m) (t : Fin d) => count (x t i)) =
      Measure.pi (fun _ : Fin m => Measure.pi (fun t => binomial (η t) (probability (q t)))) :=
  copies_law m η q

/-- Joint law, exposing the sum of the original copy counts. -/
example {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) :
    (trialLaw m η q).map (fun x t => ∑ i : Fin m, count (x t i)) =
      Measure.pi (fun t => binomial (m * η t) (probability (q t))) :=
  sum_binomial_vector_law m η q

example {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) (t : Fin d) :
    ((trialLaw m η q).map total).map (fun s => s t) =
      binomial (m * η t) (probability (q t)) := by
  rw [sum_binomial_vector_law]
  exact (measurePreserving_eval _ t).map_eq

example {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) :
    iIndepFun (fun t (s : Fin d → ℕ) => s t) ((trialLaw m η q).map total) := by
  rw [sum_binomial_vector_law]
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.count_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_law
/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.copies_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copies_law
/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.sum_binomial_vector_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_binomial_vector_law
/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.sumLaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sumLaw_eq
/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.sumLaw_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sumLaw_singleton
/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.scalar_atom_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scalar_atom_lower
/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.finite_atom_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_atom_lower
/-- info: 'MajorityDynamics.Probability.UnconditionedExactTotals.unconditioned_exact_totals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unconditioned_exact_totals

end MajorityDynamics.Probability.UnconditionedExactTotals
