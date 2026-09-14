import MajorityDynamics.Probability.UnconditionedExactTotals.Counting

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.UnconditionedExactTotals

/-- Flattening the copy/trial indices preserves the independent bit law. -/
theorem flatten_law (m η : ℕ) (q : unitInterval) :
    (Measure.pi (fun _ : Fin m => bitsLaw (Fin η) q)).map
      (fun x (ij : Fin m × Fin η) => x ij.1 ij.2) = bitsLaw (Fin m × Fin η) q := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro x
  rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton x)]
  have he : (fun y (ij : Fin m × Fin η) => y ij.1 ij.2) ⁻¹' {x} =
      {fun i j => x (i,j)} := by ext y; simp [funext_iff, Prod.forall]
  rw [he]
  simp only [measureReal_def, bitsLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  rw [Fintype.prod_prod_type]

theorem count_flatten (m η : ℕ) (x : Fin m → Fin η → Bool) :
    count (fun ij : Fin m × Fin η => x ij.1 ij.2) = ∑ i, count (x i) := by
  simp only [count_eq_sum, Fintype.sum_prod_type]

/-- Convolution of the copy counts, proved on the actual independent trials. -/
theorem sum_count_law (m η : ℕ) (q : unitInterval) :
    (Measure.pi (fun _ : Fin m => bitsLaw (Fin η) q)).map (fun x => ∑ i, count (x i)) =
      binomial (m * η) q := by
  calc
    _ = (bitsLaw (Fin m × Fin η) q).map count := by
      rw [← flatten_law, Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      exact (count_flatten m η x).symm
    _ = _ := by rw [count_law]; simp

/-- The total vector has the product of the scalar binomial laws. -/
theorem sum_binomial_vector_law {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) :
    (trialLaw m η q).map total =
      Measure.pi (fun t => binomial (m * η t) (probability (q t))) := by
  unfold trialLaw total copies
  rw [Measure.pi_map_pi (f := fun t (x : Fin m → Fin (η t) → Bool) => ∑ i, count (x i))
    (fun _ => Measurable.of_discrete.aemeasurable)]
  simp_rw [sum_count_law]

/-- Regrouping counts by copy preserves the product law. -/
theorem transpose_law {d m : ℕ} (μ : Fin d → Measure ℕ) [∀ t, IsProbabilityMeasure (μ t)] :
    (Measure.pi (fun t => Measure.pi (fun _ : Fin m => μ t))).map
      (fun x i t => x t i) = Measure.pi (fun _ : Fin m => Measure.pi μ) := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro x
  rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton x)]
  have he : (fun y (i : Fin m) (t : Fin d) => y t i) ⁻¹' {x} = {fun t i => x i t} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, funext_iff]
    exact forall_comm
  rw [he]
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_comm

/-- The sampling experiment produces exactly `m` independent copies of the
specified vector with independent binomial coordinates. -/
theorem copies_law {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) :
    (trialLaw m η q).map copies =
      Measure.pi (fun _ : Fin m => Measure.pi (fun t => binomial (η t) (probability (q t)))) := by
  have hc : (trialLaw m η q).map (fun x t i => count (x t i)) =
      Measure.pi (fun t => Measure.pi (fun _ : Fin m => binomial (η t) (probability (q t)))) := by
    unfold trialLaw
    rw [Measure.pi_map_pi (f := fun t (x : Fin m → Fin (η t) → Bool) i => count (x i))
      (fun _ => Measurable.of_discrete.aemeasurable)]
    congr 1
    funext t
    rw [Measure.pi_map_pi (f := fun (_ : Fin m) (x : Fin (η t) → Bool) => count x)
      (fun _ => measurable_count.aemeasurable)]
    simp only [count_law, Fintype.card_fin]
  rw [← transpose_law, ← hc, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Integer embedding of the joint law. -/
theorem sumLaw_eq {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) :
    sumLaw m η q = Measure.pi (fun t => (binomial (m * η t) (probability (q t))).map
      (Nat.cast : ℕ → ℤ)) := by
  rw [← Measure.pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable), ← sum_binomial_vector_law,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The exact point event, including the natural/integer embedding. -/
theorem sumLaw_singleton {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ)
    (z : Fin d → ℕ) :
    (sumLaw m η q).real {fun t => (z t : ℤ)} =
      ∏ t, ((m * η t).choose (z t) : ℝ) * (probability (q t) : ℝ) ^ (z t) *
        (1 - (probability (q t) : ℝ)) ^ (m * η t - z t) := by
  rw [sumLaw_eq]
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  change (∏ t, ((binomial (m * η t) (probability (q t))).map (Nat.cast : ℕ → ℤ)).real {(z t : ℤ)}) = _
  simp only [map_cast_binomial_real_singleton]

end MajorityDynamics.Probability.UnconditionedExactTotals
