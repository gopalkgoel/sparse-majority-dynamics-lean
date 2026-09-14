import MajorityDynamics.Binomial.ApproximationStatements
import MajorityDynamics.Analysis.GaussianRegularity.Law

/-! Exact Gaussian normalization used in Appendix E.3. These identities concern
actual measures and do not posit a Gaussian approximation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace MajorityDynamics.Idealized.RowLimits
open Analysis.ConditionalGaussian

/-- Coordinate normalization followed by the Euclidean-space identification. -/
def normalize {d : ℕ} (a : ℝ) (x : Fin d → ℝ) : Space d :=
  WithLp.toLp 2 (fun i => x i / a)

theorem measurable_normalize {d : ℕ} (a : ℝ) : Measurable (@normalize d a) := by
  unfold normalize
  fun_prop

/-- Scaling preserves the exact independent Gaussian product law. -/
theorem map_normalize_product {d : ℕ} (a : ℝ) (m : Fin d → ℝ)
    (v : Fin d → ℝ≥0) :
    (Measure.pi fun i => gaussianReal (m i) (v i)).map (normalize a) =
      gaussianLaw (Matrix.diagonal (fun i => (v i : ℝ) / a ^ 2))
        (WithLp.toLp 2 (fun i => m i / a)) := by
  have hm : Measurable (fun x : Fin d → ℝ => fun i => x i / a) := by fun_prop
  rw [show normalize a = (WithLp.toLp 2) ∘ (fun x : Fin d → ℝ => fun i => x i / a) from rfl,
    ← Measure.map_map (show Measurable (WithLp.toLp 2 : (Fin d → ℝ) → Space d) from by fun_prop) hm,
    Measure.pi_map_pi (f := fun (_ : Fin d) (x : ℝ) => x / a) (fun i => (show Measurable (fun x : ℝ => x / a) from by fun_prop).aemeasurable)]
  simp_rw [gaussianReal_map_div_const]
  convert Analysis.GaussianRegularity.map_product_gaussian
    (WithLp.toLp 2 (fun i => m i / a))
    (fun i => v i / NNReal.mk (a ^ 2) (sq_nonneg a)) using 1
  simp

/-- The A.2 Gaussian law, normalized by any scale, as an E.2 Gaussian law. -/
theorem map_normalize_a2 {d : ℕ} (p : Binomial.Probability)
    (η : Fin d → ℕ) (α : Fin d → ℝ) (a : ℝ) :
    (Binomial.Approximation.gaussianLaw p η α).map (normalize a) =
      gaussianLaw (Matrix.diagonal (fun i => (p : ℝ) * η i / a ^ 2))
        (WithLp.toLp 2 (fun i => Real.sqrt ((p : ℝ) * η i) * α i / a)) :=
  map_normalize_product a _ _

/-- Normalization is a measurable equivalence when the scale is nonzero. -/
def normalizeEquiv {d : ℕ} (a : ℝ) (ha : a ≠ 0) :
    (Fin d → ℝ) ≃ᵐ Space d where
  toFun := normalize a
  invFun := fun y i => a * y i
  left_inv := by intro x; funext i; simp [normalize, mul_div_cancel₀, ha]
  right_inv := by intro y; ext i; simp [normalize, mul_div_cancel_left₀, ha]
  measurable_toFun := measurable_normalize a
  measurable_invFun := by
    change Measurable (fun y : Space d => fun i => a * y i)
    fun_prop

/-- No measurability or integrability assumption on the observable is needed:
the exact change of variables holds under the Bochner convention. -/
theorem integral_normalize_product {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (m : Fin d → ℝ) (v : Fin d → ℝ≥0) (E : Set (Space d))
    (f : Space d → ℝ) :
    (∫ x in normalize a ⁻¹' E, f (normalize a x)
      ∂(Measure.pi fun i => gaussianReal (m i) (v i))) =
    ∫ y in E, f y ∂gaussianLaw
      (Matrix.diagonal (fun i => (v i : ℝ) / a ^ 2))
      (WithLp.toLp 2 (fun i => m i / a)) := by
  rw [← map_normalize_product a m v]
  exact (setIntegral_map_equiv (normalizeEquiv a ha) f E).symm

/-- Weak half-spaces transform exactly with their thresholds. -/
theorem normalize_event {d r : ℕ} (a : ℝ) (ha : 0 < a)
    (M : Matrix (Fin r) (Fin d) ℝ) (u : Space r) :
    normalize a ⁻¹' Analysis.GaussianRegularity.event M u =
      {x : Fin d → ℝ | ∀ j, -(u j) * a ≤ ∑ i, M j i * x i} := by
  ext x
  simp only [mem_preimage, Analysis.GaussianRegularity.event, mem_ofPred_eq, normalize]
  congr! 1 with j
  change (-u j ≤ ∑ i, M j i * (x i / a)) ↔ _
  simp only [← mul_div_assoc, ← Finset.sum_div]
  exact le_div_iff₀ ha

/-- Exact normalized variance at the paper's scale. -/
theorem normalized_variance (p : Binomial.Probability) (N η : ℕ) (hN : 0 < N) :
    (p : ℝ) * η / (Real.sqrt ((p : ℝ) * N)) ^ 2 = (η : ℝ) / N := by
  rw [Real.sq_sqrt (mul_nonneg p.property.1.le (Nat.cast_nonneg N))]
  field_simp [ne_of_gt p.property.1, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]

/-- Exact normalized mean for the tilt used in the paper. -/
theorem normalized_mean (p : Binomial.Probability) (N η : ℕ)
    (hN : 0 < N) (σ ν : ℝ) :
    Real.sqrt ((p : ℝ) * η) * (σ / ν * Real.sqrt ((η : ℝ) / N)) /
      Real.sqrt ((p : ℝ) * N) = σ * η / ((N : ℝ) * ν) := by
  have hp := p.property.1
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  rw [Real.sqrt_mul hp.le, Real.sqrt_mul hp.le, Real.sqrt_div he]
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have hsp : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  calc
    _ = σ / ν * (Real.sqrt (η : ℝ) ^ 2) / (Real.sqrt (N : ℝ) ^ 2) := by
      field_simp
    _ = _ := by rw [Real.sq_sqrt he, Real.sq_sqrt hn.le]; ring

/-- The normalizing tilt of E.3 gives the precise perturbed mean and variance,
including the one-trial diagonal correction already present in `η`. -/
theorem map_normalize_row {d : ℕ} (p : Binomial.Probability) (N : ℕ)
    (hN : 0 < N) (η : Fin d → ℕ) (σ ν : Fin d → ℝ) :
    (Binomial.Approximation.gaussianLaw p η
      (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N))).map
      (normalize (Real.sqrt ((p : ℝ) * N))) =
    gaussianLaw (Matrix.diagonal (fun i => (η i : ℝ) / N))
      (WithLp.toLp 2 (fun i => σ i * η i / ((N : ℝ) * ν i))) := by
  rw [map_normalize_a2]
  simp_rw [normalized_mean p N _ hN, normalized_variance p N _ hN]

/-- E.3 normalization of all Gaussian event moments at once. -/
theorem integral_normalize_row {d r : ℕ} (p : Binomial.Probability) (N : ℕ)
    (hN : 0 < N) (η : Fin d → ℕ) (σ ν : Fin d → ℝ)
    (M : Matrix (Fin r) (Fin d) ℝ) (u : Space r) (f : Space d → ℝ) :
    (∫ x in {x : Fin d → ℝ | ∀ j,
        -(u j) * Real.sqrt ((p : ℝ) * N) ≤ ∑ i, M j i * x i},
      f (normalize (Real.sqrt ((p : ℝ) * N)) x)
      ∂Binomial.Approximation.gaussianLaw p η
        (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N))) =
    ∫ y in Analysis.GaussianRegularity.event M u, f y
      ∂gaussianLaw (Matrix.diagonal (fun i => (η i : ℝ) / N))
        (WithLp.toLp 2 (fun i => σ i * η i / ((N : ℝ) * ν i))) := by
  have ha : 0 < Real.sqrt ((p : ℝ) * N) :=
    Real.sqrt_pos.mpr (mul_pos p.property.1 (Nat.cast_pos.mpr hN))
  rw [← normalize_event _ ha M u, ← map_normalize_row p N hN η σ ν]
  exact (setIntegral_map_equiv (normalizeEquiv _ (ne_of_gt ha)) f _).symm

end MajorityDynamics.Idealized.RowLimits
