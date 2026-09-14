import MajorityDynamics.Idealized.RowLimits.A2
import MajorityDynamics.Idealized.RowLimits.ScalingMoments
import MajorityDynamics.Idealized.RowLimits.Observables
import MajorityDynamics.Idealized.RowLimits.GeometryLocal
import MajorityDynamics.Idealized.RowLimits.EventsBounds

/-! Simultaneous normalized raw row-moment estimates from the proved A.2.
Only the explicit uniform A.2 geometry remains as a premise here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Binomial Binomial.Approximation Analysis.ConditionalGaussian Universal

/-- The exact A.2 Gaussian event after normalization by the global scale. -/
theorem gaussianEvent_normalized {d r : ℕ} (N : ℕ) (hN : 0 < N)
    (p : Probability) (η : Fin d → ℕ) (M : Fin r → Fin d → ℤ) :
    gaussianEvent M p η =
      normalize (scale N p) ⁻¹' Analysis.GaussianRegularity.event
        (fun j i => (M j i : ℝ))
        (WithLp.toLp 2 (fun j => (p : ℝ) * (∑ i, (M j i : ℝ) * η i) / scale N p)) := by
  have ha : 0 < scale N p := Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hN))
  rw [normalize_event _ ha]
  ext x
  simp only [gaussianEvent, mem_ofPred_eq]
  congr! 1 with j
  change (-(p : ℝ) * (∑ i, (M j i : ℝ) * η i) ≤ _) ↔
    (-((p : ℝ) * (∑ i, (M j i : ℝ) * η i) / scale N p) * scale N p ≤ _)
  rw [← neg_div, div_mul_cancel₀ _ ha.ne']
  simp only [neg_mul]

/-- Every degree-zero, one, and two row moment shares a uniform A.2 constant.
The right side is already the actual normalized Gaussian with the precise
perturbed parameters; the left side uses the actual independent binomials. -/
theorem normalized_gaussian_comparison_finite {ι : Type*} [Fintype ι]
    (θ T : ℝ) (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T)
    (d : ℕ) (hd : 0 < d) (r : ι → ℕ)
    (M : ∀ j, Fin (r j) → Fin d → ℤ) (hM : ∀ j, OrthogonalRows (M j))
    (strict : ∀ j, Fin (r j) → Bool) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Probability, Density θ T N p →
      ∀ η : Fin d → ℕ, Sizes T N η → ∀ σ ν : Fin d → ℝ,
      (∀ i, |σ i / ν i * Real.sqrt ((η i : ℝ) / N)| < T) → ∀ j,
      (∀ k, |∑ i, (M j k i : ℝ) * η i| < T * N / scale N p) →
      ∀ o : MomentKind d,
      |(∫ a in inequalityEvent (fun k i => (M j k i : ℝ)) (strict j),
          momentValue o (fun i => centered p η a i / scale N p)
          ∂Binomial.law η (gaussianTilt p η
            (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)))) -
        (∫ x in Analysis.GaussianRegularity.event (fun k i => (M j k i : ℝ))
          (WithLp.toLp 2 (fun k => (p : ℝ) * (∑ i, (M j k i : ℝ) * η i) / scale N p)),
          momentValue o x.ofLp ∂Analysis.ConditionalGaussian.gaussianLaw
            (Matrix.diagonal (fun i => (η i : ℝ) / N))
            (WithLp.toLp 2 (fun i => σ i * η i / ((N : ℝ) * ν i))))| ≤
        C * (Real.log N) ^ (3 + (∑ i, momentExponent o i) + d) / scale N p := by
  classical
  obtain ⟨C, hC, N₀, hN₀, h⟩ := gaussian_comparison_finite (ι := ι × MomentKind d)
    θ T hθ hθ' hT d hd (fun j => r j.1) (fun j => M j.1)
    (fun j => hM j.1) (fun j => strict j.1) (fun _ => 1)
    (fun j => momentExponent j.2)
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N hN p hp η hη σ ν hα j hbal o
  have hn : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (hN₀.trans hN)
  have ha : 0 < scale N p := Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hn))
  have hb := h N hN p hp η hη
    (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)) hα (j, o) hbal
  have hc := normalized_monomial_comparison
    (Binomial.law η (gaussianTilt p η
      (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N))))
    (Binomial.Approximation.gaussianLaw p η
      (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)))
    (inequalityEvent (fun k i => (M j k i : ℝ)) (strict j))
    (gaussianEvent (M j) p η) (centered p η) id 1 (momentExponent o)
    (scale N p) C ((Real.log N) ^ (3 + (∑ i, momentExponent o i) + d)) ha hb
  simp only [moment_monomial] at hc
  rw [gaussianEvent_normalized N hn p η (M j)] at hc
  have he := (setIntegral_map_equiv
    (μ := Binomial.Approximation.gaussianLaw p η
      (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)))
    (normalizeEquiv (scale N p) ha.ne')
    (fun x => momentValue o x.ofLp)
    (Analysis.GaussianRegularity.event (fun k i => (M j k i : ℝ))
      (WithLp.toLp 2 (fun k => (p : ℝ) * (∑ i, (M j k i : ℝ) * η i) / scale N p)))).symm
  change (∫ x in normalize (scale N p) ⁻¹' _,
    momentValue o (fun i => x i / scale N p) ∂_) =
    ∫ y in _, momentValue o y.ofLp ∂Measure.map (normalize (scale N p)) _ at he
  rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl,
    map_normalize_row p N hn η σ ν] at he
  change _ = _ at he
  simp only [id_eq, scale] at hc ⊢
  rw [he] at hc
  exact hc

end MajorityDynamics.Idealized.RowLimits
