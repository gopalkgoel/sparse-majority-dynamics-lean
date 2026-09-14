import MajorityDynamics.Idealized.PerturbedEvolution.Main

/-! An unbundled application of Theorem 5.4. The input is an arbitrary finite
partition, integer count array and flag, with exactly the structural and
faithfulness conditions of the paper. No graph realization is requested. -/
noncomputable section
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt

/-- Apply the closed theorem directly to ordinary partition/count/flag inputs.
The comparison constants precede every varying combinatorial input. -/
theorem perturbed_evolution_of_partition :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
    ∀ T δ : ℝ, 1 < T → 0 < δ →
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧
    ∃ φ₁ : ℝ, 0 < φ₁ ∧ φ₁ < 1 / 2 ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
    ∃ hp : 0 < p ∧ p < 1,
      Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
        (referenceDataReal θ T N p) ∧
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V], Fintype.card V = N →
      ∀ (π : V → History (n + 1)) (m : History (n + 1) → History (n + 1) → ℤ)
        (symm : ∀ s t, m s t = m t s) (even : ∀ s, Even (m s s))
        (nonneg : ∀ s t, 0 ≤ m s t)
        (upper : ∀ s t, m s t ≤ (Local.partSizes π s : ℤ) *
          ((Local.partSizes π t : ℤ) - if s = t then 1 else 0))
        (reg : Bool), reg = true →
      (∀ s, |(Local.partSizes π s : ℝ) -
          (((referenceDataReal θ T N p).state n).sizes s : ℝ) -
          τ * sizeScale N p n * ε n s| ≤
        T * sizeScale N p n * (N : ℝ) ^ (-δ)) →
      (∀ s t, |(m s t : ℝ) - ((referenceDataReal θ T N p).state n).edges s t *
          (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))| ≤
        T * betaScale N p n * (N : ℝ) ^ (-δ) * (N : ℝ) ^ 2 * p) →
      EvolutionConclusion N ⟨p, hp⟩ (referenceDataReal θ T N p)
        (⟨π, m, symm, even, nonneg, upper, reg⟩ : Local.CoarseData V n)
        τ T₁ δ₁ φ₁ := by
  intro θ hθlo hθhi n hk T δ hT hδ
  obtain ⟨T₁, hT₁, δ₁, hδ₁, φ₁, hφ₁, hφ₁hi, N₀, hN₀, h⟩ :=
    perturbed_evolution_finite θ hθlo hθhi n hk T δ hT hδ
  refine ⟨T₁, hT₁, δ₁, hδ₁, φ₁, hφ₁, hφ₁hi, N₀, hN₀, ?_⟩
  intro N hN p hp₀ hp₁
  obtain ⟨hp, ha, happly⟩ := h N hN p hp₀ hp₁
  refine ⟨hp, ha, ?_⟩
  intro τ hτ hτT V inst hcard π m symm even nonneg upper reg hreg hF1 hF2
  apply happly τ hτ hτT V hcard
  refine ⟨hreg, ?_, hF2⟩
  simpa only [Local.CoarseData.integerSizes, Local.CoarseData.sizes,
    Int.cast_natCast] using hF1

end MajorityDynamics.Idealized.PerturbedEvolution
