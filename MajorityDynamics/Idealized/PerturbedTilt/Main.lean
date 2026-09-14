import MajorityDynamics.Idealized.PerturbedTilt.Assembly

/-!
# Theorem 5.4: solving tilt and clause (b)

The public endpoint selects the actual Theorem 5.2 process. Constants are
chosen before N, real p, tau, integer sizes, and integer ordered edge counts.
Clauses (a) and (c) are not asserted here.
-/
noncomputable section
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse

theorem perturbed_tilt : PerturbedTiltTheorem := by
  intro θ hθlo hθhi n hk T δ hT hδ
  have hell := (processSelection_spec hθlo hθhi hT).1
  obtain ⟨T₁, hT₁, N₀, hN₀, hsolve⟩ :=
    perturbed_tilt_spec θ T δ hθlo hθhi hT hδ n (processExponent θ T) hell hk
  refine ⟨T₁, hT₁, tiltRate θ δ n,
    (tiltRate_bounds (responseRate_pos hθlo hθhi hk) hδ).1,
    max N₀ (processThreshold θ T), hN₀.trans (le_max_left _ _), ?_⟩
  intro N hN p hp₀ hp₁
  obtain ⟨hp, hspec, _⟩ := referenceData_agree hθlo hθhi hT
    ((le_max_right _ _).trans hN) hp₀ hp₁
  have heq := referenceDataReal_eq (θ := θ) (T := T) (N := N) hp
  rw [← heq] at hspec
  refine ⟨hp, hspec, ?_⟩
  exact hsolve N ((le_max_left _ _).trans hN) ⟨p, hp⟩ ⟨hp₀, hp₁⟩
    (referenceDataReal θ T N p) hspec

/-- The response bridge for the actual selected process and real density.
The tilt coordinates and response bounds belong to every solving tilt. -/
theorem perturbed_tilt_response :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
    ∀ T δ : ℝ, 1 < T → 0 < δ →
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
    ∃ hp : 0 < p ∧ p < 1,
      Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
        (referenceDataReal θ T N p) ∧
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N p T δ τ (referenceDataReal θ T N p) n η e →
        TiltConclusion N ⟨p, hp⟩ (referenceDataReal θ T N p) n η e τ T₁ (tiltRate θ δ n) ∧
        (∀ s, ResponseConclusion N ⟨p, hp⟩ (referenceDataReal θ T N p) n
          (naturalSizes η) s τ R C (responseRate θ n)) ∧
        ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
          ∃ σ : History (n + 1) → Row (n + 1),
            (∀ s, q s = processEffectiveTilt N ⟨p, hp⟩ (referenceDataReal θ T N p)
              n (naturalSizes η) s τ (σ s)) ∧
            (∀ s t, |σ s t| ≤ R) ∧
            ∀ s t, |σ s t - β n s t| ≤ B * (N : ℝ) ^ (-tiltRate θ δ n) := by
  intro θ hθlo hθhi n hk T δ hT hδ
  have hell := (processSelection_spec hθlo hθhi hT).1
  obtain ⟨T₁, hT₁, R, hR, C, hC, B, hB, N₀, hN₀, hsolve⟩ :=
    perturbed_tilt_response_spec θ T δ hθlo hθhi hT hδ n (processExponent θ T) hell hk
  refine ⟨T₁, hT₁, R, hR, C, hC, B, hB,
    max N₀ (processThreshold θ T), hN₀.trans (le_max_left _ _), ?_⟩
  intro N hN p hp₀ hp₁
  obtain ⟨hp, hspec, _⟩ := referenceData_agree hθlo hθhi hT
    ((le_max_right _ _).trans hN) hp₀ hp₁
  have heq := referenceDataReal_eq (θ := θ) (T := T) (N := N) hp
  rw [← heq] at hspec
  refine ⟨hp, hspec, ?_⟩
  exact hsolve N ((le_max_left _ _).trans hN) ⟨p, hp⟩ ⟨hp₀, hp₁⟩
    (referenceDataReal θ T N p) hspec

theorem naturalSizes_partition {n N : ℕ} (π : Fin N → History (n + 1)) :
    naturalSizes (partitionSizes π) = fun s => (Finset.univ.filter (fun v => π v = s)).card := by
  funext s
  simp [naturalSizes, partitionSizes]

/-- F1--F2 on actual cardinalities give the numerical input specification.
The regularity flag in `def:faithful` is unused by this numerical subtheorem. -/
theorem partition_faithful {n N : ℕ} {p T δ τ : ℝ} {a : Process.Data}
    (π : Fin N → History (n + 1)) (e : History (n + 1) → History (n + 1) → ℤ)
    (hF1 : ∀ s, |((Finset.univ.filter (fun v => π v = s)).card : ℝ) -
      ((a.state n).sizes s : ℝ) - τ * sizeScale N p n * ε n s| ≤
        T * sizeScale N p n * (N : ℝ) ^ (-δ))
    (hF2 : ∀ s t, |(e s t : ℝ) - (a.state n).edges s t *
      (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))| ≤
        T * betaScale N p n * (N : ℝ) ^ (-δ) * (N : ℝ) ^ 2 * p) :
    FaithfulNumericalData N p T δ τ a n (partitionSizes π) e := by
  refine ⟨?_, hF2⟩
  simpa [partitionSizes] using hF1

/-- A closed partition adapter with the same uniform quantifier order.
Its conclusion uses the actual fiber cardinalities as binomial trial sizes. -/
theorem perturbed_tilt_partition :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
    ∀ T δ : ℝ, 1 < T → 0 < δ →
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
    ∃ hp : 0 < p ∧ p < 1,
      Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
        (referenceDataReal θ T N p) ∧
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ π : Fin N → History (n + 1), ∀ e : History (n + 1) → History (n + 1) → ℤ,
      (∀ s, |((Finset.univ.filter (fun v => π v = s)).card : ℝ) -
        (((referenceDataReal θ T N p).state n).sizes s : ℝ) - τ * sizeScale N p n * ε n s| ≤
          T * sizeScale N p n * (N : ℝ) ^ (-δ)) →
      (∀ s t, |(e s t : ℝ) - ((referenceDataReal θ T N p).state n).edges s t *
        (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))| ≤
          T * betaScale N p n * (N : ℝ) ^ (-δ) * (N : ℝ) ^ 2 * p) →
      TiltConclusion N ⟨p, hp⟩ (referenceDataReal θ T N p) n (partitionSizes π) e τ T₁ δ₁ ∧
      ∃! q : Local.Tilt n, ∀ s t,
        ((Finset.univ.filter (fun v => π v = s)).card : ℝ) *
          Local.rowMean (fun t => (Finset.univ.filter (fun v => π v = t)).card) q s t = (e s t : ℝ) := by
  intro θ hθlo hθhi n hk T δ hT hδ
  obtain ⟨T₁, hT₁, δ₁, hδ₁, N₀, hN₀, h⟩ := perturbed_tilt θ hθlo hθhi n hk T δ hT hδ
  refine ⟨T₁, hT₁, δ₁, hδ₁, N₀, hN₀, ?_⟩
  intro N hN p hp₀ hp₁
  obtain ⟨hp, hspec, h⟩ := h N hN p hp₀ hp₁
  refine ⟨hp, hspec, ?_⟩
  intro τ hτ hτT π e hF1 hF2
  have hc := h τ hτ hτT (partitionSizes π) e (partition_faithful π e hF1 hF2)
  refine ⟨hc, ?_⟩
  simpa only [naturalSizes_partition, Local.Solves, realEdges] using hc.exists_unique

end MajorityDynamics.Idealized.PerturbedTilt

