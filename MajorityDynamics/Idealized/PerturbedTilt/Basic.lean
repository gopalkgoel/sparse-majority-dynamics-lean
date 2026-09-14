import MajorityDynamics.Idealized.LinearResponse.Main

/-!
# Numerical faithful data and the solving-tilt contract

Source: `def:faithful`, `thm:perturbed-evolution`, Appendix E.5.
The level `n` is paper history length `k = n + 1`. Edge entries count ordered
half-edges on the diagonal. The numerical theorem needs only F1 and F2.
-/

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse

variable {n : ℕ}

/-- F1 and F2, with no analytic consequences included as assumptions. -/
structure FaithfulNumericalData (N : ℕ) (p T δ τ : ℝ) (a : Process.Data) (n : ℕ)
    (η : History (n + 1) → ℤ) (e : History (n + 1) → History (n + 1) → ℤ) : Prop where
  sizes : ∀ s, |(η s : ℝ) - ((a.state n).sizes s : ℝ) -
      τ * sizeScale N p n * ε n s| ≤ T * sizeScale N p n * (N : ℝ) ^ (-δ)
  edges : ∀ s t, |(e s t : ℝ) - (a.state n).edges s t *
      (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))| ≤
        T * betaScale N p n * (N : ℝ) ^ (-δ) * (N : ℝ) ^ 2 * p

def naturalSizes (η : History (n + 1) → ℤ) : Local.Sizes n := fun s => (η s).toNat
def realEdges (e : History (n + 1) → History (n + 1) → ℤ) : Local.EdgeCounts n :=
  fun s t => (e s t : ℝ)

/-- The literal logarithm in clause (b); its domains are proved separately. -/
def effectiveParameter (p : ℝ) (ref sizes : Local.Sizes n) (q : Local.Tilt n)
    (s t : History (n + 1)) : ℝ :=
  Real.log ((q s t : ℝ) * residual p ref sizes s t /
    ((1 - (q s t : ℝ)) * p * (ref t : ℝ)))

structure TiltConclusion (N : ℕ) (p : Binomial.Probability) (a : Process.Data) (n : ℕ)
    (η : History (n + 1) → ℤ) (e : History (n + 1) → History (n + 1) → ℤ)
    (τ T₁ δ₁ : ℝ) : Prop where
  sizes_pos : ∀ s, 0 < η s
  sizes_cast : ∀ s, ((naturalSizes η s : ℕ) : ℝ) = (η s : ℝ)
  trials_cast : ∀ s t, (Local.trials (naturalSizes η) s t : ℝ) =
    (η t : ℝ) - diagonal s t
  reference_residual_pos : ∀ s t,
    0 < residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t
  residual_pos : ∀ s t,
    0 < residual (p : ℝ) (a.state n).sizes (naturalSizes η) s t
  exists_unique : ∃! q : Local.Tilt n,
    Local.Solves (naturalSizes η) (realEdges e) q
  approximation : ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
    (∀ s, 0 < historyMass (naturalSizes η) s (q s)) ∧
    (∀ s t, 0 < (1 - (q s t : ℝ)) * (p : ℝ) * ((a.state n).sizes t : ℝ)) ∧
    (∀ s t, 0 < (1 - (a.tilt n s t : ℝ)) * (p : ℝ) * ((a.state n).sizes t : ℝ)) ∧
    ∀ s t, |effectiveParameter (p : ℝ) (a.state n).sizes (naturalSizes η) q s t -
        effectiveParameter (p : ℝ) (a.state n).sizes (a.state n).sizes (a.tilt n) s t -
        τ * betaScale N (p : ℝ) n * β n s t| ≤ T₁ * betaScale N (p : ℝ) n * (N : ℝ) ^ (-δ₁)

/-- Constants precede the size, real density, lead, and both integer arrays. -/
def PerturbedTiltTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
  ∀ T δ : ℝ, 1 < T → 0 < δ →
  ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
  ∃ hp : 0 < p ∧ p < 1,
    Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
      (referenceDataReal θ T N p) ∧
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N p T δ τ (referenceDataReal θ T N p) n η e →
      TiltConclusion N ⟨p, hp⟩ (referenceDataReal θ T N p) n η e τ T₁ δ₁

/-- Actual partition cardinalities; no graph attainability is imposed. -/
def partitionSizes {N : ℕ} (π : Fin N → History (n + 1)) : History (n + 1) → ℤ :=
  fun s => ((Finset.univ.filter (fun v => π v = s)).card : ℤ)

end MajorityDynamics.Idealized.PerturbedTilt
