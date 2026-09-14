import MajorityDynamics.Local.Admissibility
import MajorityDynamics.Idealized.PerturbedTilt.Main

/-!
# The complete perturbed evolution contract

Source: `thm:perturbed-evolution`, `def:faithful`, Appendix E.5.
Lean level `n` represents paper history length `k = n + 1`; the output
has histories of length `n + 2`. The reference is the selected Theorem 5.2
process and its next level, including the floor-rounded reference sizes.
-/
noncomputable section
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt

variable {V : Type*} [Fintype V] {n : ℕ}

/-- Faithfulness adds only the actual flag and literal F1/F2 to coarse data. -/
def Faithful (N : ℕ) (p T δ τ : ℝ) (a : Process.Data)
    (y : Local.CoarseData V n) : Prop :=
  y.reg = true ∧ FaithfulNumericalData N p T δ τ a n y.integerSizes y.edge

@[simp] theorem naturalSizes_coarse (y : Local.CoarseData V n) :
    naturalSizes y.integerSizes = y.sizes := by
  funext s
  simp [naturalSizes]

@[simp] theorem realEdges_coarse (y : Local.CoarseData V n) :
    PerturbedTilt.realEdges y.edge = y.realEdges := rfl

/-- Both estimates use the same solving tilt and the exact local template. -/
structure TemplateConclusion (N : ℕ) (p : ℝ) (a : Process.Data)
    (sz : Local.Sizes n) (e : Local.EdgeCounts n) (q : Local.Tilt n)
    (τ T₁ δ₁ : ℝ) : Prop where
  sizes : ∀ u : History (n + 2),
    |Local.templateSizes sz q u - ((a.state (n + 1)).sizes u : ℝ) -
      τ * sizeScale N p (n + 1) * ε (n + 1) u| ≤
        T₁ * sizeScale N p (n + 1) * (N : ℝ) ^ (-δ₁)
  edges : ∀ u v : History (n + 2),
    |Local.templateEdges sz e q u v - (a.state (n + 1)).edges u v *
      (1 + τ * betaScale N p (n + 1) *
        (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
      T₁ * betaScale N p (n + 1) * (N : ℝ) ^ (-δ₁) * (N : ℝ) ^ 2 * p

/-- Domain, global uniqueness, all nine LA conditions, (b), and both (c) bounds. -/
structure EvolutionConclusion (N : ℕ) (p : Binomial.Probability) (a : Process.Data)
    (y : Local.CoarseData V n) (τ T₁ δ₁ φ₁ : ℝ) : Prop where
  tilt : TiltConclusion N p a n y.integerSizes y.edge τ T₁ δ₁
  admissible : ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
    Local.Admissible y q T₁ φ₁ (p : ℝ)
  template : ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
    TemplateConclusion N (p : ℝ) a y.sizes y.realEdges q τ T₁ δ₁

/-- Constants precede density, lead, vertex type, partition, counts, and flag. -/
def PerturbedEvolutionTheorem : Prop :=
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
    ∀ y : Local.CoarseData V n,
      Faithful N p T δ τ (referenceDataReal θ T N p) y →
      EvolutionConclusion N ⟨p, hp⟩ (referenceDataReal θ T N p) y τ T₁ δ₁ φ₁

end MajorityDynamics.Idealized.PerturbedEvolution
