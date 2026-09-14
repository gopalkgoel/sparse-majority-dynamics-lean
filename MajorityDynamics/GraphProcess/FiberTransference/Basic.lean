import MajorityDynamics.GraphProcess.FiberTransference.Gamma

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

/-- Proposition 3.8 on the literal degree-array event under actual Lambda.
The reference law conditions on original histories and every exact total.
No comparison, positivity or Gamma hypothesis remains. -/
def TransferTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
    ∀ E : Set (RowArray.Ambient y.part),
    (CoarseKernel.Lambda p y).real {σ | σ.deg ∉ RowArray.values '' E} ≤
      Real.exp (-(N : ℝ)) + C *
        (cond (RowConcentration.conditionedLaw y q)
          (RowArray.exactTotals y.part y.edge)).real Eᶜ

/-- Literal real-density form; interior density is an output of the original
window, so this adds no hypothesis to the manuscript. -/
def TransferRealTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∃ hp : 0 < p ∧ p < 1,
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
    ∀ E : Set (RowArray.Ambient y.part),
    (CoarseKernel.Lambda ⟨p,hp.1.le,hp.2.le⟩ y).real {σ | σ.deg ∉ RowArray.values '' E} ≤
      Real.exp (-(N : ℝ)) + C *
        (cond (RowConcentration.conditionedLaw y q)
          (RowArray.exactTotals y.part y.edge)).real Eᶜ

end MajorityDynamics.GraphProcess.FiberTransference
