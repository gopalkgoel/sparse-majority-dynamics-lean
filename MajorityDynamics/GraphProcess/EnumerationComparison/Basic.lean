import MajorityDynamics.GraphProcess.EnumerationBounds.Main
import MajorityDynamics.GraphProcess.BlockPairLaws.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
universe u

/-- Multiplicative comparison expressed without division, including null events. -/
def Sandwich (C P Q : ℝ) : Prop := Real.exp (-C) * Q ≤ P ∧ P ≤ Real.exp C * Q

def WeakComparisonTheorem (θ T : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
    T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n),
    (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
    (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
    ∀ (q : Local.Tilt n) (d : RowArray.Ambient y.part),
    RowArray.totals d = y.edge → RowArray.Regular p d →
    Sandwich (C*(p*N)^(2/7:ℝ)) ((GraphicalArray.law y.part y.edge).real {d})
      ((cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d})

def StrongComparisonTheorem (θ T CΓ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
    T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n),
    (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
    (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
    ∀ (q : Local.Tilt n) (E : Set (RowArray.Ambient y.part)),
    (∀ d ∈ E, RowArray.totals d = y.edge ∧ RowArray.Regular p d ∧
      RowArray.Gamma y.part y.edge CΓ p d) →
    Sandwich C ((GraphicalArray.law y.part y.edge).real E)
      ((cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real E)

end MajorityDynamics.GraphProcess.EnumerationComparison
