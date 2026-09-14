import MajorityDynamics.GraphProcess.GammaNumerator.Probability
import MajorityDynamics.GraphProcess.GammaNumerator.Adapters

/-! Complete B.3 Step 4: the exponentially small graph-side numerator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GammaNumerator
open Universal
universe u

/-- Original-window graph, pushforward-array, and literal paper numerator bounds
with one constant and one threshold, fixed before all varying data. -/
theorem uniform_numerator {θ T K : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ π : V → History (n+1),
      (∀ s, (N : ℝ)/T ≤ (Local.partSizes π s : ℝ)) →
      (SimpleGraph.binomialRandom V p).real {G |
        ¬ RowArray.Gamma π (RowArray.totals (RowArray.graphArray π G)) C p
          (RowArray.graphArray π G) ∧ RowArray.Regular p (RowArray.graphArray π G)} ≤
          Real.exp (-K*N) ∧
      ((SimpleGraph.binomialRandom V p).map (RowArray.graphArray π)).real
        {d | ¬ RowArray.Gamma π (RowArray.totals d) C p d ∧ RowArray.Regular p d} ≤
          Real.exp (-K*N) ∧
      ∀ m : History (n+1) → History (n+1) → ℤ,
        ((SimpleGraph.binomialRandom V p).map (RowArray.graphArray π)).real
          {d | ¬ RowArray.Gamma π m C p d ∧ d ∈ RowArray.history π ∧
            RowArray.Regular p d ∧ d ∈ RowArray.exactTotals π m} ≤ Real.exp (-K*N) := by
  obtain ⟨N₁,h₁⟩ := uniform_regime n hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_exp_absorption (Fintype.card (History (n+1))) K
  refine ⟨numeratorConstant T K, numeratorConstant_ge_one T K, max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi π hsizes
  obtain ⟨_,hp,_,_,hs2,htol,hratio⟩ :=
    h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi π hsizes
  have hb := graph_numerator_bound π p hT hK.le hp hcard hsizes hs2 hratio
    (by simpa only [hcard] using htol)
  have hg := hb.trans (h₂ N ((le_max_right _ _).trans hN))
  refine ⟨hg, ?_, fun m => (paper_numerator_le π p m _).trans hg⟩
  change (arrayLaw π p).real _ ≤ _
  rw [arrayLaw_real]
  exact hg

/-- Literal real-density form. Positivity and p<1 are derived uniformly before
forming the actual random graph law, with no extra density assumption. -/
theorem uniform_numerator_real {θ T K : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∃ hp : 0 < p ∧ p < 1, ∀ π : V → History (n+1),
      (∀ s, (N : ℝ)/T ≤ (Local.partSizes π s : ℝ)) →
      let q : unitInterval := ⟨p,hp.1.le,hp.2.le⟩
      (SimpleGraph.binomialRandom V q).real {G |
        ¬ RowArray.Gamma π (RowArray.totals (RowArray.graphArray π G)) C p
          (RowArray.graphArray π G) ∧ RowArray.Regular p (RowArray.graphArray π G)} ≤
          Real.exp (-K*N) ∧
      ((SimpleGraph.binomialRandom V q).map (RowArray.graphArray π)).real
        {d | ¬ RowArray.Gamma π (RowArray.totals d) C p d ∧ RowArray.Regular p d} ≤
          Real.exp (-K*N) ∧
      ∀ m : History (n+1) → History (n+1) → ℤ,
        ((SimpleGraph.binomialRandom V q).map (RowArray.graphArray π)).real
          {d | ¬ RowArray.Gamma π m C p d ∧ d ∈ RowArray.history π ∧
            RowArray.Regular p d ∧ d ∈ RowArray.exactTotals π m} ≤ Real.exp (-K*N) := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_numerator n hθlo hθhi hT hK
  refine ⟨C,hC,max N₁ (Probability.DegreeConcentration.gammaThreshold T),?_⟩
  intro N hN V inst hcard p hlo hhi
  have hp := Probability.DegreeConcentration.density_pos_lt_one θ T hθlo hT N
    ((le_max_right _ _).trans hN) p ⟨hlo,hhi⟩
  refine ⟨hp,?_⟩
  intro π hsizes
  exact h₁ N ((le_max_left _ _).trans hN) V hcard ⟨p,hp.1.le,hp.2.le⟩ hlo hhi π hsizes

end MajorityDynamics.GraphProcess.GammaNumerator
