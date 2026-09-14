import MajorityDynamics.GraphProcess.RowExactTotals.Geometry
import MajorityDynamics.GraphProcess.RowExactTotals.Numerics

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal Probability.ConditionedBinomialFourier
universe u

/-- The finitely many history constants are absorbed before varying any data. -/
theorem uniform_block_lower (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (n : ℕ) (T : ℝ) (hT : 1 < T) (φ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V],
      Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ s : History (n+1),
      IsProbabilityMeasure (Local.rowCondition y.sizes q s) ∧
      IsProbabilityMeasure (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)) ∧
      ((N : ℝ)^2*p)^(-((Fintype.card (History (n+1)) : ℝ)/2+1)) ≤
        (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)).real
          {x | ∀ t, (∑ j, (x j t : ℤ)) = y.edge s t} := by
  classical
  have hb (s : History (n+1)) : ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      IsProbabilityMeasure (Local.rowCondition y.sizes q s) ∧
      IsProbabilityMeasure (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)) ∧
      ((N : ℝ)^2*p)^(-((Fintype.card (History (n+1)) : ℝ)/2+1)) ≤
        (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)).real
          {x | ∀ t, (∑ j, (x j t : ℤ)) = y.edge s t} := by
    obtain ⟨c,hc,N₁,h₁⟩ := uniform_block_local_clt θ hθlo hθhi n T hT φ s
    obtain ⟨N₂,h₂⟩ := eventually_absorb_constant hθlo hθhi hT hc
    refine ⟨max N₁ N₂, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    have hclt := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q ha
    have habs := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
    refine ⟨hclt.1,hclt.2.1,?_⟩
    apply (habs.2 ((Fintype.card (History (n+1)) : ℝ)/2)).trans
    simpa only [neg_div] using hclt.2.2
  choose N₀ h₀ using hb
  refine ⟨Finset.univ.sup N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha s
  exact h₀ s N ((Finset.le_sup (f := N₀) (Finset.mem_univ s)).trans hN)
    V hcard p hlo hhi y q ha

end MajorityDynamics.GraphProcess.RowExactTotals
