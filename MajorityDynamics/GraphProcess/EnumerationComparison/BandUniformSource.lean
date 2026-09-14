import MajorityDynamics.GraphProcess.EnumerationComparison.UniformSource
import MajorityDynamics.GraphProcess.EnumerationComparison.BandApplicability
import MajorityDynamics.GraphProcess.EnumerationBounds.BandPreparation

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Universal EnumerationBounds
open Literature.DegreeEnumeration Probability.NeighborhoodBulk
universe u

/-- The two cited enumeration estimates on every literal block vector, with a
single global threshold. All source applicability conditions are discharged. -/
theorem uniform_band_source {θ η T : ℝ} (hη : 0 < η) (hηθ : η ≤ θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ (n : ℕ) (p : ℝ), T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-η) →
    ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
    (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
    (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
    RowArray.totals d = y.edge → RowArray.Regular p d →
    Prepared y d T p ∧
    (∀ s, RelativeApproximation (1/2)
      ((graphDegreeLaw (Fin (y.sizes s)) (y.edge s s/2).toNat).real {vec y d s s})
      ((graphBinomialLaw (Fin (y.sizes s)) (y.edge s s/2).toNat).real {vec y d s s} *
        graphCorrection (y.edge s s/2).toNat (vec y d s s))) ∧
    (∀ s t, s ≠ t → RelativeApproximation (1/2)
      ((bipartiteDegreeLaw (Fin (y.sizes s)) (Fin (y.sizes t)) (y.edge s t).toNat).real
        {(vec y d s t,vec y d t s)})
      ((bipartiteBinomialLaw (Fin (y.sizes s)) (Fin (y.sizes t)) (y.edge s t).toNat).real
        {(vec y d s t,vec y d t s)} *
        bipartiteCorrection (y.edge s t).toNat (vec y d s t) (vec y d t s))) := by
  have hT0 : 0 < T := by linarith
  have hK : 1 ≤ 4*T^4 := by nlinarith [one_le_pow₀ hT.le (n := 4)]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (graph_enumeration_band θ η (4*T^4)
    hη hηθ hθhi hK)
  obtain ⟨M',hM'⟩ := eventually_atTop.mp (bipartite_enumeration_band θ η (4*T^4)
    hη hηθ hθhi hK)
  obtain ⟨L,hL⟩ := uniform_band_preparation hη hθhi hT
  refine ⟨max L ⌈T*(max M M' : ℕ)⌉₊, ?_⟩
  intro N hN V inst hcard n p hlo hhi y d hsizes hcounts htot hreg
  have h := hL N ((le_max_left _ _).trans hN) V hcard n p hlo hhi y d hsizes hcounts hreg
  have hsz : ∀ s, max M M' ≤ y.sizes s := fun s =>
    block_threshold hT0 ((le_max_right _ _).trans hN) (hsizes s)
  have hlo' : T⁻¹*(Fintype.card V : ℝ)^(-θ) < p := by simpa only [hcard] using hlo
  have hhi' : p < T*(Fintype.card V : ℝ)^(-η) := by simpa only [hcard] using hhi
  refine ⟨h, ?_, ?_⟩
  · intro s
    exact hM (y.sizes s) ((le_max_left _ _).trans (hsz s)) _
      (prepared_internal_band y d hη hηθ hθhi hT h hlo' hhi' s) _
      (vec_source_internal y d h htot s)
  · intro s t hst
    exact hM' (y.sizes t) ((le_max_right _ _).trans (hsz t)) _ _
      (prepared_cross_band y d hη hηθ hθhi hT h hlo' hhi' s t) _ _
      (vec_source_cross y d h htot s t hst)

end MajorityDynamics.GraphProcess.EnumerationComparison
