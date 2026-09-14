import MajorityDynamics.GraphProcess.AdmissibleFiber.Main
import MajorityDynamics.GraphProcess.GoodArrays.Sparse
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Separate sparse-range versions; all original finite laws and predicates
are retained. Constants precede every varying finite datum. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology
namespace MajorityDynamics.GraphProcess.AdmissibleFiber
open Universal
universe u

theorem uniform_realization_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → GoodArrays.Separated y T p → y.reg = true →
      ∃ (d : RowArray.Ambient y.part) (G : SimpleGraph V), Realizes y T p d G := by
  obtain ⟨N₁, h₁⟩ := GoodArrays.uniform_nonempty_and_positive_sparse n hθlo hθhi hT
  obtain ⟨N₂, h₂⟩ := GoodArrays.uniform_inclusion_graphical_sparse n hθlo hθhi hT
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts hsep hr
  obtain ⟨d, hd⟩ := (h₁ N (by omega) V hcard p hlo hhi y hsizes hcounts).1
  obtain ⟨htot, hhist, hreg, hg, hmono, G, hG⟩ :=
    h₂ N (by omega) V hcard p hlo hhi y hsizes hcounts hsep d hd
  exact ⟨d, G, realizes_of_array y T p d G hd htot hhist hreg hr hg hmono hG⟩

theorem uniform_realization_and_laws_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∃ hp : 0 < p ∧ p < 1,
      let pI : unitInterval := ⟨p, hp.1.le, hp.2.le⟩
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → GoodArrays.Separated y T p → y.reg = true →
      (∃ (d : RowArray.Ambient y.part) (G : SimpleGraph V), Realizes y T p d G) ∧
        ActualLaws pI y := by
  obtain ⟨N₁, h₁⟩ := uniform_realization_sparse n hθlo hθhi hT
  obtain ⟨N₂, h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L := 1) zero_lt_one (U := 1/2) (by norm_num) (M := 1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi
  have hw := h₂ N (by omega) p hlo hhi
  have hp : 0 < p ∧ p < 1 := ⟨hw.2.1, lt_of_le_of_lt hw.2.2.2.2 (by norm_num)⟩
  refine ⟨hp, ?_⟩
  dsimp only
  intro y hsizes hcounts hsep hr
  obtain ⟨d, G, hg⟩ := h₁ N (by omega) V hcard p hlo hhi y hsizes hcounts hsep hr
  exact ⟨⟨d, G, hg⟩, actual_laws ⟨p, hp.1.le, hp.2.le⟩ y hp.1 hp.2 hg.attainable hr⟩

/-- Closed original-LA wrapper. No condition on phi is needed: only the four
coarse fields are used, and neither a tilt nor positivity certificate is imported. -/
theorem uniform_admissible_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∃ hp : 0 < p ∧ p < 1,
      let pI : unitInterval := ⟨p, hp.1.le, hp.2.le⟩
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.CoreAdmissible y q T φ p →
      (∃ (d : RowArray.Ambient y.part) (G : SimpleGraph V), Realizes y T p d G) ∧
        ActualLaws pI y := by
  obtain ⟨N₀, h₀⟩ := uniform_realization_and_laws_sparse n hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi
  obtain ⟨hp, hlaws⟩ := h₀ N hN V hcard p hlo hhi
  refine ⟨hp, ?_⟩
  dsimp only
  intro y q φ ha
  apply hlaws y _ _ ha.separation ha.regularity
  · intro s
    simpa only [← hcard, div_eq_mul_inv, mul_comm] using ha.sizes s
  · intro s t
    simpa only [← hcard, Local.CoarseData.realEdges, Local.edgeScale, mul_div_assoc,
      mul_assoc] using ha.edge_scale s t

/-- Unit-interval consumer with the same uniformity and no separate interior-p
hypothesis. All output laws are the already defined graph/fiber/kernel laws. -/
theorem uniform_admissible_unit_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.CoreAdmissible y q T φ p →
      (0 < (p : ℝ) ∧ (p : ℝ) < 1) ∧
      (∃ (d : RowArray.Ambient y.part) (G : SimpleGraph V), Realizes y T p d G) ∧
        ActualLaws p y := by
  obtain ⟨N₀, h₀⟩ := uniform_admissible_sparse n hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q φ ha
  obtain ⟨hp, h⟩ := h₀ N hN V hcard p hlo hhi
  exact ⟨hp, h y q φ ha⟩

end MajorityDynamics.GraphProcess.AdmissibleFiber
