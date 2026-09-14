import MajorityDynamics.GraphProcess.RowGamma.Main
import MajorityDynamics.GraphProcess.GammaNumerator.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
universe u

/-- A single fixed constant simultaneously serves the direct row estimate and
the exponentially small graph numerator. The graph denominator is a separate result. -/
theorem uniform_shared_constant {θ T φ K : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∃ hp : 0 < p ∧ p < 1,
      Conclusion y q C p A N ∧
      (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real {G |
        ¬ RowArray.Gamma y.part (RowArray.totals (RowArray.graphArray y.part G)) C p
          (RowArray.graphArray y.part G) ∧ RowArray.Regular p (RowArray.graphArray y.part G)} ≤
          Real.exp (-K*N) ∧
      (((SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).map
        (RowArray.graphArray y.part)).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d ∧ d ∈ RowArray.history y.part ∧
          RowArray.Regular p d ∧ d ∈ RowArray.exactTotals y.part y.edge}) ≤ Real.exp (-K*N) := by
  classical
  obtain ⟨Cg,hCg,Ng,hg⟩ := GammaNumerator.uniform_numerator_real n hθlo hθhi hT hK
  refine ⟨max (rowConstant T φ) Cg,(rowConstant_ge_one hφ).trans (le_max_left _ _),?_⟩
  intro A _
  obtain ⟨Nr,hr⟩ := uniform_complete (A := A) n hθlo hθhi hT hφ
  refine ⟨max Ng Nr,?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  obtain ⟨hp,hgraph⟩ := hg N (by omega) V hcard p hlo hhi
  have hgg := hgraph y.part (fun s => by
    simpa only [← hcard, Local.CoarseData.sizes, div_eq_mul_inv, mul_comm] using ha.sizes s)
  refine ⟨hp,hr N (by omega) V hcard p hlo hhi y q ha _ (le_max_left _ _),?_,?_⟩
  · apply le_trans (measureReal_mono (show
        {G | ¬ RowArray.Gamma y.part (RowArray.totals (RowArray.graphArray y.part G))
          (max (rowConstant T φ) Cg) p (RowArray.graphArray y.part G) ∧
          RowArray.Regular p (RowArray.graphArray y.part G)} ⊆
        {G | ¬ RowArray.Gamma y.part (RowArray.totals (RowArray.graphArray y.part G))
          Cg p (RowArray.graphArray y.part G) ∧ RowArray.Regular p (RowArray.graphArray y.part G)}
        from fun _ hd => ⟨fun hc => hd.1 (gamma_mono (le_max_right _ _) hc),hd.2⟩)) hgg.1
  · apply le_trans (measureReal_mono (show
        {d | ¬ RowArray.Gamma y.part y.edge (max (rowConstant T φ) Cg) p d ∧
          d ∈ RowArray.history y.part ∧ RowArray.Regular p d ∧
          d ∈ RowArray.exactTotals y.part y.edge} ⊆
        {d | ¬ RowArray.Gamma y.part y.edge Cg p d ∧ d ∈ RowArray.history y.part ∧
          RowArray.Regular p d ∧ d ∈ RowArray.exactTotals y.part y.edge}
        from fun _ hd => ⟨fun hc => hd.1 (gamma_mono (le_max_right _ _) hc),hd.2⟩)) (hgg.2.2 y.edge)

end MajorityDynamics.GraphProcess.RowGamma
