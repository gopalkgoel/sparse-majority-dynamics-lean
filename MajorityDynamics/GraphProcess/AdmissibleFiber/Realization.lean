import MajorityDynamics.GraphProcess.GoodArrays.Main
import MajorityDynamics.GraphProcess.GraphicalArray.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace MajorityDynamics.GraphProcess.AdmissibleFiber
universe u
variable {V : Type*} [Fintype V] {n : ℕ}

/-- A single array and graph witness all the original constraints at once. -/
structure Realizes (y : Local.CoarseData V n) (T p : ℝ)
    (d : RowArray.Ambient y.part) (G : SimpleGraph V) : Prop where
  good : d ∈ GoodArrays.E0 y T p
  totals : RowArray.totals d = y.edge
  history : d ∈ RowArray.history y.part
  regular : RowArray.Regular p d
  gamma_one : RowArray.Gamma y.part y.edge 1 p d
  gamma : ∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d
  degrees : History.degreeArray y.part G = RowArray.values d
  array_eq : RowArray.graphArray y.part G = d
  coarse_event : G ∈ CoarseKernel.E p y
  actual : CoarseKernel.actualCoarse p G (CoarseKernel.initial y) n = y
  compatible_actual : ∀ c : V → Bool, FineState.CompatibleInitial y.part c →
    CoarseKernel.actualCoarse p G c n = y
  graph_gamma_one : RowArray.Gamma y.part y.edge 1 p (RowArray.graphArray y.part G)
  graph_gamma : ∀ C : ℝ, 1 ≤ C →
    RowArray.Gamma y.part y.edge C p (RowArray.graphArray y.part G)
  attainable : CoarseKernel.pAttainable p y

/-- Pure reconstruction: every supplied original graphical/history/regular array
lies in the literal coarse event. No density or enumeration input is involved. -/
theorem graph_mem_E (y : Local.CoarseData V n) (p : ℝ)
    (d : RowArray.Ambient y.part) (G : SimpleGraph V)
    (htot : RowArray.totals d = y.edge) (hhist : d ∈ RowArray.history y.part)
    (hreg : RowArray.Regular p d) (hr : y.reg = true)
    (hG : History.degreeArray y.part G = RowArray.values d) : G ∈ CoarseKernel.E p y := by
  have hd : RowArray.graphArray y.part G = d :=
    GraphicalArray.values_injective y.part ((RowArray.values_graphArray _ _).trans hG)
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [← GraphicalArray.realRow_graphArray, hd]
    exact hhist v
  · rw [hG]
    exact htot
  · rw [hr, CoarseKernel.flag_true, hG]
    exact hreg

/-- Finite assembly, retaining one literal graph and array throughout. -/
theorem realizes_of_array (y : Local.CoarseData V n) (T p : ℝ)
    (d : RowArray.Ambient y.part) (G : SimpleGraph V)
    (hd : d ∈ GoodArrays.E0 y T p)
    (htot : RowArray.totals d = y.edge) (hhist : d ∈ RowArray.history y.part)
    (hreg : RowArray.Regular p d) (hr : y.reg = true)
    (hg : RowArray.Gamma y.part y.edge 1 p d)
    (hmono : ∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d)
    (hG : History.degreeArray y.part G = RowArray.values d) : Realizes y T p d G := by
  have he := graph_mem_E y p d G htot hhist hreg hr hG
  have ha : RowArray.graphArray y.part G = d :=
    GraphicalArray.values_injective y.part ((RowArray.values_graphArray _ _).trans hG)
  exact ⟨hd, htot, hhist, hreg, hg, hmono, hG, ha, he,
    (CoarseKernel.raw_agreement p y G he).2.2,
    fun c hc => (CoarseKernel.E_iff_actual p y G c hc).mp he,
    ha ▸ hg, fun C hC => ha ▸ hmono C hC,
    (CoarseKernel.E_nonempty_iff p y).mp ⟨G, he⟩⟩

/-- Original density, sizes, ordered counts, separation and true regularity
alone imply actual realization. The threshold precedes every varying datum. -/
theorem uniform_realization {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → GoodArrays.Separated y T p → y.reg = true →
      ∃ (d : RowArray.Ambient y.part) (G : SimpleGraph V), Realizes y T p d G := by
  obtain ⟨N₁, h₁⟩ := GoodArrays.uniform_nonempty_and_positive n hθlo hθhi hT
  obtain ⟨N₂, h₂⟩ := GoodArrays.uniform_inclusion_graphical n hθlo hθhi hT
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts hsep hr
  obtain ⟨d, hd⟩ := (h₁ N (by omega) V hcard p hlo hhi y hsizes hcounts).1
  obtain ⟨htot, hhist, hreg, hg, hmono, G, hG⟩ :=
    h₂ N (by omega) V hcard p hlo hhi y hsizes hcounts hsep d hd
  exact ⟨d, G, realizes_of_array y T p d G hd htot hhist hreg hr hg hmono hG⟩

end MajorityDynamics.GraphProcess.AdmissibleFiber
