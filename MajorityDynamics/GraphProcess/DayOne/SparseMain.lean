import MajorityDynamics.GraphProcess.DayOne.Main
import MajorityDynamics.GraphProcess.DayOne.SparseRates
import MajorityDynamics.GraphProcess.DayOne.SparseConcentration

noncomputable section
open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.GraphProcess.DayOne
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedEvolution
open Binomial.Approximation (SparseRange)

theorem day_one_sparse (θ T : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ p : Binomial.Probability,
      SparseRange θ T N p → ∀ a : Process.Data,
      a.state 0 = Process.initialState N p →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V], Fintype.card V = N → ∀ c : V → Bool,
      (Finset.univ.filter fun v => c v = false).card = N/2 + ⌊τ*Real.sqrt N⌋₊ →
      (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
        {G | ¬Faithful N p 1 ((1-θ)/4) τ a (CoarseKernel.actualCoarse p G c 0)} ≤ ε ∧
      1-ε ≤ (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
        {G | Faithful N p 1 ((1-θ)/4) τ a (CoarseKernel.actualCoarse p G c 0)} := by
  have hT0 : 0 < T := by linarith
  have hnum := eventually_faithful_errors_sparse hθlo hθhi hT
    (show 0 ≤ 20*(T+1)^2 by positivity)
  have hinv : ∀ᶠ N : ℕ in atTop, (N : ℝ)^(-(1:ℝ)) ≤ ε := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ)^(-(1:ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_le_nhds hε)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    ((eventually_ge_atTop (1)).and
      (hnum.and ((uniform_concentration_sparse hθlo hθhi hT).and hinv)))
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro N hN p hp a ha'
  obtain ⟨hNb,hnumeric,hprob,hinvN⟩ := hN₀ N ((le_max_right _ _).trans hN)
  intro τ hτlo hτhi V inst hcard c hplus
  have hτ0 : 0 ≤ τ := (inv_nonneg.mpr hT0.le).trans hτlo
  have hnumN := hnumeric p hp
  let π := History.actualHistory (⊥ : SimpleGraph V) c 1
  have hπ : ∀ G : SimpleGraph V, History.actualHistory G c 1 = π := by
    intro G
    funext v
    exact (initial_history_iff G c v _).mpr
      ((initial_history_iff (⊥ : SimpleGraph V) c v _).mp rfl)
  have himpl : ∀ G : SimpleGraph V, Good π p N G →
      Faithful N p 1 ((1-θ)/4) τ a
        (CoarseKernel.actualCoarse p G c 0) := by
    intro G hg
    apply initial_faithful ha' hNb hT.le hτ0 hτhi G c hcard hplus
    · simpa only [hπ G] using hg.1
    · simpa only [hπ G] using hg.2
    · exact hnumN.1
    · exact hnumN.2
  have hbad : (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
      {G | ¬Faithful N p 1 ((1-θ)/4) τ a
        (CoarseKernel.actualCoarse p G c 0)} ≤ ε := by
    calc
      _ ≤ (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
          {G | ¬Good π p N G} := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        exact measure_mono (fun G hG hgood => hG (himpl G hgood))
      _ ≤ (N : ℝ)^(-(1:ℝ)) := hprob p hp V hcard π
      _ ≤ ε := hinvN
  refine ⟨hbad,?_⟩
  have hc := probReal_compl_eq_one_sub
    (μ := SimpleGraph.binomialRandom V (Binomial.closedProbability p))
    ((Set.toFinite {G | Faithful N p 1 ((1-θ)/4) τ a
      (CoarseKernel.actualCoarse p G c 0)}).measurableSet)
  change (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
    {G | ¬Faithful N p 1 ((1-θ)/4) τ a
      (CoarseKernel.actualCoarse p G c 0)} = _ at hc
  linarith

end MajorityDynamics.GraphProcess.DayOne

