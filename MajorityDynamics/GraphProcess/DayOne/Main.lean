import MajorityDynamics.GraphProcess.DayOne.Initial
import MajorityDynamics.GraphProcess.DayOne.Concentration

noncomputable section
open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.GraphProcess.DayOne
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedEvolution

/-- The original graph law, exact floor-rounded initial bias and constant-one
faithfulness, uniformly over densities, colorings and finite vertex carriers. -/
def DayOneTheorem : Prop :=
  ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∀ T : ℝ, 1 < T →
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
  ∃ hp : 0 < p ∧ p < 1,
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ (V : Type*) [Fintype V], Fintype.card V = N →
    ∀ c : V → Bool,
      (Finset.univ.filter fun v => c v = false).card = N/2 + ⌊τ*Real.sqrt N⌋₊ →
    (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real
      {G | ¬Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
        (CoarseKernel.actualCoarse p G c 0)} ≤ ε ∧
    1-ε ≤ (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real
      {G | Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
        (CoarseKernel.actualCoarse p G c 0)}

theorem day_one : DayOneTheorem := by
  intro θ hθlo hθhi T hT ε hε
  have hT0 : 0 < T := by linarith
  have hnum := eventually_faithful_errors hθlo hθhi hT
    (show 0 ≤ 20*(T+1)^2 by positivity)
  have hinv : ∀ᶠ N : ℕ in atTop, (N : ℝ)^(-(1:ℝ)) ≤ ε := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ)^(-(1:ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_le_nhds hε)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    ((eventually_ge_atTop (max 1 (processThreshold θ T))).and
      (hnum.and ((uniform_concentration hθlo hθhi hT).and hinv)))
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro N hN p hlo hhi
  obtain ⟨hNb,hnumeric,hprob,hinvN⟩ := hN₀ N ((le_max_right _ _).trans hN)
  obtain ⟨hp,ha,_⟩ := referenceData_agree hθlo hθhi hT
    ((le_max_right _ _).trans hNb) hlo hhi
  have ha' : (referenceDataReal θ T N p).state 0 = Process.initialState N ⟨p,hp⟩ := by
    rw [referenceDataReal_eq hp]
    exact ha.initial
  refine ⟨hp,?_⟩
  intro τ hτlo hτhi V inst hcard c hplus
  have hτ0 : 0 ≤ τ := (inv_nonneg.mpr hT0.le).trans hτlo
  have hnumN := hnumeric ⟨p,hp⟩ ⟨hlo,hhi⟩
  let π := History.actualHistory (⊥ : SimpleGraph V) c 1
  have hπ : ∀ G : SimpleGraph V, History.actualHistory G c 1 = π := by
    intro G
    funext v
    exact (initial_history_iff G c v _).mpr
      ((initial_history_iff (⊥ : SimpleGraph V) c v _).mp rfl)
  have himpl : ∀ G : SimpleGraph V, Good π p N G →
      Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
        (CoarseKernel.actualCoarse p G c 0) := by
    intro G hg
    apply initial_faithful ha' ((le_max_left _ _).trans hNb) hT.le hτ0 hτhi G c hcard hplus
    · simpa only [hπ G] using hg.1
    · simpa only [hπ G] using hg.2
    · exact hnumN.1
    · exact hnumN.2
  have hbad : (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real
      {G | ¬Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
        (CoarseKernel.actualCoarse p G c 0)} ≤ ε := by
    calc
      _ ≤ (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real
          {G | ¬Good π p N G} := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        exact measure_mono (fun G hG hgood => hG (himpl G hgood))
      _ ≤ (N : ℝ)^(-(1:ℝ)) := hprob ⟨p,hp⟩ ⟨hlo,hhi⟩ V hcard π
      _ ≤ ε := hinvN
  refine ⟨hbad,?_⟩
  have hc := probReal_compl_eq_one_sub
    (μ := SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩)
    ((Set.toFinite {G | Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
      (CoarseKernel.actualCoarse p G c 0)}).measurableSet)
  change (SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).real
    {G | ¬Faithful N p 1 ((1-θ)/4) τ (referenceDataReal θ T N p)
      (CoarseKernel.actualCoarse p G c 0)} = _ at hc
  linarith

end MajorityDynamics.GraphProcess.DayOne
