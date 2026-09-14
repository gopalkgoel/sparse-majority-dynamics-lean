import MajorityDynamics.GraphProcess.FaithfulTrajectory.Induction
import MajorityDynamics.GraphProcess.FaithfulTrajectory.CriticalGain
import MajorityDynamics.Idealized.CriticalDay.Basic
import MajorityDynamics.Paper.Expansion.Rates

noncomputable section
open Filter Topology MeasureTheory
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution FineState CoarseKernel

/-- Critical local-to-actual step. The sole intermediate premise is the exact
5.5 contract, which the final endpoint supplies from its proof. -/
theorem critical_from_uniform (hcritical : CriticalDay.CriticalDayTheorem.{0})
    {θ T U δ : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hTU : T ≤ U) (hδ : 0 < δ) (n : ℕ) (hk : (n:ℝ)+1 = 1/(1-θ))
    (hprev : UniformFaithful θ T U δ n) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Paper.Coloring N),
      Paper.densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → Paper.initialBias N τ c →
      Paper.graphLaw N p {G | ¬ CriticalGain N ζ (rho p (actualState G c (n+1)))} ≤
        ENNReal.ofReal ε := by
  have hU : 1 < U := hT.trans_le hTU
  have hT0 : 0 < T := by linarith
  obtain ⟨ζ,hζ,hcrit⟩ := hcritical θ hθlo hθhi n hk U hU
  obtain ⟨T₁,hT₁,δ₁,_,φ₁,hφ₁,hφ₁hi,N₁,_,h₁⟩ := hcrit δ hδ
  obtain ⟨C,hC,hloc⟩ := LocalTheorem.local_coarse_transition n hθlo hθhi
    (hU.trans_le hT₁) hφ₁ hφ₁hi
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp (Paper.Expansion.eventually_critical_error hC.le hζ)
  refine ⟨ζ/2,by positivity,?_⟩
  intro ε hε
  have he : 0 < ε/2 := by positivity
  obtain ⟨N₃,h₃⟩ := hprev (ε/2) he
  obtain ⟨N₄,h₄⟩ := hloc (ε/2) he
  refine ⟨max N₁ (max N₂ (max N₃ N₄)),?_⟩
  intro N hN p τ c hd hlo hhi hc
  have hdU := density_widen hT0 hTU hd.1 hd.2
  have hdT₁ := density_widen hT0 (hTU.trans hT₁) hd.1 hd.2
  obtain ⟨hp,_,hcrit'⟩ := h₁ N (by omega) p hdU.1 hdU.2
  have hloU := (inv_anti₀ hT0 hTU).trans hlo
  have hhiU := hhi.trans hTU
  have hstep (y : Local.CoarseData (Fin N) n)
      (hy : Faithful N p U δ τ (referenceDataReal θ U N p) y) (_ : pAttainable p y) :
      Kbar p y {z | ¬CriticalGain N (ζ/2) z} ≤ ENNReal.ofReal (ε/2) := by
    have hev := hcrit' τ hloU hhiU (Fin N) (Fintype.card_fin N) y hy
    obtain ⟨q,hq,_⟩ := hev.exists_unique
    obtain ⟨hnorm,hfail,_⟩ := h₄ N (by omega) (Fin N) (Fintype.card_fin N)
      p hdT₁.1 hdT₁.2 y q (hev.admissible q hq)
    let := hnorm
    apply local_success_failure p y q C (ε/2) {z | CriticalGain N (ζ/2) z} hfail
    exact fun z hz => critical_gain_of_local_success (Fintype.card_fin N) y q
      (hev.gain q hq) (h₂ N (by omega)) z hz
  have hb := actual_one_step n p c hp.1 hp.2
    {y | Faithful N p U δ τ (referenceDataReal θ U N p) y}
    {z | CriticalGain N (ζ/2) z} (ENNReal.ofReal (ε/2)) hstep
  have hpast := h₃ N (by omega) p τ c hd hlo hhi hc
  change Paper.graphLaw N p _ ≤ Paper.graphLaw N p _ + ENNReal.ofReal (ε/2) at hb
  refine hb.trans ?_
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hpast le_rfl
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add he.le he.le]; congr 1; ring

end MajorityDynamics.GraphProcess.FaithfulTrajectory
