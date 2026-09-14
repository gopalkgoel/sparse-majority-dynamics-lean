import MajorityDynamics.GraphProcess.DayOne.Main
import MajorityDynamics.GraphProcess.FaithfulTrajectory.Prefix

noncomputable section
open MeasureTheory
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution

theorem day_one_seed {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    UniformFaithful θ T T ((1-θ)/4) 0 := by
  intro ε hε
  obtain ⟨N₀,hN₀,h₀⟩ := DayOne.day_one θ hθlo hθhi T hT ε hε
  refine ⟨N₀,?_⟩
  intro N hN p τ c hd hlo hhi hc
  obtain ⟨hp,hp'⟩ := h₀ N hN p hd.1 hd.2
  have h := (hp' τ hlo hhi (Fin N) (Fintype.card_fin N) c hc).1
  have heq : (⟨(p:ℝ),hp.1.le,hp.2.le⟩ : unitInterval) = p := Subtype.ext rfl
  rw [heq] at h
  change (Paper.graphLaw N p).real {G | ¬Faithful N p 1 ((1-θ)/4) τ
    (referenceDataReal θ T N p) (CoarseKernel.rho p (FineState.actualState G c 0))} ≤ ε at h
  rw [← ofReal_measureReal (μ := Paper.graphLaw N p)]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans (measureReal_mono ?_) h
  intro G hbad hgood
  exact hbad (faithful_mono (hN₀.trans hN) hp.1.le zero_le_one hT.le le_rfl hgood)

/-- All subcritical days are jointly faithful, with no remaining internal
premise: day one, 5.4, 5.6, and the actual local kernel are all supplied. -/
theorem faithful_prefix {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (n : ℕ) (hn : (n:ℝ) < 1/(1-θ)) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ UniformFaithfulPrefix θ T U δ n :=
  finite_prefix_of_seed hθlo hθhi hT (by linarith) (day_one_seed hθlo hθhi hT) n hn

end MajorityDynamics.GraphProcess.FaithfulTrajectory
