import MajorityDynamics.GraphProcess.FaithfulTrajectory.UniformStep

noncomputable section
open MeasureTheory
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution
open FineState CoarseKernel

/-- Uniform high probability at one fixed day; all varying densities, biases
and deterministic initial colorings come after the common size threshold. -/
def UniformFaithful (θ T U δ : ℝ) (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Paper.Coloring N),
      Paper.densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → Paper.initialBias N τ c →
      Paper.graphLaw N p {G | ¬ Faithful N p U δ τ (referenceDataReal θ U N p)
        (rho p (actualState G c n))} ≤ ENNReal.ofReal ε

/-- One full induction step of 5.8 with closed analytic and local-probability
inputs. Its only premise is the previous day's high-probability statement. -/
theorem extend_uniform_faithful {θ T U δ : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hTU : T ≤ U) (hδ : 0 < δ) (n : ℕ)
    (hk : (n:ℝ)+1 < 1/(1-θ)) (hprev : UniformFaithful θ T U δ n) :
    ∃ U' : ℝ, U ≤ U' ∧ ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      UniformFaithful θ T U' δ' (n+1) := by
  have hU : 1 < U := hT.trans_le hTU
  have hT0 : 0 < T := by linarith
  obtain ⟨U',hUU,δ',hδ',hδle,hs⟩ := uniform_faithful_step hθlo hθhi n hk hU hδ
  refine ⟨U',hUU,δ',hδ',hδle,?_⟩
  intro ε hε
  have he : 0 < ε/2 := by positivity
  obtain ⟨N₁,h₁⟩ := hprev (ε/2) he
  obtain ⟨N₂,_,h₂⟩ := hs (ε/2) he
  refine ⟨max N₁ (max N₂ (processThreshold θ U)),?_⟩
  intro N hN p τ c hd hτlo hτhi hc
  have hdU := density_widen hT0 hTU hd.1 hd.2
  have hτUlo : U⁻¹ ≤ τ := (inv_anti₀ hT0 hTU).trans hτlo
  have hτUhi : τ ≤ U := hτhi.trans hTU
  obtain ⟨hp,_,_⟩ := referenceData_agree hθlo hθhi hU (by omega) hdU.1 hdU.2
  have hb := actual_one_step n p c hp.1 hp.2
    {y | Faithful N p U δ τ (referenceDataReal θ U N p) y}
    {z | Faithful N p U' δ' τ (referenceDataReal θ U' N p) z}
    (ENNReal.ofReal (ε/2)) (fun y hy _ =>
      h₂ N (by omega) p hdU.1 hdU.2 τ hτUlo hτUhi (Fin N) (Fintype.card_fin N) y hy)
  have hpast := h₁ N (by omega) p τ c hd hτlo hτhi hc
  change Paper.graphLaw N p _ ≤ Paper.graphLaw N p _ + ENNReal.ofReal (ε/2) at hb
  refine hb.trans ?_
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hpast le_rfl
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add he.le he.le]; congr 1; ring

/-- Finite-horizon closure from day one. This helper exposes only the seed;
the local transitions and reference changes above are already proved. -/
theorem finite_horizon_of_seed {θ T δ₀ : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ₀ : 0 < δ₀) (hseed : UniformFaithful θ T T δ₀ 0)
    (n : ℕ) (hn : (n:ℝ) < 1/(1-θ)) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ UniformFaithful θ T U δ n := by
  induction n with
  | zero => exact ⟨T,le_rfl,δ₀,hδ₀,hseed⟩
  | succ n ih =>
    obtain ⟨U,hTU,δ,hδ,hprev⟩ := ih (by push_cast at hn; linarith)
    obtain ⟨U',hUU,δ',hδ',_,hnext⟩ := extend_uniform_faithful hθlo hθhi hT hTU hδ n
      (by simpa only [Nat.cast_add,Nat.cast_one] using hn) hprev
    exact ⟨U',hTU.trans hUU,δ',hδ',hnext⟩

end MajorityDynamics.GraphProcess.FaithfulTrajectory
