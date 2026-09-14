import MajorityDynamics.GraphProcess.FaithfulTrajectory.Parameters
import MajorityDynamics.GraphProcess.FaithfulTrajectory.OneStep

noncomputable section
open MeasureTheory
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution

/-- Closed uniform subcritical transition on the original faithful sets.
Output references are transported exactly and the exponent decreases. -/
theorem uniform_faithful_step {θ T δ : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (n : ℕ) (hk : (n:ℝ)+1 < 1/(1-θ)) (hT : 1 < T) (hδ : 0 < δ) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : unitInterval,
      T⁻¹*(N:ℝ)^(-θ) < (p:ℝ) → (p:ℝ) < T*(N:ℝ)^(-θ) →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ (V : Type*) [Fintype V], Fintype.card V = N →
    ∀ y : Local.CoarseData V n,
      Faithful N p T δ τ (referenceDataReal θ T N p) y →
      CoarseKernel.Kbar p y {z | ¬ Faithful N p U δ' τ (referenceDataReal θ U N p) z}
        ≤ ENNReal.ofReal ε := by
  obtain ⟨T₁,hT₁,δ₁,hδ₁,φ₁,hφ₁,hφ₁hi,hinc⟩ :=
    FaithfulStep.faithful_inclusion θ hθlo hθhi n hk T δ hT hδ
  have hT₁hi : 1 < T₁ := hT.trans_le hT₁
  have hT₁0 : 0 < T₁ := by linarith
  let U := 2*T₁
  let d := min δ (min δ₁ ((1-θ)/8))
  have hTU : T ≤ U := by dsimp [U]; linarith
  have hU : 1 < U := hT.trans_le hTU
  have hd : 0 < d := lt_min hδ (lt_min hδ₁ (by linarith))
  refine ⟨U,hTU,d,hd,min_le_left _ _,?_⟩
  obtain ⟨C,hC,hloc⟩ := LocalTheorem.local_coarse_transition n hθlo hθhi hT₁hi hφ₁ hφ₁hi
  obtain ⟨N₁,hN₁,hi⟩ := hinc C hC.le
  intro ε hε
  obtain ⟨N₂,hl⟩ := hloc ε hε
  refine ⟨max N₁ (max N₂ (max (processThreshold θ T) (processThreshold θ U))),
    hN₁.trans (le_max_left _ _),?_⟩
  intro N hN p hlo hhi τ hτlo hτhi V inst hcard y hf
  obtain ⟨hp,ha,hyi⟩ := hi N (by omega) p hlo hhi
  have hev := hyi τ hτlo hτhi V hcard y hf
  obtain ⟨q,hq,_⟩ := hev.1.tilt.exists_unique
  have hwide := density_widen (show 0 < T by linarith) hT₁ hlo hhi
  obtain ⟨hnorm,hfail,_⟩ := hl N (by omega) V hcard p hwide.1 hwide.2 y q
    (hev.1.admissible q hq)
  let := hnorm
  have hwideU := density_widen (show 0 < T by linarith) hTU hlo hhi
  have href := references_agree hθlo hθhi hT hU (by omega) (by omega)
    hlo hhi hwideU.1 hwideU.2
  apply local_success_failure p y q C ε
    {z | Faithful N p U d τ (referenceDataReal θ U N p) z} hfail
  intro z hz
  have hfz := hev.2 q hq z hz
  have hfm := faithful_mono (by omega) hp.1.le (by positivity)
    (show 2*T₁ ≤ U by rfl) (min_le_right δ _) hfz
  exact (FaithfulStep.faithful_reference_iff
    (href.1 (n+1) (level_succ_lt_horizon hk)) z).mp hfm

end MajorityDynamics.GraphProcess.FaithfulTrajectory
