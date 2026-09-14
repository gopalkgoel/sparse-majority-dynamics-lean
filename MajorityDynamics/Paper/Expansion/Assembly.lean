import MajorityDynamics.GraphProcess.FaithfulTrajectory.FaithfulLead
import MajorityDynamics.GraphProcess.FaithfulTrajectory.CriticalStep
import MajorityDynamics.Paper.Expansion.Rates

noncomputable section
open Filter Topology MeasureTheory
namespace MajorityDynamics.Paper.Expansion
open GraphProcess GraphProcess.FaithfulTrajectory Idealized Idealized.LinearResponse

/-- A faithful noncritical endpoint yields the original expansion event,
uniformly in all densities and initial colorings. -/
theorem noncritical_expansion {θ T U δ : ℝ} {n : ℕ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hTU : T ≤ U) (hδ : 0 < δ)
    (hday : n+1 = expansionDay θ)
    (hfaith : UniformFaithful θ T U δ n) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
      densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
      graphLaw N p (expansionEvent θ p c)ᶜ ≤ ENNReal.ofReal ε := by
  have hT0 : 0 < T := by linarith
  have hU := hT.trans_le hTU
  have hS := responseLead_pos n
  have hc : 0 < responseLead n/(2*T) := by positivity
  have hn : 1 < (1-θ)*((n:ℝ)+1) := by
    have h := expansionDay_exponent hθhi
    rw [← hday] at h
    push_cast at h
    nlinarith only [h]
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp (eventually_noncritical_lead hT0 hc hn)
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp
    (eventually_error_coefficient ((Fintype.card (Universal.History (n+1)):ℝ)*U) hδ hc)
  intro ε hε
  obtain ⟨N₃,h₃⟩ := hfaith ε hε
  refine ⟨max N₁ (max N₂ (max N₃ (processThreshold θ U))),?_⟩
  intro N hN p τ c hd hlo hhi hb
  have hdU := density_widen hT0 hTU hd.1 hd.2
  obtain ⟨hp,ha,_⟩ := referenceData_agree hθlo hθhi hU (by omega) hdU.1 hdU.2
  have hs : Process.StateSymmetric ((referenceDataReal θ U N p).state n) := by
    rw [referenceDataReal_eq hp]
    apply ha.symmetry
    change n < expansionDay θ
    omega
  apply le_trans (measure_mono ?_) (h₃ N (by omega) p τ c hd hlo hhi hb)
  intro G hfail hf
  have hl := faithful_actual_lead_half hT0 hlo (h₂ N (by omega)) G c hs hf
  have hdom := h₁ N (by omega) ⟨(p:ℝ),hp⟩ hd
  apply hfail
  change (N:ℝ)/Real.sqrt ((p:ℝ)*N)*Real.log N ≤ lead (coloringOnDay G c (expansionDay θ))
  rw [← hday]
  exact hdom.trans hl

/-- Macroscopic gains at the final critical day dominate the expansion target. -/
theorem critical_expansion {θ T ζ : ℝ} {n : ℕ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hζ : 0 < ζ) (hday : n+1 = expansionDay θ)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
        densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
        graphLaw N p {G | ¬CriticalGain N ζ (CoarseKernel.rho p (FineState.actualState G c n))}
          ≤ ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
      densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
      graphLaw N p (expansionEvent θ p c)ᶜ ≤ ENNReal.ofReal ε := by
  have hT0 : 0 < T := by linarith
  let c₀ := (Fintype.card (Universal.History (n+1)):ℝ)*ζ
  have hc : 0 < c₀ := by dsimp [c₀]; positivity
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp (eventually_critical_lead hθhi hT0 hc)
  intro ε hε
  obtain ⟨N₃,h₃⟩ := hg ε hε
  refine ⟨max N₁ (max (processThreshold θ T) N₃),?_⟩
  intro N hN p τ c hd hlo hhi hb
  obtain ⟨hpN,_,_⟩ := referenceData_agree hθlo hθhi hT (by omega) hd.1 hd.2
  apply le_trans (measure_mono ?_) (h₃ N (by omega) p τ c hd hlo hhi hb)
  intro G hfail hgain
  have hl := critical_gain_lead G c p ζ hgain
  have hdom := h₁ N (by omega) ⟨(p:ℝ),hpN⟩ hd
  apply hfail
  change (N:ℝ)/Real.sqrt ((p:ℝ)*N)*Real.log N ≤ lead (coloringOnDay G c (expansionDay θ))
  rw [← hday]
  exact hdom.trans hl

end MajorityDynamics.Paper.Expansion
