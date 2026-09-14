import MajorityDynamics.GraphProcess.FaithfulStep.Main

noncomputable section
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution

theorem density_widen {θ T U p : ℝ} {N : ℕ} (hT : 0 < T) (hTU : T ≤ U)
    (hlo : T⁻¹*(N:ℝ)^(-θ) < p) (hhi : p < T*(N:ℝ)^(-θ)) :
    U⁻¹*(N:ℝ)^(-θ) < p ∧ p < U*(N:ℝ)^(-θ) := by
  constructor
  · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hT hTU) (Real.rpow_nonneg (by positivity) _)).trans_lt hlo
  · exact hhi.trans_le (mul_le_mul_of_nonneg_right hTU (Real.rpow_nonneg (by positivity) _))

theorem faithful_mono {V : Type*} [Fintype V] {N n : ℕ} {p T U δ δ' τ : ℝ}
    {a : Process.Data} {y : Local.CoarseData V n} (hN : 1 ≤ N) (hp : 0 ≤ p)
    (hT : 0 ≤ T) (hTU : T ≤ U) (hδ : δ' ≤ δ)
    (h : Faithful N p T δ τ a y) : Faithful N p U δ' τ a y := by
  have hpow : (N:ℝ)^(-δ) ≤ (N:ℝ)^(-δ') :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  have hm : T*(N:ℝ)^(-δ) ≤ U*(N:ℝ)^(-δ') :=
    mul_le_mul hTU hpow (Real.rpow_nonneg (by positivity) _) (hT.trans hTU)
  refine ⟨h.1,?_,?_⟩
  · intro s
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ sizeScale N p n by unfold sizeScale; positivity)
    exact (h.2.sizes s).trans (by nlinarith only [hh])
  · intro s t
    have hh := mul_le_mul_of_nonneg_right hm
      (show 0 ≤ betaScale N p n*(N:ℝ)^2*p by unfold betaScale; positivity)
    exact (h.2.edges s t).trans (by nlinarith only [hh])

/-- Selected references at different parameter bounds are identical on their
whole certified horizon; no approximate comparison is involved. -/
theorem references_agree {θ T U : ℝ} {N : ℕ} {p : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hU : 1 < U)
    (hNT : processThreshold θ T ≤ N) (hNU : processThreshold θ U ≤ N)
    (hTlo : T⁻¹*(N:ℝ)^(-θ) < p) (hThi : p < T*(N:ℝ)^(-θ))
    (hUlo : U⁻¹*(N:ℝ)^(-θ) < p) (hUhi : p < U*(N:ℝ)^(-θ)) :
    Process.AgreeThrough (responseHorizon θ)
      (referenceDataReal θ T N p) (referenceDataReal θ U N p) := by
  obtain ⟨hp,ha,huniq⟩ := referenceData_agree hθlo hθhi hT hNT hTlo hThi
  obtain ⟨hp',hb,_⟩ := referenceData_agree hθlo hθhi hU hNU hUlo hUhi
  rw [referenceDataReal_eq hp, referenceDataReal_eq hp']
  exact huniq _ hb.toRecursion

end MajorityDynamics.GraphProcess.FaithfulTrajectory
