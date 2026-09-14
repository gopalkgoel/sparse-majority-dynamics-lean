import MajorityDynamics.Idealized.PerturbedEvolution.AdmissibilityAssembly
import MajorityDynamics.Idealized.PerturbedEvolution.Template
import MajorityDynamics.Idealized.PerturbedEvolution.Monotonicity

/-! Theorem 5.4 and Appendix E.5: all clauses with one set of constants. -/
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt

theorem perturbed_evolution : PerturbedEvolutionTheorem := by
  intro θ hθlo hθhi n hk T δ hT hδ
  have hT0 : 0 < T := by linarith
  have hell := (processSelection_spec hθlo hθhi hT).1
  obtain ⟨Kt, hKt, R, hR, C, hC, B, hB, Nt, hNt, hresponse⟩ :=
    perturbed_tilt_response θ hθlo hθhi n hk T δ hT hδ
  obtain ⟨Ka, hKaT, hKaC, hKa, hadmissible⟩ :=
    admissibility_spec θ T δ hθlo hθhi hT hδ n (processExponent θ T) hk C hC.le
  obtain ⟨Km, hKm, Nm, hNm, htemplate⟩ :=
    template_spec θ T δ hθlo hθhi hT hδ n (processExponent θ T) hell hk
  let K := max Kt (max Ka Km)
  have hKtK : Kt ≤ K := le_max_left _ _
  have hKaK : Ka ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKmK : Km ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hK : T ≤ K := hKt.trans hKtK
  have hφ := (universal_nondegeneracy n).probability_pos
  have hφhi := (universal_nondegeneracy n).probability_le_quarter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    ((eventually_ge_atTop Nt).and ((eventually_ge_atTop Nm).and hadmissible))
  refine ⟨K, hK, tiltRate θ δ n,
    (tiltRate_bounds (responseRate_pos hθlo hθhi hk) hδ).1,
    φStar n / 4, by positivity, by linarith,
    max 1 N₀, le_max_left _ _, ?_⟩
  intro N hN p hp₀ hp₁
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hNNt, hNNm, hadm⟩ := hN₀ N ((le_max_right _ _).trans hN)
  obtain ⟨hp, ha, hresp⟩ := hresponse N hNNt p hp₀ hp₁
  refine ⟨hp, ha, ?_⟩
  intro τ hτ hτT V inst hcard y hf
  obtain ⟨htilt, hrows, hsolve⟩ := hresp τ hτ hτT y.integerSizes y.edge hf.2
  refine ⟨tiltConclusion_mono hN1 (hT0.le.trans hKt) hKtK le_rfl htilt, ?_, ?_⟩
  · intro q hq
    have hq' : Local.Solves (naturalSizes y.integerSizes) (realEdges y.edge) q := by
      simpa only [naturalSizes_coarse, realEdges_coarse] using hq
    obtain ⟨σ, hσq, hσR, _⟩ := hsolve q hq'
    obtain ⟨hbound, hmass, hsplit⟩ := response_local_bounds hrows σ hσq hσR
    simp only [naturalSizes_coarse] at hbound hmass hsplit
    have had := hadm ⟨p, hp⟩ ⟨hp₀, hp₁⟩ _ ha τ hτ hτT V y hcard hf.1 hf.2
      q hq hbound (φStar n / 4) hmass hsplit
    exact had.mono hKa hKaK le_rfl hp.1.le
  · intro q hq
    have hq' : Local.Solves (naturalSizes y.integerSizes) (realEdges y.edge) q := by
      simpa only [naturalSizes_coarse, realEdges_coarse] using hq
    have hm := htemplate N hNNm ⟨p, hp⟩ ⟨hp₀, hp₁⟩ _ ha τ hτ hτT
      y.integerSizes y.edge hf.2 q hq'
    simp only [naturalSizes_coarse, realEdges_coarse] at hm
    exact templateConclusion_mono hN1 hp.1.le hKm.le hKmK le_rfl hm

/-- The endpoint already quantifies over arbitrary finite vertex types and
uses their actual partition fibers, so no graph realization or relabeling
hypothesis is required. -/
theorem perturbed_evolution_finite : PerturbedEvolutionTheorem := perturbed_evolution

end MajorityDynamics.Idealized.PerturbedEvolution
