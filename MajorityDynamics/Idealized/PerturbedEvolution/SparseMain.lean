import MajorityDynamics.Idealized.PerturbedEvolution.SparseAdmissibilityAssembly
import MajorityDynamics.Idealized.PerturbedEvolution.SparseTemplate
import MajorityDynamics.Idealized.PerturbedEvolution.Monotonicity

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (SparseRange)

/-- The complete perturbed-evolution conclusion at any fixed reference
horizon, throughout the wider density range and before the response cutoff.
All constants precede the reference realization and faithful coarse data. -/
theorem perturbed_evolution_spec_sparse (θ T δ : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ)
    (n ell D : ℕ) (hell : 1 ≤ ell) (hDlt : n+1 < D) :
    ∃ K : ℝ, T ≤ K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V], Fintype.card V = N →
      ∀ y : Local.CoarseData V n, Faithful N p T δ τ a y →
        EvolutionConclusion N p a y τ K (sparseTiltRate θ δ) (φStar n/4) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨Kt,hKt,R,hR,C,hC,B,hB,Nt,hNt,hresponse⟩ :=
    perturbed_tilt_response_spec_sparse θ T δ hθlo hθhi hT hδ n ell hell D hDlt
  obtain ⟨Ka,hKaT,hKaC,hKa,hadmissible⟩ :=
    admissibility_spec_sparse θ T δ hθlo hθhi hT hδ n ell D hDlt C hC.le
  obtain ⟨Km,hKm,Nm,hNm,htemplate⟩ :=
    template_spec_sparse θ T δ hθlo hθhi hT hδ n ell hell D hDlt
  let K := max Kt (max Ka Km)
  have hKtK : Kt ≤ K := le_max_left _ _
  have hKaK : Ka ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKmK : Km ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    ((eventually_ge_atTop Nt).and ((eventually_ge_atTop Nm).and hadmissible))
  refine ⟨K,hKt.trans hKtK,max 1 N₀,le_max_left _ _,?_⟩
  intro N hN p hp hsub a ha τ hτ hτT V inst hcard y hf
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hNNt,hNNm,hadm⟩ := hN₀ N ((le_max_right _ _).trans hN)
  obtain ⟨htilt,hrows,hsolve⟩ :=
    hresponse N hNNt p hp hsub a ha τ hτ hτT y.integerSizes y.edge hf.2
  refine ⟨tiltConclusion_mono hN1 (hT0.le.trans hKt) hKtK le_rfl htilt,?_,?_⟩
  · intro q hq
    have hq' : Local.Solves (naturalSizes y.integerSizes) (realEdges y.edge) q := by
      simpa only [naturalSizes_coarse,realEdges_coarse] using hq
    obtain ⟨σ,hσq,hσR,_⟩ := hsolve q hq'
    obtain ⟨hbound,hmass,hsplit⟩ := response_local_bounds hrows σ hσq hσR
    simp only [naturalSizes_coarse] at hbound hmass hsplit
    have had := hadm p hp hsub a ha τ hτ hτT V y hcard hf.1 hf.2
      q hq hbound (φStar n/4) hmass hsplit
    exact had.mono hKa hKaK le_rfl p.property.1.le
  · intro q hq
    have hq' : Local.Solves (naturalSizes y.integerSizes) (realEdges y.edge) q := by
      simpa only [naturalSizes_coarse,realEdges_coarse] using hq
    have hm := htemplate N hNNm p hp hsub a ha τ hτ hτT
      y.integerSizes y.edge hf.2 q hq'
    simp only [naturalSizes_coarse,realEdges_coarse] at hm
    exact templateConclusion_mono hN1 p.property.1.le hKm.le hKmK le_rfl hm

end MajorityDynamics.Idealized.PerturbedEvolution
