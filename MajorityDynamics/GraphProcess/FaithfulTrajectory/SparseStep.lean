import MajorityDynamics.GraphProcess.FaithfulTrajectory.OneStep
import MajorityDynamics.GraphProcess.FaithfulStep.Basic
import MajorityDynamics.GraphProcess.FaithfulStep.SparseRates
import MajorityDynamics.GraphProcess.LocalTheorem.SparseMain
import MajorityDynamics.Idealized.PerturbedEvolution.SparseMain

noncomputable section
open Filter Topology MeasureTheory
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedTilt Idealized.PerturbedEvolution
open Binomial.Approximation (SparseRange)

/-- The actual coarse transition propagates faithfulness before the response
cutoff, using one fixed reference process. Neither a statistical transition
estimate nor an analytic evolution estimate is assumed. -/
theorem uniform_faithful_step_sparse {θ T δ : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ)
    (n ell D : ℕ) (hell : 1 ≤ ell) (hDlt : n+1 < D) :
    ∃ U : ℝ, T ≤ U ∧ ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ResponseSmall θ N p n → ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V], Fintype.card V = N →
      ∀ y : Local.CoarseData V n, Faithful N p T δ τ a y →
      CoarseKernel.Kbar (Binomial.closedProbability p) y
        {z | ¬Faithful N p U d τ a z} ≤ ENNReal.ofReal ε := by
  obtain ⟨K,hKT,Ne,hNe,hevol⟩ :=
    perturbed_evolution_spec_sparse θ T δ hθlo hθhi hT hδ n ell D hell hDlt
  have hK : 1 < K := hT.trans_le hKT
  have hK0 : 0 < K := by linarith
  have hT0 : 0 < T := by linarith
  have hρ := (sparseTiltRate_bounds (sparseResponseRate_pos hθhi) hδ).1
  let d := min δ (min (sparseTiltRate θ δ) ((1-θ)/8))
  have hd : 0 < d := lt_min hδ (lt_min hρ (by linarith))
  have hdρ : d ≤ sparseTiltRate θ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hdgap : d ≤ (1-θ)/8 := (min_le_right _ _).trans (min_le_right _ _)
  have hφ := (Universal.universal_nondegeneracy n).probability_pos
  have hφhi := (Universal.universal_nondegeneracy n).probability_le_quarter
  obtain ⟨C,hC,hloc⟩ := LocalTheorem.local_coarse_transition_sparse n hθlo hθhi hK
    (show 0 < Universal.φStar n/4 by positivity) (show Universal.φStar n/4 < 1/2 by linarith)
  obtain ⟨Nr,hr⟩ := Filter.eventually_atTop.mp
    (FaithfulStep.eventually_local_errors_sparse hθlo hθhi hT hK0 hC.le hdgap)
  refine ⟨2*K,by linarith,d,hd,min_le_left _ _,?_⟩
  intro ε hε
  obtain ⟨Nl,hl⟩ := hloc ε hε
  refine ⟨max Ne (max Nr Nl),hNe.trans (le_max_left _ _),?_⟩
  intro N hN p hp hsub a ha τ hτ hτT V inst hcard y hf
  have hev := hevol N (by omega) p hp hsub a ha τ hτ hτT V hcard y hf
  obtain ⟨q,hq,_⟩ := hev.tilt.exists_unique
  have hwide := Idealized.RowLimits.sparseRange_enlarge hT0 hKT hp
  obtain ⟨hnorm,hfail,_⟩ := hl N (by omega) V hcard (Binomial.closedProbability p)
    hwide.1 hwide.2 y q (hev.admissible q hq)
  let := hnorm
  apply local_success_failure (Binomial.closedProbability p) y q C ε
    {z | Faithful N p (2*K) d τ a z} hfail
  intro z hz
  have hsc := hr N (by omega) p hp n
  exact FaithfulStep.local_success_faithful (hNe.trans (by omega)) hcard p.property.1.le
    hK0.le hdρ hsc.1 hsc.2 (hev.template q hq) hz

end MajorityDynamics.GraphProcess.FaithfulTrajectory
