import MajorityDynamics.GraphProcess.FaithfulTrajectory.SparsePrefix
import MajorityDynamics.Idealized.CriticalDay.PreStoppingResponse

noncomputable section
open MeasureTheory Set Filter Topology
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution
open CoarseKernel
open Binomial.Approximation (SparseRange scale)

/-- Actual faithfulness at a density-dependent stopping level, with the
faithfulness rate fixed before the stopping exponent. The same level works
for every reference process and initial coloring at the given N and p. -/
theorem uniform_stopped_faithfulness {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (ell D H : ℕ) (hell : 1 ≤ ell) (hHD : H < D)
    (hH : 1 < (H:ℝ)*(1-θ)) :
    ∃ U δ r : ℝ, T ≤ U ∧ 0 < δ ∧ 0 < r ∧ r ≤ 1/4 ∧ r/4 < δ ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p →
      1 ≤ scale N p ∧ ∃ j : ℕ, 0 < j ∧ j ≤ H-2 ∧
        scale N p^r ≤ (betaScale N p j*scale N p)*scale N p ∧
        betaScale N p j*scale N p < scale N p^r ∧
        (∀ i < j, ResponseSmall θ N p i) ∧
        ∀ a : Process.Data, Process.Specification N p D ell a →
        ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T → ∀ c : Fin N → Bool,
        (Finset.univ.filter fun v => c v = false).card = N/2+⌊τ*Real.sqrt N⌋₊ →
        SimpleGraph.binomialRandom (Fin N) (Binomial.closedProbability p)
          {G | ¬Faithful N p U δ τ a (actualCoarse p G c j)} ≤ ENNReal.ofReal ε := by
  obtain ⟨U,hTU,δ,hδ,hprefix⟩ := uniform_sparse_prefix hθlo hθhi hT ell D hell H hHD
  obtain ⟨r,hr,hr4,hgap,htiming⟩ :=
    CriticalDay.choose_flexible_stopping_exponent_before H hθlo hθhi hδ hH
  have hH2 : 2 ≤ H := by
    by_contra hh
    have hHle : H ≤ 1 := by omega
    have hcast : (H : ℝ) ≤ 1 := by exact_mod_cast hHle
    have hα : 0 ≤ 1-θ := by linarith
    have hα1 : 1-θ < 1 := by linarith
    have hprod : (H:ℝ)*(1-θ) < 1 :=
      (mul_le_mul_of_nonneg_right hcast hα).trans_lt (by simpa using hα1)
    linarith
  have hsharp : 1 < (1-θ)*((((H-2 : ℕ) : ℝ))+2-r) := by
    have heq : (((H-2 : ℕ) : ℝ))+2-r = (H:ℝ)-r := by
      rw [Nat.cast_sub hH2]
      norm_num
    rw [heq]
    exact htiming
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp
    (CriticalDay.uniform_flexible_stopping_index_at θ T r (H-2) hr (by linarith)
      hθhi hT hsharp)
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp
    (CriticalDay.pre_stopping_response_small θ T hθhi (by linarith))
  refine ⟨U,δ,r,hTU,hδ,hr,hr4,hgap,?_⟩
  intro ε hε
  obtain ⟨N₃,h₃⟩ := hprefix ε hε
  refine ⟨max 1 (max N₁ (max N₂ N₃)),le_max_left _ _,?_⟩
  intro N hN p hp
  obtain ⟨hs,_,j,hj0,hjH,hlo,hhi,hprev⟩ := (h₁ N (by omega)).2 p hp
  have hcut : ∀ i < j, ResponseSmall θ N p i :=
    fun i hi => h₂ N (by omega) p hp r hr4 i (hprev i hi)
  refine ⟨hs,j,hj0,hjH,hlo,hhi,hcut,?_⟩
  intro a ha τ hτ hτT c hc
  apply le_trans (measure_mono ?_) (h₃ N (by omega) p hp a ha τ hτ hτT c hc)
  intro G hbad
  exact ⟨j,by omega,hcut,hbad⟩

end MajorityDynamics.GraphProcess.FaithfulTrajectory
