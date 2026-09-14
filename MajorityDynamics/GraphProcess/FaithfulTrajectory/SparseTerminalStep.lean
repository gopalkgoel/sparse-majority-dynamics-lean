import MajorityDynamics.Idealized.CriticalDay.SparseCore
import MajorityDynamics.Idealized.CriticalDay.TerminalLeadBudget
import MajorityDynamics.GraphProcess.LocalTheorem.SparseTerminalSizes
import MajorityDynamics.GraphProcess.FaithfulTrajectory.TerminalCriticalGain
import MajorityDynamics.GraphProcess.FaithfulTrajectory.OneStep

noncomputable section
open Filter Topology MeasureTheory Set
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedEvolution CoarseKernel
open Binomial.Approximation (SparseRange scale)

/-- The cleanup lead expressed directly in the coarse partition sizes. -/
def CoarseLead {V : Type*} [Fintype V] {n : ℕ}
    (N : ℕ) (p : ℝ) (y : Local.CoarseData V n) : Prop :=
  (N:ℝ)/Real.sqrt (p*N)*Real.log N ≤
    ∑ s, character (Fin.last n) s*(y.sizes s:ℝ)

theorem coarseLead_actual {N n : ℕ} (p : ℝ) (G : Paper.Graph N) (c : Paper.Coloring N)
    (h : CoarseLead N p (rho p (FineState.actualState G c n))) :
    (N:ℝ)/Real.sqrt (p*N)*Real.log N ≤ Paper.lead (Paper.coloringOnDay G c (n+1)) := by
  rw [← signed_actual_partition G c]
  exact h

/-- The actual terminal coarse kernel reaches the cleanup lead, uniformly
over every faithful input state in the flexible stopping window. -/
theorem uniform_terminal_step_sparse (θ T δ r : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hr : 0 < r) (hr3 : r ≤ 1/3) (hgap : r/4 < δ) (n ell : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      1 ≤ scale N p →
      scale N p^r ≤ (betaScale N p n*scale N p)*scale N p →
      betaScale N p n*scale N p ≤ scale N p^r →
      ∀ a : Process.Data, Process.LevelEstimates N p ell (a.state n) →
      Process.StateSymmetric (a.state n) → ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V], Fintype.card V = N →
      ∀ y : Local.CoarseData V n, Faithful N p T δ τ a y →
      Kbar (Binomial.closedProbability p) y {z | ¬CoarseLead N p z} ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨U,φ,ζ,hTU,hU,hφ,hζ,hcore⟩ := CriticalDay.terminal_faithful_core_sparse
    θ T δ r hθlo hθhi hT hr hr3 hgap n ell
  obtain ⟨C,hC,hkernel⟩ :=
    LocalTheorem.terminal_size_transition_sparse n hθlo hθhi hU hφ
  obtain ⟨N₀,hkernel⟩ := hkernel ε hε
  filter_upwards [hcore,eventually_ge_atTop N₀,eventually_ge_atTop (1:ℕ),
    CriticalDay.terminal_lead_budget_sparse θ T r ζ C hθhi (by linarith)
      hr (by linarith) hζ hC] with N hc hN hN1 hbudget
  intro p hp hs halo hahi a ha hsym τ hτ hτT V inst hcard y hf
  obtain ⟨q,hq,hgain⟩ := hc p hp halo hahi a ha hsym τ hτ hτT V hcard y hf
  have hpU := RowLimits.sparseRange_enlarge (by linarith : 0 < T) hTU hp
  obtain ⟨hnorm,hfail,_⟩ := hkernel N hN V hcard (Binomial.closedProbability p)
    hpU.1 hpU.2 y q hq
  let := hnorm
  obtain ⟨herror,hlead⟩ := hbudget p hp hs (betaScale N p n*scale N p) halo
  have hinc (z : Local.CoarseData V (n+1))
      (hz : LocalTransition.TerminalSizeSuccess y q C z) : CoarseLead N p z := by
    have hg := critical_gain_of_terminal_size_success hcard y q hgain herror z hz
    have hl := lead_of_critical_gains (fun s => (z.sizes s:ℝ)) N
      (ζ*min (betaScale N p n*scale N p) 1/2) hg
    have hcard1 : (1:ℝ) ≤ Fintype.card (History (n+2)) := by
      exact_mod_cast Fintype.card_pos (α := History (n+2))
    have hpos : 0 ≤ ζ*min (betaScale N p n*scale N p) 1/2*N :=
      le_trans (by positivity) hlead
    have hm : ζ*min (betaScale N p n*scale N p) 1/2*N ≤
        (Fintype.card (History (n+2)):ℝ)*(ζ*min (betaScale N p n*scale N p) 1/2)*N := by
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hcard1 hpos
    exact hlead.trans (hm.trans hl)
  rw [← ofReal_measureReal (μ := Kbar (Binomial.closedProbability p) y)]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans (measureReal_mono ?_) hfail
  exact fun z hbad hgood => hbad (hinc z hgood)

end MajorityDynamics.GraphProcess.FaithfulTrajectory
