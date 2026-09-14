import MajorityDynamics.Paper.UniformProblem
import MajorityDynamics.Paper.CleanupAsymptotics
import MajorityDynamics.Idealized.Process.SparseMain
import MajorityDynamics.GraphProcess.FaithfulTrajectory.SparseStopped
import MajorityDynamics.GraphProcess.FaithfulTrajectory.SparseTerminalStep
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

noncomputable section
open Filter Topology MeasureTheory Set
namespace MajorityDynamics.Paper
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution
open GraphProcess GraphProcess.FaithfulTrajectory GraphProcess.CoarseKernel
open Binomial.Approximation (SparseRange)

/-- Uniform expansion on the entire density interval, with a deterministic
density-dependent stopping day bounded independently of N, p and the coloring. -/
theorem uniform_expansion : UniformExpansionPhase := by
  intro θ T hθlo hθhi hT ε hε
  have hT0 : 0 < T := by linarith
  have he : 0 < ε/2 := half_pos hε
  let H := expansionDay θ
  let D := H+2
  obtain ⟨ell,hell,NP,_,hprocess⟩ :=
    Process.idealized_process_sparse θ hθlo hθhi D (by omega) T hT
  obtain ⟨U,δ,r,hTU,_,hr,hr4,hgap,hstop⟩ :=
    uniform_stopped_faithfulness hθlo hθhi hT ell D H hell (by omega)
      (expansionDay_exponent hθhi)
  have hU : 1 < U := hT.trans_le hTU
  obtain ⟨NS,_,hstop⟩ := hstop (ε/2) he
  have hterm := Filter.eventually_all.mpr (fun j : Fin (H+1) =>
    uniform_terminal_step_sparse θ U δ r hθlo hθhi hU hr (by linarith)
      hgap j.val ell (ε/2) he)
  obtain ⟨NT,hterm⟩ := eventually_atTop.mp hterm
  obtain ⟨NB,hband⟩ := EnumerationBounds.eventually_band_window
    (θ := θ) (η := 1/2) (T := T) (L := 1) (U := 1/2) (M := 1)
    (by norm_num) hθhi hT zero_lt_one (by norm_num) zero_lt_one
  refine ⟨max NP (max NS (max NT NB)),?_⟩
  intro N hN p τ c hp hτ hτT hinit
  obtain ⟨_,hp0,_,_,hpHalf⟩ := hband N (by omega) p hp.1 hp.2
  have hp1 : (p:ℝ) < 1 := lt_of_le_of_lt hpHalf (by norm_num)
  let pb : Binomial.Probability := ⟨p,hp0,hp1⟩
  have hpb : Binomial.closedProbability pb = p := Subtype.ext rfl
  have hpr : SparseRange θ T N pb := hp
  obtain ⟨hs,j,hj0,hjH,halo,hahi,_,hfaith⟩ := hstop N (by omega) pb hpr
  obtain ⟨a,ha,_⟩ := hprocess N (by omega) pb hpr
  have hpast := hfaith a ha τ hτ hτT c hinit
  have hpU := RowLimits.sparseRange_enlarge hT0 hTU hpr
  have hstep (y : Local.CoarseData (Fin N) j)
      (hy : Faithful N pb U δ τ a y) (_ : pAttainable p y) :
      Kbar p y {z | ¬CoarseLead N p z} ≤ ENNReal.ofReal (ε/2) := by
    have hh := hterm N (by omega) ⟨j,by omega⟩ pb hpU hs halo hahi.le a
      (ha.estimates j (by omega)) (ha.symmetry j (by omega)) τ
      ((inv_anti₀ hT0 hTU).trans hτ) (hτT.trans hTU)
      (Fin N) (Fintype.card_fin N) y hy
    simpa only [hpb] using hh
  have hb := actual_one_step j p c hp0 hp1 {y | Faithful N pb U δ τ a y}
    {z | CoarseLead N p z} (ENNReal.ofReal (ε/2)) hstep
  have hbad : graphLaw N p {G | ¬CoarseLead N p
      (rho p (FineState.actualState G c (j+1)))} ≤ ENNReal.ofReal ε := by
    have hpast' : graphLaw N p {G | ¬Faithful N pb U δ τ a
        (rho p (FineState.actualState G c j))} ≤ ENNReal.ofReal (ε/2) := by
      simpa only [hpb,actualCoarse,graphLaw,pb] using hpast
    refine hb.trans ((add_le_add hpast' le_rfl).trans ?_)
    rw [← ENNReal.ofReal_add he.le he.le,add_halves]
  apply le_trans (measure_mono ?_) hbad
  intro G hnot hlead
  exact hnot ⟨j+2,by omega,by dsimp [H] at hjH; omega,
    coarseLead_actual p G c hlead⟩

end MajorityDynamics.Paper
