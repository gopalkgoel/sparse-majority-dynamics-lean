import MajorityDynamics.Idealized.Process.Solvability
import MajorityDynamics.Idealized.Process.SupportUniform
import MajorityDynamics.Idealized.Process.Positivity
import MajorityDynamics.Idealized.Process.TiltUniform
import MajorityDynamics.Idealized.Process.Evolution
import MajorityDynamics.Idealized.Process.Finite

/-! # The closed uniform analytic step for the idealized process -/

noncomputable section
open Filter
open scoped Topology

namespace MajorityDynamics.Idealized.Process

open Universal Binomial Binomial.Approximation

theorem one_step : OneStepTheorem := by
  intro θ T hθlo hθhi hT n ell hell
  obtain ⟨L, _hL, R, hR, hγR, C, hC, N₀, hN₀, hsolve⟩ :=
    solvable_rows θ T hθlo hθhi hT n ell hell
  obtain ⟨A, hA, hrows⟩ := row_asymptotics_of_estimates n R hR.le
  let K := C + A * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨ellE, hellE, hevolution⟩ :=
    eventual_evolution_estimates θ T n ell L K hθhi (by linarith) hK
  let ell' := max ellE (L + 1)
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hsupport := eventually_support_sizes (n := n) θ T ell hθhi (by linarith)
  have hpositive := eventually_level_edges_positive (n := n) θ T ell hθhi (by linarith)
  have htilt := eventually_tilt_estimates θ T n L R C (by linarith) hθhi
    (by linarith) hR.le hC.le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((((hlog.and hsupport).and hpositive).and htilt).and hevolution)
  refine ⟨ell', hellE.trans (le_max_left _ _), max N₀ N₁,
    hN₀.trans (le_max_left _ _), ?_⟩
  intro N hN p hp x hsym hx
  obtain ⟨⟨⟨⟨hlog, hsupport⟩, hpositive⟩, htilt⟩, hevolution⟩ :=
    hN₁ N ((le_max_right _ _).trans hN)
  obtain ⟨σ, hσR, hσγ, hsolves, hest⟩ :=
    hsolve N ((le_max_left _ _).trans hN) p hp x hsym hx
  let q : Local.Tilt n := fun s => RowLimits.rowTilt N p (σ s)
  have hsizes := hsupport p hp x hx
  have hq : Solvable x q := by
    refine ⟨fun s => by have := hsizes s; omega, hpositive p hp x hx, ?_, hsolves, ?_⟩
    · intro s
      exact history_eventMass_pos x.sizes hsizes s (q s)
    · intro q' hq'
      exact solving_tilt_unique x.sizes hsizes x.edges hq' hsolves
  have hqsym := solving_tilt_symmetric x hsym q hq
  have hqest : TiltEstimates N p (L + 1) q := htilt p hp σ hσR hγR hσγ
  have hρ : 0 ≤ Real.log N ^ L / scale N p := by
    apply div_nonneg (pow_nonneg (le_trans zero_le_one hlog) _) (Real.sqrt_nonneg _)
  have hrow : RowAsymptotics N p x.sizes q (K * (Real.log N ^ L / scale N p)) :=
    hrows N p x.sizes σ C C (Real.log N ^ L / scale N p) hC.le hρ hσR hγR hσγ hest
  have hnex := hevolution p hp x q hx hrow
  exact ⟨q, hq, hqsym, hqest.mono hlog (le_max_right _ _),
    nextState_symmetric x hsym q hqsym, hnex.mono hlog (le_max_left _ _)⟩

end MajorityDynamics.Idealized.Process
