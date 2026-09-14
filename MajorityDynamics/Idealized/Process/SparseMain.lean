import MajorityDynamics.Idealized.Process.OneStep
import MajorityDynamics.Idealized.Process.Induction
import MajorityDynamics.Idealized.Process.SparseSolvability
import MajorityDynamics.Idealized.Process.SparseEvolution
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.Process
open Universal Local Binomial Binomial.Approximation RowLimits
variable {n : ℕ}
def SparseIdealizedProcessTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ D : ℕ, 1 ≤ D →
  ∀ T : ℝ, 1 < T → ∃ ell : ℕ, 1 ≤ ell ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : Binomial.Probability, Binomial.Approximation.SparseRange θ T N p →
    ∃ a : Data, Specification N p D ell a ∧
      ∀ b : Data, Recursion N p D b → AgreeThrough D a b
def SparseOneStepTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → ∀ n ell : ℕ, 1 ≤ ell →
  ∃ ell' : ℕ, ell ≤ ell' ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
  ∀ N ≥ N₀, ∀ p : Binomial.Probability, Binomial.Approximation.SparseRange θ T N p →
  ∀ x : State n, StateSymmetric x → LevelEstimates N p ell x →
    ∃ q : Local.Tilt n, Solvable x q ∧ TiltSymmetric q ∧
      TiltEstimates N p ell' q ∧ StateSymmetric (nextState x q) ∧
      LevelEstimates N p ell' (nextState x q)

theorem one_step_sparse : SparseOneStepTheorem := by
  intro θ T hθlo hθhi hT n ell hell
  obtain ⟨L, _hL, R, hR, hγR, C, hC, N₀, hN₀, hsolve⟩ :=
    solvable_rows_sparse θ T hθlo hθhi hT n ell hell
  obtain ⟨A, hA, hrows⟩ := row_asymptotics_of_estimates n R hR.le
  let K := C + A * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨ellE, hellE, hevolution⟩ :=
    eventual_evolution_estimates_sparse θ T n ell L K hθhi (by linarith) hK
  let ell' := max ellE (L + 1)
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hsupport := eventually_support_sizes_sparse (n := n) θ T ell hθhi (by linarith)
  have hpositive := eventually_level_edges_positive_sparse (n := n) θ T ell hθhi (by linarith)
  have htilt := eventually_tilt_estimates_sparse θ T n L R C (by linarith) hθhi
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
theorem idealized_process_of_step_sparse (step : SparseOneStepTheorem) : SparseIdealizedProcessTheorem := by
  intro θ hθlo hθhi D hD T hT
  have finite : ∀ d : ℕ, ∃ ell : ℕ, 1 ≤ ell ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability,
        Binomial.Approximation.SparseRange θ T N p →
          ∃ a : Data, Specification N p (d + 1) ell a := by
    intro d
    induction d with
    | zero =>
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_initialState_estimates
      refine ⟨1, le_rfl, max N₀ 1, le_max_right _ _, ?_⟩
      intro N hN p _hp
      have hbase := hN₀ N ((le_max_left _ _).trans hN)
      exact ⟨initialData N p, initialData_specification N p (hbase.2.2 p)⟩
    | succ d ih =>
      obtain ⟨ell, hell, N₀, hN₀, hf⟩ := ih
      obtain ⟨ell', hell', N₁, _hN₁, hstep⟩ := step θ T hθlo hθhi hT d ell hell
      have hlog := (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
          (eventually_ge_atTop (1 : ℝ))
      obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hlog
      refine ⟨ell', hell.trans hell', max N₀ (max N₁ N₂),
        hN₀.trans (le_max_left _ _), ?_⟩
      intro N hN p hp
      have hn₀ : N₀ ≤ N := (le_max_left _ _).trans hN
      have hn₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
      have hn₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
      obtain ⟨a, ha⟩ := hf N hn₀ p hp
      obtain ⟨q, hq, hqsym, hqest, hnsym, hnest⟩ :=
        hstep N hn₁ p hp (a.state d) (ha.symmetry d (by omega)) (ha.estimates d (by omega))
      exact ⟨a.advance d q, ha.advance (hN₂ N hn₂) hell' q hq hqsym hqest hnsym hnest⟩
  obtain ⟨ell, hell, N₀, hN₀, hf⟩ := finite (D - 1)
  refine ⟨ell, hell, N₀, hN₀, ?_⟩
  intro N hN p hp
  obtain ⟨a, ha⟩ := hf N hN p hp
  have hd : D - 1 + 1 = D := by omega
  rw [hd] at ha
  exact ⟨a, ha, fun b hb => recursion_determined ha.toRecursion hb⟩

/-- Exact symmetric reference process on the wider density range. -/
theorem idealized_process_sparse : SparseIdealizedProcessTheorem :=
  idealized_process_of_step_sparse one_step_sparse

end MajorityDynamics.Idealized.Process
