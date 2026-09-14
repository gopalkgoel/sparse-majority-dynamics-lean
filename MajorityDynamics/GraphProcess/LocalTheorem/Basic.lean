import MajorityDynamics.GraphProcess.LocalTransition.Main
import MajorityDynamics.GraphProcess.RowExactTotals.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace MajorityDynamics.GraphProcess.LocalTheorem
universe u
variable {V : Type u} [Fintype V] {n : ℕ}

/-- Transport of the literal array event to R1/R2/R3 on actual fine states.
Only the known fiber support is used; the degree array is never replaced. -/
theorem typical_failure_le (p : unitInterval) (y : Local.CoarseData V n)
    (q : Local.Tilt n) [IsProbabilityMeasure (CoarseKernel.Lambda p y)]
    (hs : CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1) :
    (CoarseKernel.Lambda p y).real {σ | ¬ LocalTransition.FiberTypical y q p 1 σ} ≤
      (CoarseKernel.Lambda p y).real
        {σ | σ.deg ∉ RowArray.values '' {d | RowConcentration.Good y p q d}} := by
  have ha : ∀ᵐ σ ∂CoarseKernel.Lambda p y, CoarseKernel.rho p σ = y :=
    (mem_ae_iff_prob_eq_one (Set.toFinite _).measurableSet).mpr hs
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ha] with σ hρ hbad hmem
  obtain ⟨d, hd, he⟩ := hmem
  exact hbad (LocalTransition.fiberTypical_of_good y q p σ d
    (congrArg Local.CoarseData.part hρ) he.symm hd)

/-- A convenient explicit rate for transfer of the existing power-one row bound. -/
def fiberError (C : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-(N : ℝ)) + C * (N : ℝ)^(-(1 : ℝ))

theorem fiberError_nonneg {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    0 ≤ fiberError C N := by
  unfold fiberError
  positivity

theorem fiberError_tendsto (C : ℝ) :
    Tendsto (fiberError C) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)) + C * (N : ℝ)^(-(1 : ℝ))) atTop (𝓝 0)
  have he : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(-(1 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp tendsto_natCast_atTop_atTop
  simpa only [mul_zero, add_zero] using he.add (hp.const_mul C)

end MajorityDynamics.GraphProcess.LocalTheorem
