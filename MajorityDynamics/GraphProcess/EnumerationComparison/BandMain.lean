import MajorityDynamics.GraphProcess.EnumerationComparison.BandUniformSource
import MajorityDynamics.GraphProcess.EnumerationComparison.BandBasic
import MajorityDynamics.GraphProcess.EnumerationComparison.Atoms
import MajorityDynamics.GraphProcess.EnumerationComparison.Factorization
import MajorityDynamics.GraphProcess.EnumerationComparison.Events

/-! Complete Appendix B.2, on the original graphical and conditioned tilted
row laws. Constants and threshold precede every varying finite datum. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open EnumerationBounds
universe u

theorem uniform_band_weak_comparison {θ η T : ℝ} (n : ℕ)
    (hη : 0 < η) (hηθ : η ≤ θ) (hθhi : θ < 1) (hT : 1 < T) :
    BandWeakComparisonTheorem.{u} θ η T n := by
  obtain ⟨N₀,hN₀⟩ := uniform_band_source hη hηθ hθhi hT
  refine ⟨weakConstant n T + correctionCount n, add_pos (weakConstant_pos n T)
    (correctionCount_pos n), N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts q d htot hreg
  obtain ⟨h,hi,hc⟩ := hN₀ N hN V hcard n p hlo hhi y d hsizes hcounts htot hreg
  have hf := factor_shift y q d (fun s => relative_internal y d h htot s (hi s))
    (fun r => relative_cross y d h htot r (hc _ _ (ne_of_lt r.property)))
  have hweak := weak_correction_bound hT h
  have hx := Real.one_le_rpow h.mean_one (by norm_num : (0:ℝ) ≤ 2/7)
  have hpos := correctionCount_pos n
  apply hf.sandwich _ measureReal_nonneg
  rw [← hcard]
  nlinarith

theorem uniform_band_strong_comparison {θ η T CΓ : ℝ} (n : ℕ)
    (hη : 0 < η) (hηθ : η ≤ θ) (hθhi : θ < 1) (hT : 1 < T) (hΓ : 0 < CΓ) :
    BandStrongComparisonTheorem.{u} θ η T CΓ n := by
  obtain ⟨N₀,hN₀⟩ := uniform_band_source hη hηθ hθhi hT
  refine ⟨strongConstant n T CΓ + correctionCount n,
    add_pos (strongConstant_pos n hΓ) (correctionCount_pos n), N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts q E hE
  have := GraphicalArray.law_probability y
  have := BlockPairLaws.conditioned_probability y q
  apply sandwich_event
  intro d hd
  obtain ⟨htot,hreg,hgamma⟩ := hE d hd
  obtain ⟨h,hi,hc⟩ := hN₀ N hN V hcard n p hlo hhi y d hsizes hcounts htot hreg
  have hf := factor_shift y q d (fun s => relative_internal y d h htot s (hi s))
    (fun r => relative_cross y d h htot r (hc _ _ (ne_of_lt r.property)))
  exact hf.sandwich (by have := strong_correction_bound hT h hΓ hgamma; linarith)
    measureReal_nonneg

end MajorityDynamics.GraphProcess.EnumerationComparison
