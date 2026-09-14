import MajorityDynamics.Literature.LWAdapters.GraphLaws
import MajorityDynamics.Literature.LWAdapters.Growth
import MajorityDynamics.Literature.LWFormal.Final

noncomputable section
open Filter
open scoped Topology
namespace MajorityDynamics.Literature.LWAdapters
open DegreeEnumeration

theorem average_eq {n m : ℕ} (d : Fin n → ℕ) (hs : ∑ i, d i = 2*m) :
    LW.avgDeg d = graphAverage n m := by
  have hh : ∑ i, (d i : ℝ) = 2*(m:ℝ) := by exact_mod_cast hs
  simp [LW.avgDeg, graphAverage, hh]

theorem correction_eq {n m : ℕ} (d : Fin n → ℕ) (hs : ∑ i, d i = 2*m) :
    LW.expFactor d = graphCorrection m d := by
  simp only [LW.expFactor, LW.gamma2, LW.density, average_eq d hs,
    graphCorrection, graphGamma, graphDensity]

theorem graph_enumeration : GraphEnumerationTheorem := by
  obtain ⟨μ₀, hμ₀, hsource⟩ := LW.theorem_1_4
  refine ⟨μ₀, hμ₀, ?_⟩
  intro α hαlo hαhi m hcap hlogs
  obtain ⟨ω, hω, hlow⟩ := graph_slow_growth id m tendsto_id hlogs
  obtain ⟨C, N, hbound⟩ := hsource α hαlo hαhi ω hω
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  filter_upwards [hcap, hlow, eventually_ge_atTop N, eventually_ge_atTop 2] with n hc hl hn hn2
  intro d hd
  have hn2' : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hu : graphAverage n (m n) ≤ μ₀*(n:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : (0:ℝ) < n-1)).mp hc.2
    exact hh.trans (by nlinarith)
  obtain ⟨e, he, hEq⟩ := hbound n hn (m n) hl hu d ⟨hd.2.1, hd.2.2⟩
  refine ⟨e, ?_, ?_⟩
  · apply he.trans
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    unfold LW.err14
    positivity
  · rw [probGnm_eq_degreeLaw, correction_eq d hd.2.1] at hEq
    rw [probBinom_eq_binomialLaw d ?_ hd.2.1] at hEq
    · exact hEq
    · have hb := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hd.1 i
      simpa [hd.2.1] using hb

end MajorityDynamics.Literature.LWAdapters
