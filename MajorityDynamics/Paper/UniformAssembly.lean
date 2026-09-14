import MajorityDynamics.Paper.UniformProblem
import MajorityDynamics.Paper.UniformCleanup
import MajorityDynamics.Paper.UniformPseudorandomness
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! The outer uniform theorem reduces to uniform expansion. The closed proof
is supplied by `UniformExpansion` and assembled in `UniformMain`. This helper
keeps its explicit expansion premise for modularity. -/
noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Paper

theorem uniform_main_of_expansion (hExpansion : UniformExpansionPhase) : SparseMainTheorem := by
  obtain ⟨CJ, hCJ, hP⟩ := pseudorandomness_lower_only
  intro θ T hθlo hθhi hT ε hε
  have hT0 : 0 < T := by linarith
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨NE, hE⟩ := hExpansion θ T hθlo hθhi hT (ε / 2) hhalf
  obtain ⟨NP, hP⟩ := hP θ T hθhi hT0 (ε / 2) hhalf
  obtain ⟨NC, hC⟩ := uniform_cleanup_at_stopping_day θ T CJ hθhi hT hCJ
  obtain ⟨NB, hB⟩ := GraphProcess.EnumerationBounds.eventually_band_window
    (θ := θ) (η := 1 / 2) (T := T) (L := 1) (U := 99 / 100) (M := 1)
    (by norm_num) hθhi hT zero_lt_one (by norm_num) zero_lt_one
  refine ⟨max NE (max NP (max NC NB)), ?_⟩
  intro N hN p τ c hp hτlo hτhi hinit
  have hcap := (hB N (by omega) p hp.1 hp.2).2.2.2.2
  have hexp := hE N (by omega) p τ c hp hτlo hτhi hinit
  have hps := hP N (by omega) p hp.1 hcap
  have hsub : (uniformSuccessEvent θ c)ᶜ ⊆
      (uniformExpansionEvent θ p c)ᶜ ∪ (pseudorandomEvent p CJ)ᶜ := by
    intro G hfail
    by_cases he : G ∈ uniformExpansionEvent θ p c
    · right
      intro hg
      obtain ⟨d, hd, hdH, hlead⟩ := he
      exact hfail (hC N (by omega) p G c hp.1 hg d hd hdH hlead)
    · exact Or.inl he
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hexp hps).trans ?_))
  rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

end MajorityDynamics.Paper
