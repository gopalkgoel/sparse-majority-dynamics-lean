import MajorityDynamics.Probability.RandomOpinionsReduction.Orientation
import MajorityDynamics.Probability.RandomOpinionsReduction.Window

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace MajorityDynamics.Probability.RandomOpinionsReduction

theorem oriented_success_consensus {N : ℕ} (θ : ℝ) (c : Paper.Coloring N) (G : Paper.Graph N)
    (h : G ∈ Paper.successEvent θ (majorityOrientation c)) :
    (c, G) ∈ consensusEvent N θ := by
  apply (consensusEvent_iff θ c G).mpr
  unfold Paper.successEvent majorityOrientation at h
  split_ifs at h with hc
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    simpa only [Set.mem_ofPred_eq, coloringOnDay_flip, flip, Bool.not_eq_false'] using h

theorem average_failure_bound {N : ℕ} (θ : ℝ) (p : unitInterval)
    (B : Set (Paper.Coloring N)) (δ : ℝ≥0∞)
    (h : ∀ c ∈ B, Paper.graphLaw N p {G | (c,G) ∉ consensusEvent N θ} ≤ δ) :
    jointLaw N p (consensusEvent N θ)ᶜ ≤ uniformColoringLaw N Bᶜ + δ := by
  classical
  rw [jointLaw, Measure.prod_apply (Set.toFinite _).measurableSet]
  calc
    _ ≤ ∫⁻ c, Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) c + δ ∂uniformColoringLaw N := by
      apply lintegral_mono
      intro c
      change Paper.graphLaw N p {G | (c,G) ∉ consensusEvent N θ} ≤
        Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) c + δ
      by_cases hc : c ∈ B
      · simpa [Set.indicator_of_notMem (show c ∉ Bᶜ from by simpa using hc)] using h c hc
      · simp only [Set.indicator_of_mem (show c ∈ Bᶜ from hc)]
        exact (prob_le_one (μ := Paper.graphLaw N p)).trans (le_add_right le_rfl)
    _ = _ := by
      rw [lintegral_add_left (Measurable.indicator measurable_const (Set.toFinite _).measurableSet)]
      simp [lintegral_indicator (Set.toFinite _).measurableSet]

/-- Full reduction from the exact existing fixed-lead theorem, with no further premise. -/
theorem random_opinions_of_main (main : Paper.MainTheorem) : RandomOpinionsTheorem := by
  intro θ T hθ hθ1 hT ε hε
  have hε2 : 0 < ε/2 := by positivity
  obtain ⟨A, hA, M, hM1, hM⟩ := random_bias_window (ε/2) hε2
  let U : ℝ := max T (A+1)
  have hTU : T ≤ U := le_max_left _ _
  have hAU : A+1 ≤ U := le_max_right _ _
  have hU : 1 < U := hT.trans_le hTU
  obtain ⟨K, hK⟩ := main θ U hθ hθ1 hU (ε/2) hε2
  refine ⟨max M K, ?_⟩
  intro N hN p hp
  have hMN : M ≤ N := (le_max_left _ _).trans hN
  have hKN : K ≤ N := (le_max_right _ _).trans hN
  have hN1 := hM1.trans hMN
  have hpU := densityRange_mono (show 0 < T by linarith) hTU hp
  have hgood (c : Paper.Coloring N) (hc : c ∈ goodBias N A) :
      Paper.graphLaw N p {G | (c,G) ∉ consensusEvent N θ} ≤ ENNReal.ofReal (ε/2) := by
    obtain ⟨τ, hlo, hhi, hb⟩ := exact_majority_bias hN1 c hc.1 hc.2
    have hi : U⁻¹ ≤ A⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have hm := hK N hKN p τ (majorityOrientation c) hpU (hi.trans hlo) (hhi.trans hAU) hb
    apply le_trans (measure_mono (t := (Paper.successEvent θ (majorityOrientation c))ᶜ) ?_) hm
    intro G hG hS
    exact hG (oriented_success_consensus θ c G hS)
  have ha := average_failure_bound θ p (goodBias N A) (ENNReal.ofReal (ε/2)) hgood
  have hb := hM N hMN
  calc
    _ ≤ uniformColoringLaw N (goodBias N A)ᶜ + ENNReal.ofReal (ε/2) := ha
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hb le_rfl
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end MajorityDynamics.Probability.RandomOpinionsReduction
