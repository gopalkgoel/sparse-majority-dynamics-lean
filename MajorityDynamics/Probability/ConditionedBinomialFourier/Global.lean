import MajorityDynamics.Probability.ConditionedBinomialFourier.Box
import MajorityDynamics.Probability.ConditionedBinomialFourier.MixtureGap
import MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency
import MajorityDynamics.Probability.ConditionedBinomialBox.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialFourier

/-- The fixed rectangular weight and width produce one fixed density-scale gap. -/
def gapConstant (β w : ℝ) : ℝ := β*intervalConstant*min (w^2) 1 / 2

theorem gapConstant_pos {β w : ℝ} (hβ : 0 < β) (hw : 0 < w) :
    0 < gapConstant β w := by
  unfold gapConstant
  exact div_pos (mul_pos (mul_pos hβ intervalConstant_pos)
    (lt_min (sq_pos_of_pos hw) zero_lt_one)) (by norm_num)

theorem gapConstant_le_half {β w : ℝ} (_hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    gapConstant β w ≤ 1/2 := by
  have hb : β*intervalConstant ≤ 1 := by
    calc
      β*intervalConstant ≤ 1*1 := mul_le_mul hβ1 intervalConstant_le_one
        intervalConstant_pos.le zero_le_one
      _ = 1 := by ring
  have hh : β*intervalConstant*min (w^2) 1 ≤ 1 := by
    calc
      β*intervalConstant*min (w^2) 1 ≤ 1*1 :=
        mul_le_mul hb (min_le_right _ _) (le_min (sq_nonneg w) zero_le_one) zero_le_one
      _ = 1 := by ring
  unfold gapConstant
  linarith

theorem rectangular_mixture_gap {d L : ℕ} (hd : 1 ≤ d) (a : Fin d → ℕ)
    (ν : Measure (Fin d → ℕ)) [IsProbabilityMeasure ν]
    {β w s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hw : 0 < w) (hs : 0 ≤ s)
    (hL : 16 ≤ L) (hwidth : w*Real.sqrt s ≤ (L : ℝ))
    (t : Fin d → ℝ) (ht : t ∈ HighFrequency.cube d) :
    ‖chi (ENNReal.ofReal β • ConditionedBinomialBox.uniformBox
      (ConditionedBinomialBox.Geometry.box a L) + ENNReal.ofReal (1-β) • ν) t‖ ≤
      1-gapConstant β w*min (s*‖t‖^2) 1 := by
  let μ := ConditionedBinomialBox.uniformBox (ConditionedBinomialBox.Geometry.box a L)
  let : IsProbabilityMeasure μ := ConditionedBinomialBox.uniformBox_probability _
    (ConditionedBinomialBox.Geometry.box_nonempty a (by omega))
  have hbox := uniformBox_chi_norm_gap a hL hd t ht
  have hm := mixture_norm_gap μ ν hβ0.le hβ1.le t hbox
  apply hm.trans
  have hwmin := width_min_lower hw.le hs hwidth (z := ‖t‖)
  have hfactor : 0 ≤ β*intervalConstant := mul_nonneg hβ0.le intervalConstant_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hwmin hfactor
  have hh : 0 ≤ β*intervalConstant*min (w^2) 1*min (s*‖t‖^2) 1 := by positivity
  dsimp [gapConstant]
  nlinarith

/-- Closed original-data Fourier estimate, on the entire fundamental cube.
The normalization, rectangular mixture and common side length are all proved
from the paper's density, sizes, tilts, matrix and row-balance assumptions. -/
theorem uniform_global_gap (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      let ρ := cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
      0 < p ∧ p < 1 ∧ IsProbabilityMeasure ρ ∧
      (∀ t ∈ HighFrequency.cube d, ‖chi ρ t‖ ≤ 1-c*min (p*N*‖t‖^2) 1) ∧
      ∀ (m : ℕ) (t : Fin d → ℝ), t ∈ HighFrequency.cube d →
        ‖centeredChi ρ m t‖ ≤ Real.exp (-c*m*min (p*N*‖t‖^2) 1) := by
  obtain ⟨w, W, A, cp, ce, β, hw, _hW, _hA, _hcp, _hce, hβ0, hβ1, N₁, hbox⟩ :=
    ConditionedBinomialBox.uniform_component θ hθlo hθhi d hd r M hM strict T hT
  obtain ⟨N₂, hlength⟩ := eventually_length_sixteen hθlo hθhi hT hw
  refine ⟨gapConstant β w, gapConstant_pos hβ0 hw,
    gapConstant_le_half hβ0.le hβ1.le, max N₁ N₂, ?_⟩
  intro N hN p hlo hhi η q hηlo hηhi hq hbal
  obtain ⟨hp, hp1, a, L, hb⟩ := hbox N ((le_max_left _ _).trans hN)
    p hlo hhi η q hηlo hηhi hq hbal
  obtain ⟨_hN1, _hp, _hp1, hlength⟩ := hlength N ((le_max_right _ _).trans hN) p hlo hhi
  let ρ := cond (Binomial.law η q)
    (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
  let : IsProbabilityMeasure ρ := hb.conditioned_probability
  obtain ⟨ν, hν, hmix⟩ := hb.mixture
  let := hν
  have hgap : ∀ t ∈ HighFrequency.cube d,
      ‖chi ρ t‖ ≤ 1-gapConstant β w*min (p*N*‖t‖^2) 1 := by
    intro t ht
    change ‖chi (cond (Binomial.law η q) _) t‖ ≤ _
    rw [hmix]
    exact rectangular_mixture_gap hd a ν hβ0 hβ1 hw
      (mul_nonneg hp.le (Nat.cast_nonneg N)) (hlength L hb.width_lower)
      hb.width_lower t ht
  refine ⟨hp, hp1, hb.conditioned_probability, hgap, ?_⟩
  intro m t ht
  have h := centeredChi_exp_of_gap ρ m t (hgap t ht)
  convert h using 1
  congr 1
  ring

end MajorityDynamics.Probability.ConditionedBinomialFourier
