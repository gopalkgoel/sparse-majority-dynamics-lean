import MajorityDynamics.Idealized.Process.Basic
import MajorityDynamics.Idealized.RowLimits.ComparisonTargets
import MajorityDynamics.Idealized.RowLimits.ContractBridges

/-! The Gaussian part of Step 7 of Theorem 5.2: replacing the solved mean
parameter by the universal mean changes branch probabilities and conditional
means by a uniform Lipschitz error. All laws and conditioning events are the
actual Gaussian row laws. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal

namespace MajorityDynamics.Idealized.Process
open Universal RowLimits
variable {n : ℕ}

theorem gaussian_branch_probability (s : History (n + 1)) (b : Bool)
    (σ : Row (n + 1)) :
    gaussianMass σ (childEvent s b) / gaussianMass σ (historyEvent s) =
      branchProbability s (ν n) σ b := by
  unfold branchProbability gaussianMass
  rw [← measureReal_congr (childEvent_ae_eq_cone s b (ν n) (ν_positive n) σ),
    ← measureReal_congr (historyEvent_ae_eq_cone s (ν n) (ν_positive n) σ)]
  rfl

theorem gaussianMass_le_one (σ : Row (n + 1)) (A : Set (Row (n + 1))) :
    |gaussianMass σ A| ≤ 1 := by
  unfold gaussianMass
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (measureReal_mono (subset_univ A)).trans_eq (by simp)

theorem gaussian_mean_parameter_distance {σ τ : Row (n + 1)} {e : ℝ}
    (he : 0 ≤ e) (hστ : ∀ t, |σ t - τ t| ≤ e) :
    dist (historyParameters σ) (historyParameters τ) ≤
        (Fintype.card (Fin (n + 1) → Bool) + 1 : ℝ) * e ∧
      ∀ b, dist (childParameters σ b 0) (childParameters τ b 0) ≤
        (Fintype.card (Fin (n + 1) → Bool) + 1 : ℝ) * e := by
  have hd := space_dist_le_of_coordinates he hστ
  constructor
  · simpa [historyParameters, Prod.dist_eq] using hd
  · intro b
    simpa [childParameters, Prod.dist_eq] using hd

/-- One constant works for every row and branch in a fixed compact mean box. -/
theorem gaussian_branch_lipschitz (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : History (n + 1)) (σ τ : Row (n + 1)),
      (∀ t, |σ t| ≤ R) → (∀ t, |τ t| ≤ R) → ∀ e : ℝ, 0 ≤ e →
      (∀ t, |σ t - τ t| ≤ e) →
      (∀ b, |branchProbability s (ν n) σ b - branchProbability s (ν n) τ b| ≤ K * e) ∧
      ∀ b t, |branchMean s (ν n) σ b t - branchMean s (ν n) τ b t| ≤ K * e := by
  obtain ⟨c, hc, hlower⟩ := gaussian_probabilities_uniform_lower n hR (show 0 ≤ (1 : ℝ) by norm_num)
  obtain ⟨B, _, L, hhistory, hchild⟩ := gaussian_boxes_uniform_control n R 1
  let d : ℝ := Fintype.card (Fin (n + 1) → Bool) + 1
  let K : ℝ := (1 / c + 1 / c ^ 2 + 1) * (L : ℝ) * d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro s σ τ hσ hτ e he hστ
  have hdist := gaussian_mean_parameter_distance he hστ
  have hσh := historyParameters_mem_box hR (show 0 ≤ (1 : ℝ) by norm_num) hσ
  have hτh := historyParameters_mem_box hR (show 0 ≤ (1 : ℝ) by norm_num) hτ
  have hσc := fun b => childParameters_mem_box hR (show 0 ≤ (1 : ℝ) by norm_num)
    hσ b (show |(0 : ℝ)| ≤ 1 by norm_num)
  have hτc := fun b => childParameters_mem_box hR (show 0 ≤ (1 : ℝ) by norm_num)
    hτ b (show |(0 : ℝ)| ≤ 1 by norm_num)
  have hmass : |gaussianMass σ (historyEvent s) - gaussianMass τ (historyEvent s)| ≤
      (L : ℝ) * (d * e) := by
    rw [gaussianMass_history_eq, gaussianMass_history_eq]
    exact abs_sub_le_of_lipschitz (hhistory s).mass_lipschitz hσh hτh hdist.1
  have hhσ := (hlower s σ hσ).1
  have hhτ := (hlower s τ hτ).1
  constructor
  · intro b
    have hmc : |gaussianMass σ (childEvent s b) - gaussianMass τ (childEvent s b)| ≤
        (L : ℝ) * (d * e) := by
      rw [← shiftedChildEvent_zero s b, gaussianMass_child_eq, gaussianMass_child_eq]
      exact abs_sub_le_of_lipschitz (hchild s b).mass_lipschitz (hσc b) (hτc b) (hdist.2 b)
    rw [← gaussian_branch_probability, ← gaussian_branch_probability]
    have hratio := ratio_error hc hhσ hhτ (gaussianMass_le_one τ (childEvent s b)) hmc hmass
    refine hratio.trans ?_
    dsimp [K]
    nlinarith [mul_nonneg L.coe_nonneg (mul_nonneg hd he)]
  · intro b t
    rw [← gaussianMean_child_eq_branchMean, ← gaussianMean_child_eq_branchMean,
      ← shiftedChildEvent_zero s b, gaussianMean_child_eq, gaussianMean_child_eq]
    have hm := abs_sub_le_of_lipschitz ((hchild s b).mean_lipschitz t) (hσc b) (hτc b) (hdist.2 b)
    refine hm.trans ?_
    dsimp [K]
    have hp : 0 ≤ 1 / c + 1 / c ^ 2 := by positivity
    nlinarith [mul_nonneg hp (mul_nonneg L.coe_nonneg (mul_nonneg hd he))]

end MajorityDynamics.Idealized.Process
