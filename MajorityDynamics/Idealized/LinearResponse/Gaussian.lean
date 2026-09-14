import MajorityDynamics.Idealized.LinearResponse.Basic
import MajorityDynamics.Idealized.RowLimits.ComparisonTargets
import MajorityDynamics.Idealized.RowLimits.ContractBridges
import MajorityDynamics.Idealized.RowLimits.EventsGaussian
import MajorityDynamics.Universal.Nondegeneracy

/-! Transport of the Gaussian functionals from a bounded mean parameter to the
universal parameter `γ`, and identification of the universal quantities. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal
open MajorityDynamics.Analysis
open MajorityDynamics.Idealized.RowLimits

/-- Lipschitz transport in the Gaussian mean, with a constant fixed before the
row, the parameters, and the tolerance. -/
theorem gaussian_bridge (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : History (n + 1)) (σ γ : Row (n + 1)),
      (∀ t, |σ t| ≤ R) → (∀ t, |γ t| ≤ R) → ∀ δ : ℝ, 0 ≤ δ → (∀ t, |σ t - γ t| ≤ δ) →
      |gaussianMass σ (historyEvent s) - gaussianMass γ (historyEvent s)| ≤ K * δ ∧
      (∀ t, |gaussianMean σ (historyEvent s) t - gaussianMean γ (historyEvent s) t| ≤ K * δ) ∧
      (∀ t t', |gaussianCovariance σ (historyEvent s) t t' -
        gaussianCovariance γ (historyEvent s) t t'| ≤ K * δ) ∧
      (∀ b, |gaussianMass σ (childEvent s b) - gaussianMass γ (childEvent s b)| ≤ K * δ) ∧
      (∀ b t, |gaussianMean σ (childEvent s b) t - gaussianMean γ (childEvent s b) t| ≤ K * δ) := by
  obtain ⟨_, _, L, hcontrol⟩ := gaussian_boxes_uniform_control n R 1
  refine ⟨(L : ℝ) * ((Fintype.card (Fin (n + 1) → Bool) : ℝ) + (n : ℝ) + 2), by positivity, ?_⟩
  intro s σ γ hσ hγ δ hδ hclose
  have hc := hcontrol.1 s
  have hσh := historyParameters_mem_box hR zero_le_one hσ
  have hγh := historyParameters_mem_box hR zero_le_one hγ
  have hdist : dist (historyParameters σ) (historyParameters γ) ≤
      ((Fintype.card (Fin (n + 1) → Bool) : ℝ) + (n : ℝ) + 2) * δ := by
    have h := parameters_dist_le_of_coordinates (x := historyParameters σ)
      (y := historyParameters γ) hδ hclose
      (fun i => by
        show |(WithLp.toLp 2 (ν n) : Row (n + 1)) i - (WithLp.toLp 2 (ν n) : Row (n + 1)) i| ≤ δ
        rw [sub_self, abs_zero]
        exact hδ)
      (fun j => by
        show |(0 : Analysis.ConditionalGaussian.Space n) j -
          (0 : Analysis.ConditionalGaussian.Space n) j| ≤ δ
        rw [sub_self, abs_zero]
        exact hδ)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hδ)
    linarith
  have hdistc (b : Bool) : dist (childParameters σ b 0) (childParameters γ b 0) ≤
      ((Fintype.card (Fin (n + 1) → Bool) : ℝ) + (n : ℝ) + 2) * δ := by
    have h := parameters_dist_le_of_coordinates (x := childParameters σ b 0)
      (y := childParameters γ b 0) hδ hclose
      (fun i => by
        show |(WithLp.toLp 2 (ν n) : Row (n + 1)) i - (WithLp.toLp 2 (ν n) : Row (n + 1)) i| ≤ δ
        rw [sub_self, abs_zero]
        exact hδ)
      (fun j => by
        show |childThreshold (n := n) b 0 j - childThreshold (n := n) b 0 j| ≤ δ
        rw [sub_self, abs_zero]
        exact hδ)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hδ)
    push_cast
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gaussianMass_history_eq, gaussianMass_history_eq]
    exact (abs_sub_le_of_lipschitz hc.mass_lipschitz hσh hγh hdist).trans_eq
      (mul_assoc _ _ _).symm
  · intro t
    rw [gaussianMean_history_eq, gaussianMean_history_eq]
    exact (abs_sub_le_of_lipschitz (hc.mean_lipschitz t) hσh hγh hdist).trans_eq
      (mul_assoc _ _ _).symm
  · intro t t'
    rw [gaussianCovariance_history_eq, gaussianCovariance_history_eq]
    exact (abs_sub_le_of_lipschitz (hc.covariance_lipschitz t t') hσh hγh hdist).trans_eq
      (mul_assoc _ _ _).symm
  · intro b
    have hcb := hcontrol.2 s b
    have hσb := childParameters_mem_box hR zero_le_one hσ b (by rw [abs_zero]; exact zero_le_one)
    have hγb := childParameters_mem_box hR zero_le_one hγ b (by rw [abs_zero]; exact zero_le_one)
    rw [← shiftedChildEvent_zero s b, gaussianMass_child_eq s σ b 0, gaussianMass_child_eq s γ b 0]
    exact (abs_sub_le_of_lipschitz hcb.mass_lipschitz hσb hγb (hdistc b)).trans_eq
      (mul_assoc _ _ _).symm
  · intro b t
    have hcb := hcontrol.2 s b
    have hσb := childParameters_mem_box hR zero_le_one hσ b (by rw [abs_zero]; exact zero_le_one)
    have hγb := childParameters_mem_box hR zero_le_one hγ b (by rw [abs_zero]; exact zero_le_one)
    rw [← shiftedChildEvent_zero s b, gaussianMean_child_eq s σ b 0, gaussianMean_child_eq s γ b 0]
    exact (abs_sub_le_of_lipschitz (hcb.mean_lipschitz t) hσb hγb (hdistc b)).trans_eq
      (mul_assoc _ _ _).symm

/-! ### Universal identities -/

theorem gaussianMass_universal_history (n : ℕ) (s : History (n + 1)) :
    gaussianMass (γ n s) (historyEvent s) = (dayLaw n s).real (historyEvent s) := rfl

theorem gaussianMean_universal_history (n : ℕ) (s t : History (n + 1)) :
    gaussianMean (γ n s) (historyEvent s) t = ∫ x, x t ∂historyLaw n s := by
  rw [gaussianMean_eq_integral]
  rfl

theorem gaussianMean_universal_child (n : ℕ) (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    gaussianMean (γ n s) (childEvent s b) t = ∫ x, x t ∂childLaw n s b := by
  rw [gaussianMean_eq_integral]
  rfl

theorem gaussianCovariance_universal (n : ℕ) (s t t' : History (n + 1)) :
    gaussianCovariance (γ n s) (historyEvent s) t t' = conditionalCovariance n s t t' := by
  rw [conditionalCovariance_entry, gaussianCovariance, gaussianMean_eq_integral,
    gaussianMean_eq_integral]
  unfold gaussianSecond gaussianMass
  have hcond : ConditionalGaussian.condition (rowLaw (ν n) (γ n s)) (historyEvent s) =
      historyLaw n s := rfl
  rw [hcond]
  have hint : (∫ x in historyEvent s, x t * x t' ∂rowLaw (ν n) (γ n s)) /
      (rowLaw (ν n) (γ n s) (historyEvent s)).toReal = ∫ x, x t * x t' ∂historyLaw n s := by
    simp only [historyLaw, dayLaw, ConditionalGaussian.condition, integral_smul_measure,
      ENNReal.toReal_inv, smul_eq_mul]
    exact (div_eq_inv_mul _ _)
  rw [hint]

/-- The universal split ratio is the paper's `ν[sb]/ν[s]`. -/
theorem universal_split_ratio (n : ℕ) (s : History (n + 1)) (b : Bool) :
    gaussianMass (γ n s) (childEvent s b) / gaussianMass (γ n s) (historyEvent s) =
      ν (n + 1) (append s b) / ν n s := by
  have hν : ν n s ≠ 0 := (ν_positive n s).ne'
  rw [ν_recursion_events n s b]
  have hcancel : ν n s * (historyLaw n s).real (childEvent s b) / ν n s =
      (historyLaw n s).real (childEvent s b) := by
    field_simp
  rw [hcancel]
  have h := branchProbability_eq_event_condition s (ν n) (ν_positive n) (γ n s) b
  rw [show (historyLaw n s).real (childEvent s b) = branchProbability s (ν n) (γ n s) b from h.symm]
  unfold branchProbability gaussianMass
  rw [measure_congr (childEvent_ae_eq_cone s b (ν n) (ν_positive n) (γ n s)),
    measure_congr (historyEvent_ae_eq_cone s (ν n) (ν_positive n) (γ n s))]
  rfl

theorem universal_split_eq (n : ℕ) (s : History (n + 1)) (b : Bool) :
    (historyLaw n s).real (childEvent s b) = ν (n + 1) (append s b) / ν n s := by
  have hν : ν n s ≠ 0 := (ν_positive n s).ne'
  rw [ν_recursion_events n s b]
  field_simp

end MajorityDynamics.Idealized.LinearResponse
