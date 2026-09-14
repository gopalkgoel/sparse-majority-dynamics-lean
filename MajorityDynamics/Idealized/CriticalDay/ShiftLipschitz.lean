import MajorityDynamics.Idealized.Process.EvolutionGaussian
noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits Process
variable {n : ℕ}
theorem shifted_parameter_distance {σ τ : Row (n + 1)} {e : ℝ}
    (u : ℝ) (he : 0 ≤ e) (hστ : ∀ t, |σ t - τ t| ≤ e) :
    dist (historyParameters σ) (historyParameters τ) ≤
        (Fintype.card (Fin (n + 1) → Bool) + 1 : ℝ) * e ∧
      ∀ b, dist (childParameters σ b u) (childParameters τ b u) ≤
        (Fintype.card (Fin (n + 1) → Bool) + 1 : ℝ) * e := by
  have hd := space_dist_le_of_coordinates he hστ
  constructor
  · simpa [historyParameters, Prod.dist_eq] using hd
  · intro b
    simpa [childParameters, Prod.dist_eq] using hd

theorem gaussian_shifted_lipschitz (n : ℕ) (R U : ℝ) (hR : 0 ≤ R) (hU : 0 ≤ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : History (n+1)) (σ τ : Row (n+1)),
      (∀ t, |σ t| ≤ R) → (∀ t, |τ t| ≤ R) → ∀ u : ℝ, |u| ≤ U →
      ∀ e : ℝ, 0 ≤ e → (∀ t, |σ t - τ t| ≤ e) → ∀ b,
        |gaussianMass σ (shiftedChildEvent s b u) / gaussianMass σ (historyEvent s) -
          gaussianMass τ (shiftedChildEvent s b u) / gaussianMass τ (historyEvent s)| ≤ K*e := by
  obtain ⟨c, hc, hlower⟩ := gaussian_probabilities_uniform_lower n hR hU
  obtain ⟨B, _, L, hhistory, hchild⟩ := gaussian_boxes_uniform_control n R U
  let d : ℝ := Fintype.card (Fin (n + 1) → Bool) + 1
  let K : ℝ := (1 / c + 1 / c ^ 2 + 1) * (L : ℝ) * d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro s σ τ hσ hτ u hu e he hστ
  have hdist := shifted_parameter_distance u he hστ
  have hσh := historyParameters_mem_box hR hU hσ
  have hτh := historyParameters_mem_box hR hU hτ
  have hσc := fun b => childParameters_mem_box hR hU
    hσ b hu
  have hτc := fun b => childParameters_mem_box hR hU
    hτ b hu
  have hmass : |gaussianMass σ (historyEvent s) - gaussianMass τ (historyEvent s)| ≤
      (L : ℝ) * (d * e) := by
    rw [gaussianMass_history_eq, gaussianMass_history_eq]
    exact abs_sub_le_of_lipschitz (hhistory s).mass_lipschitz hσh hτh hdist.1
  have hhσ := (hlower s σ hσ).1
  have hhτ := (hlower s τ hτ).1
  intro b
  have hmc : |gaussianMass σ (shiftedChildEvent s b u) - gaussianMass τ (shiftedChildEvent s b u)| ≤
      (L : ℝ) * (d * e) := by
    rw [gaussianMass_child_eq, gaussianMass_child_eq]
    exact abs_sub_le_of_lipschitz (hchild s b).mass_lipschitz (hσc b) (hτc b) (hdist.2 b)
  have hratio := ratio_error hc hhσ hhτ (gaussianMass_le_one τ (shiftedChildEvent s b u)) hmc hmass
  refine hratio.trans ?_
  dsimp [K]
  nlinarith [mul_nonneg L.coe_nonneg (mul_nonneg hd he)]

end MajorityDynamics.Idealized.CriticalDay
