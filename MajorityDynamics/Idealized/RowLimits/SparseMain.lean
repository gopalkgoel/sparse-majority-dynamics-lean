import MajorityDynamics.Idealized.RowLimits.Main
import MajorityDynamics.Idealized.RowLimits.SparseUniform
import MajorityDynamics.Idealized.RowLimits.SparseAdmissibleComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis Binomial Binomial.Approximation
variable {n : ℕ}
set_option maxHeartbeats 1200000
def SparseRowLimitsTheorem : Prop :=
  ∀ n : ℕ, ∃ lower : ℝ → ℝ → ℝ,
    ∀ ell : ℕ, 1 ≤ ell → ∃ ell' : ℕ,
    ∀ (T R : ℝ), 1 < T → 0 < R → 0 < lower T R ∧
      ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
        ∀ (N : ℕ), N₀ ≤ N → ∀ p : Binomial.Probability,
          T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) → (p : ℝ) < T * (N : ℝ) ^ (-(1/2:ℝ)) →
          ∀ ξ : ℝ, 0 < ξ → ξ ≤ T → ∀ (s : History (n + 1)) (sizes : Local.Sizes n),
            AdmissibleSizes N p ell T ξ s sizes →
            SmoothQuantities N p sizes s ∧
            ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
              lower T R ≤ gaussianMass σ (historyEvent s) ∧
              (∀ b, lower T R ≤ gaussianMass σ (shiftedChildEvent s b (shift N p sizes))) ∧
              |shift N p sizes| ≤ T ∧
              Estimates N p sizes s σ (shift N p sizes) C (error ell' N p ξ) ∧
              (|nextImbalance sizes| ≤ ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N) →
                |shift N p sizes| ≤ ξ ∧ ξ ≤ error ell' N p ξ ∧
                (∀ b, lower T R ≤ gaussianMass σ (childEvent s b)) ∧
                Estimates N p sizes s σ 0 C (error ell' N p ξ))

theorem row_limits_sparse : SparseRowLimitsTheorem := by
  classical
  intro n
  refine ⟨fun T R => (gaussian_boxes_uniform_lower n R T).choose, ?_⟩
  intro ell _hell
  let m := 5 + Fintype.card (Fin (n + 1) → Bool)
  let ell' := m + ell
  refine ⟨ell', ?_⟩
  intro T R hT hR
  let c₀ := (gaussian_boxes_uniform_lower n R T).choose
  have hc₀ : 0 < c₀ := (gaussian_boxes_uniform_lower n R T).choose_spec.1
  refine ⟨hc₀, ?_⟩
  intro θ hθ hθ'
  obtain ⟨B, hB, L, hcontrol⟩ := eventwise_compact_control n R T
  obtain ⟨A, hA, N₁, hN₁, happ⟩ :=
    row_normalized_comparison_admissible_sparse (n := n) θ T R ell hθ hθ' hT hR.le
  let K := distanceConstant n R
  let D := A + (L : ℝ) * K
  have hK : 0 < K := distanceConstant_pos n R hR.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hc : 0 < c₀ / 2 := half_pos hc₀
  have hT0 : 0 < T := zero_lt_one.trans hT
  refine ⟨finalConstant (c₀ / 2) B D (T + 1),
    finalConstant_pos hc hB0 hD (by positivity), ?_⟩
  have hevent :=
    (eventual_event_geometry_sparse (n := n) θ T R ell hθ' hT0 hR.le).and
      (eventually_error_budget_sparse θ T c₀ A ell' hθ' hT0 hc₀ hA)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hp₁ hp₂ ξ hξ hξT s sizes had
  have hNge₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNge₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  have hgeo := (hN₂ N hNge₂).1
  have hbudget := (hN₂ N hNge₂).2
  have hpos : 0 < N := hgeo.1
  have hlog : 1 ≤ Real.log (N : ℝ) := hgeo.2.1
  have hp : SparseRange θ T N p := ⟨hp₁, hp₂⟩
  have hszgeo := hgeo.2.2 p hp ξ hξ.le hξT s sizes had
  have hsz : ∀ t, 0 < sizes t := hszgeo.1
  have hε : 0 ≤ error ell' N p ξ := error_nonneg (by omega) hξ.le
  have hεE : error ell' N p ξ ≤ T + 1 := (hbudget.2.2 p hp).2 ξ hξT
  have hexp : error ell N p ξ ≤ error ell' N p ξ :=
    error_mono_exponent (show ell ≤ ell' by dsimp [ell']; omega) hlog
  let δ := Real.log (N : ℝ) ^ m / scale N p
  have hδ : δ ≤ error ell' N p ξ := by
    have hpowers : Real.log (N : ℝ) ^ m ≤ Real.log (N : ℝ) ^ ell' :=
      pow_le_pow_right₀ hlog (by dsimp [ell']; omega)
    exact (div_le_div_of_nonneg_right hpowers (Real.sqrt_nonneg _)).trans
      (le_add_of_nonneg_right hξ.le)
  have hsmall : A * δ ≤ c₀ / 2 := by
    have hpowers : Real.log (N : ℝ) ^ m ≤ Real.log (N : ℝ) ^ ell' :=
      pow_le_pow_right₀ hlog (by dsimp [ell']; omega)
    calc
      _ ≤ A * (Real.log (N : ℝ) ^ ell' / scale N p) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hpowers (Real.sqrt_nonneg _)) hA.le
      _ = A * Real.log (N : ℝ) ^ ell' / scale N p := by ring
      _ ≤ _ := (hbudget.2.2 p hp).1
  refine ⟨smooth_quantities N p sizes s, ?_⟩
  intro σ hσ
  have hpoint := hszgeo.2 σ hσ
  have hg := hpoint.2
  have hlower (b : Option Bool) (z)
      (hz : z ∈ gaussianBox n (eventRows n b) R T) :
      c₀ ≤ GaussianRegularity.mass (eventMatrix s b) z :=
    eventwise_compact_lower n R T s b z hz
  have hraw (u : ℝ)
      (hy : ∀ b, targetParameters σ b u ∈ gaussianBox n (eventRows n b) R T)
      (hdist : ∀ b, dist (actualNormalizedParameters N p sizes s σ b)
        (targetParameters σ b u) ≤ K * error ell' N p ξ) :
      ∀ b, EventRawEstimates N p sizes s σ (eventSupport sizes s b)
        (targetEvent s b u) (c₀ / 2) B D (error ell' N p ξ) := by
    intro b
    apply eventRawEstimates_of_comparison (hcontrol s b)
      (hg.actual_mem b) (hy b) hc₀ hA.le
      (hlower b _ (hg.actual_mem b)) (hlower b _ (hy b))
    · intro o
      have hh := happ N hNge₁ p hp ξ hξT s sizes had σ hσ b o
      rw [actualGaussianMoment_eq_parameterMoment] at hh
      simpa only [δ, m, mul_div_assoc, scale] using hh
    · exact hdist b
    · exact hδ
    · exact hsmall
    · exact target_mass_eq s σ b u
    · exact target_first_eq s σ b u
    · exact target_second_eq s σ b u
  have hrawShift := hraw (shift N p sizes) hg.target_mem
    (fun b => (hg.distance b).trans (mul_le_mul_of_nonneg_left hexp hK.le))
  have hgaussLower (u : ℝ)
      (hy : ∀ b, targetParameters σ b u ∈ gaussianBox n (eventRows n b) R T)
      (b : Option Bool) : c₀ ≤ gaussianMass σ (targetEvent s b u) := by
    rw [target_mass_eq]
    exact hlower b _ (hy b)
  have hJB (u : ℝ) (b : Bool) : |gaussianMass σ (shiftedChildEvent s b u)| ≤ B :=
    (gaussianMass_le_one σ _).trans hB
  have hcenter : (p : ℝ) / Real.sqrt ((p : ℝ) * N) ≤ error ell' N p ξ :=
    diagonal_error_le hlog hξ.le
  refine ⟨hgaussLower _ hg.target_mem none,
    (fun b => hgaussLower _ hg.target_mem (some b)), hpoint.1, ?_, ?_⟩
  · exact estimates_of_raw (hrawShift none) (fun b => hrawShift (some b))
      hc hB0 hD hε hεE hpos hsz (hJB _) hcenter
  · intro hbalance
    have hshift : |shift N p sizes| ≤ ξ := shift_abs_le_of_small_balance hpos hbalance
    have hrawZero := hraw 0 hg.target_zero_mem
      (fun b => (hg.distance_zero hshift b).trans (mul_le_mul_of_nonneg_left hexp hK.le))
    refine ⟨hshift, error_ge_xi (by omega), ?_, ?_⟩
    · intro b
      simpa only [targetEvent, shiftedChildEvent_zero] using
        hgaussLower 0 hg.target_zero_mem (some b)
    · exact estimates_of_raw (hrawZero none) (fun b => hrawZero (some b))
        hc hB0 hD hε hεE hpos hsz (hJB 0) hcenter

end MajorityDynamics.Idealized.RowLimits
