import MajorityDynamics.Idealized.RowLimits.ApproximationSparse
import MajorityDynamics.Idealized.RowLimits.ApproximationLocal

/-! The actual binomial row approximation on the sparse range, with only
macroscopic trial intervals. No history or final-decision balance is assumed.
In particular this endpoint admits the growing terminal response scale. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation Analysis.ConditionalGaussian
variable {n : ℕ}

theorem sparseRange_enlarge {N : ℕ} {p : Probability} {θ T K : ℝ}
    (hT : 0 < T) (hTK : T ≤ K) (hp : SparseRange θ T N p) :
    SparseRange θ K N p := by
  constructor
  · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hT hTK)
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-θ))).trans_lt hp.1
  · exact hp.2.trans_le (mul_le_mul_of_nonneg_right hTK
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-(1 / 2 : ℝ))))

theorem row_normalized_comparison_sparse (θ T R : ℝ)
    (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, 1 ≤ Real.log (N : ℝ) →
      ∀ p : Probability, SparseRange θ T N p →
      ∀ (s : History (n + 1)) (sizes : Local.Sizes n),
      (∀ t, (N : ℝ) * ν n t / 2 ≤ (Local.trials sizes s t : ℝ)) →
      (∀ t, (Local.trials sizes s t : ℝ) ≤ 2 * N * ν n t) →
      ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
      ∀ b : Option Bool, ∀ o : MomentKind (Fintype.card (Fin (n + 1) → Bool)),
      |binomialNormalizedMoment N p sizes s (eventSupport sizes s b)
          (fun t => (p : ℝ) * Local.trials sizes s t) (scale N p) o σ -
        actualGaussianMoment N p sizes s σ b o| ≤
        C * Real.log N ^ (5 + Fintype.card (Fin (n + 1) → Bool)) / scale N p := by
  classical
  let K := geometryConstant n T R
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hK := geometryConstant_bounds (n := n) T R hT0 hR
  obtain ⟨C, hC, N₀, hN₀, hA⟩ := normalized_gaussian_comparison_sparse_finite
    (ι := History (n + 1) × Option Bool) θ K hθ hθ' hK.1
    (Fintype.card (Fin (n + 1) → Bool)) Fintype.card_pos
    (fun j => eventRows n j.2) (fun j => eventIntegerMatrix j.1 j.2)
    (fun j => eventIntegerMatrix_orthogonal j.1 j.2) (fun j => eventStrict j.1 j.2)
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N hN hlog p hp s sizes hlo hhi σ hσ b o
  have hn : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (hN₀.trans hN)
  have hnreal : 0 < (N : ℝ) := by exact_mod_cast hn
  have hKpos : 0 < K := zero_lt_one.trans hK.1
  have htr (t : History (n + 1)) : 0 < Local.trials sizes s t := by
    have hv := ν_positive n t
    have h := hlo t
    have : (0 : ℝ) < Local.trials sizes s t :=
      lt_of_lt_of_le (by positivity) h
    exact_mod_cast this
  have hsz : Sizes K N (Local.trials sizes s) := by
    intro t
    have hv := ν_positive n t
    have hkl : K⁻¹ < ν n t / 2 := by
      rw [inv_eq_one_div]
      apply (div_lt_iff₀ hKpos).mpr
      have hh := (div_lt_iff₀ hv).mp (hK.2.2 t).1
      nlinarith
    constructor
    · have hh := mul_lt_mul_of_pos_right hkl hnreal
      nlinarith [hlo t]
    · have hh := mul_lt_mul_of_pos_right (hK.2.2 t).2.1 hnreal
      nlinarith [hhi t]
  have hα (t : History (n + 1)) : |alpha N sizes s σ t| < K :=
    (rowAlpha_bound N hn (Local.trials sizes s t) (σ t) (ν n t) R
      (Nat.cast_nonneg _) (ν_positive n t) (hσ t) (hhi t)).trans_lt (hK.2.2 t).2.2
  have h := hA N hN p (sparseRange_enlarge hT0 hK.2.1.le hp)
    (Local.trials sizes s) hsz σ.ofLp (ν n) hα (s, b) o
  have heq : gaussianTilt p (Local.trials sizes s)
      (fun t => σ t / ν n t * Real.sqrt ((Local.trials sizes s t : ℝ) / N)) =
      rowTilt N p σ := by
    funext t
    exact rowAlpha_logit N hn p _ (htr t) _ _
  rw [heq] at h
  rw [eventSupport_normalized_integral]
  change |(∫ a in inequalityEvent (eventMatrix s b) (eventStrict s b),
    momentValue o (fun t => centered p (Local.trials sizes s) a t / scale N p)
      ∂Binomial.law (Local.trials sizes s) (rowTilt N p σ)) -
    actualGaussianMoment N p sizes s σ b o| ≤ _ at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_right₀ hlog (by have hh := moment_degree_le_two o; omega)

end MajorityDynamics.Idealized.RowLimits
