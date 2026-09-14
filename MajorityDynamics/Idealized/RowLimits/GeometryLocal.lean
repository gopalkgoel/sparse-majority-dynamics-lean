import MajorityDynamics.Idealized.RowLimits.Geometry
import MajorityDynamics.Idealized.RowLimits.Basic

/-! Uniform trial geometry for the actual history-indexed row model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation
variable {n : ℕ}

 theorem trials_cast (sizes : Local.Sizes n) (s t : History (n + 1))
    (h : 0 < sizes t) :
    (Local.trials sizes s t : ℝ) = (sizes t : ℝ) - if s = t then 1 else 0 := by
  classical
  by_cases he : s = t
  · simp only [Local.trials, he, if_true]
    rw [Nat.cast_sub (by omega)]
    norm_num
  · simp [Local.trials, he]

 def normalizedVariance (N : ℕ) (sizes : Local.Sizes n)
    (s t : History (n + 1)) : ℝ := (Local.trials sizes s t : ℝ) / N

 def normalizedMean (N : ℕ) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (t : History (n + 1)) : ℝ :=
    σ t * (Local.trials sizes s t : ℝ) / ((N : ℝ) * ν n t)

 def alpha (N : ℕ) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (t : History (n + 1)) : ℝ :=
    rowAlpha N (Local.trials sizes s t) (σ t) (ν n t)

 theorem admissible_close {N ell : ℕ} {p : Probability} {T ξ : ℝ}
    {s : History (n + 1)} {sizes : Local.Sizes n}
    (h : AdmissibleSizes N p ell T ξ s sizes) (t : History (n + 1)) :
    |(sizes t : ℝ) - (N : ℝ) * ν n t| ≤
      (N : ℝ) * (Real.log N ^ ell / scale N p) := by
  simpa only [scale, div_mul_eq_mul_div, mul_div_assoc] using h.close t

 theorem eventual_trial_geometry (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Probability, Density θ T N p →
      ∀ ξ : ℝ, ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
        AdmissibleSizes N p ell T ξ s sizes → ∀ t,
          0 < Local.trials sizes s t ∧
          (N : ℝ) * ν n t / 2 < (Local.trials sizes s t : ℝ) ∧
          (Local.trials sizes s t : ℝ) < 2 * N * ν n t ∧
          |normalizedVariance N sizes s t - ν n t| ≤
            Real.log N ^ ell / scale N p + 1 / N := by
  classical
  have he : ∀ᶠ N : ℕ in atTop, ∀ t : History (n + 1),
      0 < N ∧ ∀ p : Probability, Density θ T N p →
        Real.log N ^ ell / scale N p + 1 / N < ν n t / 2 :=
    Filter.eventually_all.mpr (fun t => eventually_size_error_small θ T (ν n t / 2)
      ell hθ hT (div_pos (ν_positive n t) (by norm_num)))
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with N he hN
  refine ⟨by omega, ?_⟩
  intro p hp ξ s sizes had t
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hδ : |(if s = t then 1 else 0 : ℝ)| ≤ 1 := by split_ifs <;> norm_num
  have hraw := corrected_trial_interval (N : ℝ) (sizes t) (ν n t)
    (if s = t then 1 else 0) (Real.log N ^ ell / scale N p) hn (ν_positive n t)
    hδ (admissible_close had t) ((he t).2 p hp)
  have hsz : 0 < sizes t := by
    have hpv : 0 < (N : ℝ) * ν n t / 2 := div_pos (mul_pos hn (ν_positive n t)) (by norm_num)
    have hd : 0 ≤ (if s = t then 1 else 0 : ℝ) := by split_ifs <;> norm_num
    have : (0 : ℝ) < sizes t := by linarith [hraw.1]
    exact_mod_cast this
  have hc := trials_cast sizes s t hsz
  have htr : (0 : ℝ) < Local.trials sizes s t := by rw [hc]; nlinarith [hraw.1, ν_positive n t]
  refine ⟨by exact_mod_cast htr, ?_, ?_, ?_⟩
  · simpa only [hc] using hraw.1
  · simpa only [hc] using hraw.2
  · dsimp [normalizedVariance]
    rw [hc]
    exact normalized_variance_error _ _ _ _ _ hn hδ (admissible_close had t)

/-- A fixed enlargement sufficient for trial intervals, density and all bounded tilts. -/
def geometryConstant (n : ℕ) (T R : ℝ) : ℝ :=
  1 + 2 * |T| + ∑ t : History (n + 1),
    (2 / ν n t + 2 * ν n t + |R| / ν n t * Real.sqrt (2 * ν n t))

theorem geometryConstant_bounds (T R : ℝ) (hT : 0 < T) (hR : 0 ≤ R) :
    1 < geometryConstant n T R ∧ T < geometryConstant n T R ∧
      ∀ t : History (n + 1),
        2 / ν n t < geometryConstant n T R ∧
        2 * ν n t < geometryConstant n T R ∧
        R / ν n t * Real.sqrt (2 * ν n t) < geometryConstant n T R := by
  classical
  have hsum : 0 ≤ ∑ t : History (n + 1),
      (2 / ν n t + 2 * ν n t + |R| / ν n t * Real.sqrt (2 * ν n t)) := by
    apply Finset.sum_nonneg
    intro t _
    have := ν_positive n t
    positivity
  have hbase : 1 < geometryConstant n T R ∧ T < geometryConstant n T R := by
    dsimp [geometryConstant]
    rw [abs_of_pos hT]
    constructor <;> linarith
  refine ⟨hbase.1, hbase.2, ?_⟩
  intro t
  have ht := ν_positive n t
  have hterm := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    show 0 ≤ 2 / ν n i + 2 * ν n i + |R| / ν n i * Real.sqrt (2 * ν n i) from by
      have := ν_positive n i; positivity) (Finset.mem_univ t)
  have hpos : 0 ≤ R / ν n t * Real.sqrt (2 * ν n t) := by positivity
  simp only [abs_of_nonneg hR] at hterm
  dsimp [geometryConstant]
  simp only [abs_of_pos hT, abs_of_nonneg hR]
  refine ⟨?_, ?_, ?_⟩ <;> linarith [div_pos (by norm_num : (0 : ℝ) < 2) ht]

theorem density_enlarge {N : ℕ} {p : Probability} {θ T T₁ : ℝ}
    (hT : 0 < T) (hTT : T ≤ T₁) (hp : Density θ T N p) :
    Density θ T₁ N p := by
  constructor
  · have h := mul_le_mul_of_nonneg_right (inv_anti₀ hT hTT)
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-θ))
    exact h.trans_lt hp.1
  · exact hp.2.trans_le (mul_le_mul_of_nonneg_right hTT
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-θ)))

/-- Uniform geometry for A.2, with no eventual admissibility assumption left
    for the caller to discharge. The explicit constant precedes the threshold. -/
theorem eventual_row_geometry (θ T R : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hR : 0 ≤ R) :
    1 < geometryConstant n T R ∧
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Probability, Density θ T N p →
      Density θ (geometryConstant n T R) N p ∧
      ∀ ξ : ℝ, ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
        AdmissibleSizes N p ell T ξ s sizes →
        ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ t,
          0 < Local.trials sizes s t ∧
          (geometryConstant n T R)⁻¹ * N < (Local.trials sizes s t : ℝ) ∧
          (Local.trials sizes s t : ℝ) < geometryConstant n T R * N ∧
          |alpha N sizes s σ t| < geometryConstant n T R ∧
          logistic (logOdds p + alpha N sizes s σ t /
            Real.sqrt ((p : ℝ) * Local.trials sizes s t)) = rowTilt N p σ t := by
  have hK := geometryConstant_bounds (n := n) T R hT hR
  refine ⟨hK.1, ?_⟩
  filter_upwards [eventual_trial_geometry (n := n) θ T ell hθ hT] with N hN
  refine ⟨hN.1, ?_⟩
  intro p hp
  refine ⟨density_enlarge hT hK.2.1.le hp, ?_⟩
  intro ξ s sizes had σ hσ t
  have ht := hN.2 p hp ξ s sizes had t
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN.1
  have hv := ν_positive n t
  have hKpos : 0 < geometryConstant n T R := lt_trans zero_lt_one hK.1
  have hkl : (geometryConstant n T R)⁻¹ < ν n t / 2 := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hKpos).mpr
    have hh := (div_lt_iff₀ hv).mp (hK.2.2 t).1
    nlinarith
  refine ⟨ht.1, (mul_lt_mul_of_pos_right hkl hn).trans ?_, ?_, ?_, ?_⟩
  · nlinarith [ht.2.1]
  · have hh := mul_lt_mul_of_pos_right (hK.2.2 t).2.1 hn
    nlinarith [ht.2.2.1]
  · exact (rowAlpha_bound N hN.1 (Local.trials sizes s t) (σ t) (ν n t) R
      (Nat.cast_nonneg _) hv (hσ t) ht.2.2.1.le).trans_lt (hK.2.2 t).2.2
  · exact rowAlpha_logit N hN.1 p _ ht.1 _ _

theorem normalized_parameters_bounds (N : ℕ) (hN : 0 < N)
    (sizes : Local.Sizes n) (s : History (n + 1)) (σ : Row (n + 1))
    (R : ℝ) (hσ : ∀ t, |σ t| ≤ R)
    (hlo : ∀ t, (N : ℝ) * ν n t / 2 ≤ (Local.trials sizes s t : ℝ))
    (hhi : ∀ t, (Local.trials sizes s t : ℝ) ≤ 2 * N * ν n t) :
    (∀ t, ν n t / 2 ≤ normalizedVariance N sizes s t ∧
      normalizedVariance N sizes s t ≤ 2 * ν n t) ∧
    ∀ t, |normalizedMean N sizes s σ t| ≤ 2 * R := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  constructor
  · intro t
    dsimp [normalizedVariance]
    constructor
    · apply (le_div_iff₀ hn).mpr
      nlinarith [hlo t]
    · apply (div_le_iff₀ hn).mpr
      nlinarith [hhi t]
  · intro t
    have hv := ν_positive n t
    have hR : 0 ≤ R := (abs_nonneg (σ t)).trans (hσ t)
    dsimp [normalizedMean]
    rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg (Local.trials sizes s t) : (0 : ℝ) ≤ Local.trials sizes s t), abs_of_pos (mul_pos hn hv)]
    apply (div_le_iff₀ (mul_pos hn hv)).mpr
    have hh := mul_le_mul_of_nonneg_right (hσ t) (Nat.cast_nonneg (Local.trials sizes s t))
    have hh' := mul_le_mul_of_nonneg_left (hhi t) hR
    nlinarith

theorem normalized_mean_close {N ell : ℕ} (hN : 0 < N) {p : Probability}
    {T ξ : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (had : AdmissibleSizes N p ell T ξ s sizes) (hsz : ∀ t, 0 < sizes t)
    (σ : Row (n + 1)) (R : ℝ) (hσ : ∀ t, |σ t| ≤ R) :
    ∀ t, |normalizedMean N sizes s σ t - σ t| ≤
      R / ν n t * (Real.log N ^ ell / scale N p + 1 / N) := by
  intro t
  dsimp [normalizedMean]
  rw [trials_cast sizes s t (hsz t)]
  exact normalized_mean_error _ _ _ _ _ _ _ (by exact_mod_cast hN)
    (ν_positive n t) (by split_ifs <;> norm_num) (admissible_close had t) (hσ t)

theorem geometryConstant_two_mul_lt (T R : ℝ) (hT : 0 < T) :
    2 * T < geometryConstant n T R := by
  have hs : 0 ≤ ∑ t : History (n + 1),
      (2 / ν n t + 2 * ν n t + |R| / ν n t * Real.sqrt (2 * ν n t)) := by
    apply Finset.sum_nonneg
    intro t _
    have := ν_positive n t
    positivity
  dsimp [geometryConstant]
  rw [abs_of_pos hT]
  linarith

end MajorityDynamics.Idealized.RowLimits
