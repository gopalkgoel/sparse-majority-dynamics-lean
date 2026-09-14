import MajorityDynamics.Idealized.RowLimits.EventsBounds
import MajorityDynamics.Idealized.RowLimits.EventsGaussian
import MajorityDynamics.Idealized.RowLimits.Comparison

/-! A single uniform compact-geometry package for E.3. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis Binomial Binomial.Approximation
variable {n r : ℕ}

def rowParameterBox (n r : ℕ) (T R : ℝ) :
    Set (GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) r) :=
  parameterBox (2 * R) (2 * T + 1) (fun t => ν n t / 2) (fun t => 2 * ν n t)

def normalizedParameters (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1))
    (M : Matrix (Fin r) (History (n + 1)) ℝ) :
    GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) r :=
  ((WithLp.toLp 2 (normalizedMean N sizes s σ),
    WithLp.toLp 2 (normalizedVariance N sizes s)), normalizedThreshold N p sizes s M)

theorem rowParameterBox_compact (n r : ℕ) (T R : ℝ) :
    IsCompact (rowParameterBox n r T R) := parameterBox_compact _ _ _ _

theorem rowParameterBox_positive (n r : ℕ) (T R : ℝ) :
    ∀ x ∈ rowParameterBox n r T R, GaussianRegularity.positiveVariance x :=
  parameterBox_positive (fun t => div_pos (ν_positive n t) (by norm_num))

theorem target_parameters_mem (T R : ℝ) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (σ : Row (n + 1)) (hσ : ∀ t, |σ t| ≤ R) (u : ℝ) (hu : |u| ≤ T) :
    historyParameters σ ∈ rowParameterBox n n T R ∧
    ∀ b, childParameters σ b u ∈ rowParameterBox n (n + 1) T R := by
  have hm : ∀ t, -2 * R ≤ σ t ∧ σ t ≤ 2 * R := by
    intro t
    have := abs_le.mp (hσ t)
    constructor <;> linarith
  have hv : ∀ t, ν n t / 2 ≤ ν n t ∧ ν n t ≤ 2 * ν n t := by
    intro t
    have := ν_positive n t
    constructor <;> linarith
  have hh : historyParameters σ ∈ rowParameterBox n n T R := by
    refine ⟨⟨?_, hv⟩, ?_⟩
    · intro t
      simpa only [historyParameters, childParameters, neg_mul] using hm t
    · intro j
      change -(2 * T + 1) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 2 * T + 1
      constructor <;> linarith
  refine ⟨hh, ?_⟩
  intro b
  refine ⟨⟨?_, hv⟩, ?_⟩
  · intro t
    simpa only [historyParameters, childParameters, neg_mul] using hm t
  · intro j
    change -(2 * T + 1) ≤ childThreshold b u j ∧ childThreshold b u j ≤ 2 * T + 1
    apply abs_le.mp
    have hb : |childThreshold (n := n) b u j| ≤ T := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [childThreshold_last, abs_mul]
        have hs : |sign b| = 1 := by cases b <;> norm_num
        simpa only [hs, one_mul] using hu
      · simpa only [childThreshold_castSucc, abs_zero] using hT
    linarith

theorem normalized_parameters_mem {N : ℕ} (hN : 0 < N) (p : Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (σ : Row (n + 1))
    (M : Matrix (Fin r) (History (n + 1)) ℝ) (T R : ℝ)
    (hσ : ∀ t, |σ t| ≤ R)
    (hlo : ∀ t, (N : ℝ) * ν n t / 2 ≤ (Local.trials sizes s t : ℝ))
    (hhi : ∀ t, (Local.trials sizes s t : ℝ) ≤ 2 * N * ν n t)
    (hu : ∀ j, |normalizedThreshold N p sizes s M j| ≤ 2 * T + 1) :
    normalizedParameters N p sizes s σ M ∈ rowParameterBox n r T R := by
  have hb := normalized_parameters_bounds N hN sizes s σ R hσ hlo hhi
  exact ⟨⟨fun t => abs_le.mp (hb.2 t), hb.1⟩, fun j => abs_le.mp (hu j)⟩

/-- Fixed coordinate-error coefficient, independent of density and size. -/
def parameterErrorConstant (n : ℕ) (R : ℝ) : ℝ :=
  2 + ∑ t : History (n + 1), 2 * |R| / ν n t

theorem parameterErrorConstant_bounds (R : ℝ) (hR : 0 ≤ R) :
    2 ≤ parameterErrorConstant n R ∧ ∀ t, 2 * R / ν n t ≤ parameterErrorConstant n R := by
  classical
  have hh : ∀ t : History (n + 1), 0 ≤ 2 * |R| / ν n t := by
    intro t
    exact div_nonneg (by positivity) (ν_positive n t).le
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun t _ => hh t))
  · intro t
    have ht := Finset.single_le_sum (fun t (_ : t ∈ Finset.univ) => hh t) (Finset.mem_univ t)
    dsimp [parameterErrorConstant]
    rw [abs_of_nonneg hR] at ht ⊢
    linarith

/-- Coordinatewise estimates for the actual normalized parameters, ready for
    the E.2 Lipschitz comparison. -/
theorem normalized_parameter_errors {N ell : ℕ} (hN : 0 < N)
    (hlog : 1 ≤ Real.log (N : ℝ)) {p : Probability} {T ξ R : ℝ}
    {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hs : ∀ t, 0 < sizes t)
    (hξ : 0 ≤ ξ) (hR : 0 ≤ R) (σ : Row (n + 1)) (hσ : ∀ t, |σ t| ≤ R) :
    (∀ t, |normalizedMean N sizes s σ t - σ t| ≤ parameterErrorConstant n R * error ell N p ξ) ∧
    (∀ t, |normalizedVariance N sizes s t - ν n t| ≤ parameterErrorConstant n R * error ell N p ξ) ∧
    (∀ j, |normalizedThreshold N p sizes s (historyMatrix s) j| ≤ parameterErrorConstant n R * error ell N p ξ) ∧
    ∀ b j, |normalizedThreshold N p sizes s (childMatrix s b) j - childThreshold b (shift N p sizes) j| ≤
      parameterErrorConstant n R * error ell N p ξ := by
  have hsmall := elementary_errors_le_rate N ell p (by omega) hlog
  have hr : 0 ≤ Real.log N ^ ell / scale N p :=
    div_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  have he : Real.log N ^ ell / scale N p ≤ error ell N p ξ := le_add_of_nonneg_right hξ
  have he0 : 0 ≤ error ell N p ξ := hr.trans he
  have hK := parameterErrorConstant_bounds (n := n) R hR
  have hK1 : 1 ≤ parameterErrorConstant n R := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    have ht := normalized_mean_close hN ha hs σ R hσ t
    have hv := ν_positive n t
    have hb : Real.log N ^ ell / scale N p + 1 / N ≤ 2 * error ell N p ξ := by linarith [hsmall.1]
    have hh := mul_le_mul_of_nonneg_left hb (div_nonneg hR hv.le)
    have hk := mul_le_mul_of_nonneg_right (hK.2 t) he0
    calc
      _ ≤ R / ν n t * (Real.log N ^ ell / scale N p + 1 / N) := ht
      _ ≤ R / ν n t * (2 * error ell N p ξ) := hh
      _ = 2 * R / ν n t * error ell N p ξ := by ring
      _ ≤ _ := hk
  · intro t
    have ht := normalized_variance_error (N : ℝ) (sizes t) (ν n t)
      (if s = t then 1 else 0) (Real.log N ^ ell / scale N p)
      (by exact_mod_cast hN) (by split_ifs <;> norm_num) (admissible_close ha t)
    change |(Local.trials sizes s t : ℝ) / N - ν n t| ≤ _
    rw [trials_cast sizes s t (hs t)]
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right hK.1 he0, hsmall.1])
  · intro j
    have ht := normalizedThreshold_history_bound hN ha hs j
    have hh : ξ + (p : ℝ) / Real.sqrt ((p : ℝ) * N) ≤ error ell N p ξ := by
      change ξ + (p : ℝ) / scale N p ≤ Real.log N ^ ell / scale N p + ξ
      linarith [hsmall.2]
    exact ht.trans (hh.trans (le_mul_of_one_le_left he0 hK1))
  · intro b j
    have ht := normalizedThreshold_child_error hN ha hs hξ b j
    have hh : ξ + (p : ℝ) / Real.sqrt ((p : ℝ) * N) ≤ error ell N p ξ := by
      change ξ + (p : ℝ) / scale N p ≤ Real.log N ^ ell / scale N p + ξ
      linarith [hsmall.2]
    exact ht.trans (hh.trans (le_mul_of_one_le_left he0 hK1))

theorem normalized_parameter_distances {N ell : ℕ} (hN : 0 < N)
    (hlog : 1 ≤ Real.log (N : ℝ)) {p : Probability} {T ξ R : ℝ}
    {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hs : ∀ t, 0 < sizes t)
    (hξ : 0 ≤ ξ) (hR : 0 ≤ R) (σ : Row (n + 1)) (hσ : ∀ t, |σ t| ≤ R) :
    dist (normalizedParameters N p sizes s σ (historyMatrix s)) (historyParameters σ) ≤
      (Fintype.card (Fin (n + 1) → Bool) + (n + 1) + 1 : ℝ) *
        parameterErrorConstant n R * error ell N p ξ ∧
    (∀ b, dist (normalizedParameters N p sizes s σ (childMatrix s b))
      (childParameters σ b (shift N p sizes)) ≤
      (Fintype.card (Fin (n + 1) → Bool) + (n + 1) + 1 : ℝ) *
        parameterErrorConstant n R * error ell N p ξ) ∧
    (|shift N p sizes| ≤ ξ → ∀ b,
      dist (normalizedParameters N p sizes s σ (childMatrix s b))
        (childParameters σ b 0) ≤
      (Fintype.card (Fin (n + 1) → Bool) + (n + 1) + 1 : ℝ) *
        parameterErrorConstant n R * error ell N p ξ) := by
  have herr := normalized_parameter_errors hN hlog ha hs hξ hR σ hσ
  have hK := parameterErrorConstant_bounds (n := n) R hR
  have hr : 0 ≤ Real.log N ^ ell / scale N p :=
    div_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  have he : 0 ≤ error ell N p ξ := add_nonneg hr hξ
  have hek : 0 ≤ parameterErrorConstant n R * error ell N p ξ :=
    mul_nonneg (by linarith [hK.1]) he
  have hg := parameters_dist_le_of_coordinates
    (x := normalizedParameters N p sizes s σ (historyMatrix s)) (y := historyParameters σ)
    hek herr.1 herr.2.1
    (show ∀ j, |(normalizedParameters N p sizes s σ (historyMatrix s)).2 j -
      (historyParameters σ).2 j| ≤ parameterErrorConstant n R * error ell N p ξ from by
        simpa only [normalizedParameters, historyParameters, PiLp.zero_apply, sub_zero] using herr.2.2.1)
  refine ⟨?_, ?_, ?_⟩
  · apply hg.trans
    have hk0 : 0 ≤ parameterErrorConstant n R := by linarith
    nlinarith [mul_nonneg hk0 he]
  · intro b
    have hb := parameters_dist_le_of_coordinates
      (x := normalizedParameters N p sizes s σ (childMatrix s b))
      (y := childParameters σ b (shift N p sizes)) hek herr.1 herr.2.1 (herr.2.2.2 b)
    simpa only [mul_assoc, Nat.cast_add, Nat.cast_one] using hb
  · intro hshift b
    have hu : ∀ j, |normalizedThreshold N p sizes s (childMatrix s b) j -
        childThreshold (n := n) b 0 j| ≤ parameterErrorConstant n R * error ell N p ξ := by
      intro j
      have hz : childThreshold (n := n) b 0 j = 0 := by
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      rw [hz, sub_zero]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · have hd := normalizedThreshold_child_last (N := N) p sizes s hs b
        have hb : |childThreshold (n := n) b (shift N p sizes) (Fin.last n)| ≤ ξ := by
          rw [childThreshold_last, abs_mul]
          have hs : |sign b| = 1 := by cases b <;> norm_num
          simpa only [hs, one_mul] using hshift
        have hh := (abs_sub_le (normalizedThreshold N p sizes s (childMatrix s b) (Fin.last n))
          (childThreshold (n := n) b (shift N p sizes) (Fin.last n)) 0)
        simp only [sub_zero] at hh
        have hsmall := (elementary_errors_le_rate N ell p (by omega) hlog).2
        have hkb := mul_le_mul_of_nonneg_right (show 1 ≤ parameterErrorConstant n R by linarith) he
        change (p : ℝ) / Real.sqrt ((p : ℝ) * N) ≤ Real.log N ^ ell / Real.sqrt ((p : ℝ) * N) at hsmall
        dsimp [error] at hkb ⊢
        linarith
      · simpa only [normalizedThreshold_child_castSucc] using herr.2.2.1 i
    have hb := parameters_dist_le_of_coordinates
      (x := normalizedParameters N p sizes s σ (childMatrix s b))
      (y := childParameters σ b 0) hek herr.1 herr.2.1 hu
    simpa only [mul_assoc, Nat.cast_add, Nat.cast_one] using hb

/-- All actual and target Gaussian parameters lie in fixed compact boxes,
    uniformly over the paper's varying density and admissible size vector. -/
theorem eventual_parameters_mem (θ T R : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hR : 0 ≤ R) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ p : Probability, Density θ T N p → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ T →
      ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
        AdmissibleSizes N p ell T ξ s sizes →
        (∀ t, 0 < sizes t) ∧ ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
          |shift N p sizes| ≤ T ∧
          normalizedParameters N p sizes s σ (historyMatrix s) ∈ rowParameterBox n n T R ∧
          historyParameters σ ∈ rowParameterBox n n T R ∧
          ∀ b, normalizedParameters N p sizes s σ (childMatrix s b) ∈ rowParameterBox n (n + 1) T R ∧
            childParameters σ b (shift N p sizes) ∈ rowParameterBox n (n + 1) T R ∧
            childParameters σ b 0 ∈ rowParameterBox n (n + 1) T R := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventual_trial_geometry (n := n) θ T ell hθ hT,
    eventually_size_error_small θ T 1 ell hθ hT zero_lt_one, hl] with N hgeom hsmall hlog
  refine ⟨hgeom.1, hlog, ?_⟩
  intro p hp ξ hξ hξT s sizes ha
  have hsz : ∀ t, 0 < sizes t := by
    intro t
    have ht := (hgeom.2 p hp ξ s sizes ha t).1
    dsimp [Local.trials] at ht
    omega
  refine ⟨hsz, ?_⟩
  intro σ hσ
  have hs := shift_abs_le hgeom.1 ha
  have htarget := target_parameters_mem T R hT.le hR σ hσ _ hs
  have htarget0 := target_parameters_mem T R hT.le hR σ hσ 0 (by simpa using hT.le)
  have hrate := (hsmall.2 p hp)
  have hps : (p : ℝ) / Real.sqrt ((p : ℝ) * N) ≤ 1 := by
    have hh := (elementary_errors_le_rate N ell p (by omega) hlog).2
    change (p : ℝ) / scale N p ≤ 1
    have hi : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith
  have hlo := fun t => (hgeom.2 p hp ξ s sizes ha t).2.1.le
  have hhi := fun t => (hgeom.2 p hp ξ s sizes ha t).2.2.1.le
  have hist : normalizedParameters N p sizes s σ (historyMatrix s) ∈ rowParameterBox n n T R := by
    apply normalized_parameters_mem hgeom.1 p sizes s σ (historyMatrix s) T R hσ hlo hhi
    intro j
    have hh := normalizedThreshold_history_bound hgeom.1 ha hsz j
    linarith
  refine ⟨hs, hist, htarget.1, ?_⟩
  intro b
  refine ⟨?_, htarget.2 b, htarget0.2 b⟩
  apply normalized_parameters_mem hgeom.1 p sizes s σ (childMatrix s b) T R hσ hlo hhi
  intro j
  have hh := normalizedThreshold_child_error hgeom.1 ha hsz hξ b j
  have hb : |childThreshold (n := n) b (shift N p sizes) j| ≤ T := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [childThreshold_last, abs_mul]
      have hsign : |sign b| = 1 := by cases b <;> norm_num
      simpa only [hsign, one_mul] using hs
    · simpa only [childThreshold_castSucc, abs_zero] using hT.le
  have hu := abs_sub_le (normalizedThreshold N p sizes s (childMatrix s b) j)
    (childThreshold (n := n) b (shift N p sizes) j) 0
  simp only [sub_zero] at hu
  linarith

end MajorityDynamics.Idealized.RowLimits
