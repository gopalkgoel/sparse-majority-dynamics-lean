import MajorityDynamics.Idealized.RowLimits.UniformEvents
import MajorityDynamics.Idealized.RowLimits.ErrorBounds
import MajorityDynamics.Idealized.RowLimits.SparseGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis Binomial Binomial.Approximation
variable {n : ℕ}
theorem eventual_parameters_mem_sparse (θ T R : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hR : 0 ≤ R) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ p : Probability, SparseRange θ T N p → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ T →
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
  filter_upwards [eventual_trial_geometry_sparse (n := n) θ T ell hθ hT,
    eventually_size_error_small_sparse θ T 1 ell hθ hT zero_lt_one, hl] with N hgeom hsmall hlog
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
theorem eventual_event_geometry_sparse (θ T R : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hR : 0 ≤ R) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ p : Probability, SparseRange θ T N p → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ T →
      ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
        AdmissibleSizes N p ell T ξ s sizes →
        (∀ t, 0 < sizes t) ∧ ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
          |shift N p sizes| ≤ T ∧ EventGeometry N p sizes s σ T R ell ξ := by
  filter_upwards [eventual_parameters_mem_sparse (n := n) θ T R ell hθ hT hR] with N hN
  refine ⟨hN.1, hN.2.1, ?_⟩
  intro p hp ξ hξ hξT s sizes ha
  have hs := hN.2.2 p hp ξ hξ hξT s sizes ha
  refine ⟨hs.1, ?_⟩
  intro σ hσ
  have hg := hs.2 σ hσ
  have hd := normalized_parameter_distances hN.1 hN.2.1 ha hs.1 hξ hR σ hσ
  refine ⟨hg.1, ?_⟩
  constructor
  · intro b
    cases b with
    | none => simpa only [actualNormalizedParameters_none, eventRows,
        ← rowParameterBox_eq_gaussianBox] using hg.2.1
    | some b => simpa only [actualNormalizedParameters_some, eventRows,
        ← rowParameterBox_eq_gaussianBox] using (hg.2.2.2 b).1
  · intro b
    cases b with
    | none => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using hg.2.2.1
    | some b => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using (hg.2.2.2 b).2.1
  · intro b
    cases b with
    | none => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using hg.2.2.1
    | some b => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using (hg.2.2.2 b).2.2
  · intro b
    cases b with
    | none => simpa only [actualNormalizedParameters_none, targetParameters,
        distanceConstant] using hd.1
    | some b => simpa only [actualNormalizedParameters_some, targetParameters,
        distanceConstant] using hd.2.1 b
  · intro hu b
    cases b with
    | none => simpa only [actualNormalizedParameters_none, targetParameters,
        distanceConstant] using hd.1
    | some b => simpa only [actualNormalizedParameters_some, targetParameters,
        distanceConstant] using hd.2.2 hu b
theorem eventually_error_budget_sparse (θ T c A : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ p : Probability, SparseRange θ T N p →
        A * Real.log (N : ℝ) ^ ell / scale N p ≤ c / 2 ∧
        ∀ ξ : ℝ, ξ ≤ T → error ell N p ξ ≤ T + 1 := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hlog,
    eventually_size_error_small_sparse θ T (min 1 (c / (2 * A))) ell hθ hT (by positivity)]
    with N hl hn
  refine ⟨hn.1, hl, ?_⟩
  intro p hp
  have hsmall := hn.2 p hp
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hn.1
  have hfrac : Real.log (N : ℝ) ^ ell / scale N p < min 1 (c / (2 * A)) := by
    have hinv : (0 : ℝ) ≤ 1 / N := by positivity
    linarith
  have hratio : Real.log (N : ℝ) ^ ell / scale N p < c / (2 * A) :=
    hfrac.trans_le (min_le_right _ _)
  have hunit : Real.log (N : ℝ) ^ ell / scale N p < 1 :=
    hfrac.trans_le (min_le_left _ _)
  constructor
  · have hh := mul_le_mul_of_nonneg_left hratio.le hA.le
    calc
      _ = A * (Real.log (N : ℝ) ^ ell / scale N p) := by ring
      _ ≤ A * (c / (2 * A)) := hh
      _ = c / 2 := by field_simp
  · intro ξ hξ
    unfold error
    change Real.log (N : ℝ) ^ ell / scale N p + ξ ≤ T + 1
    linarith

end MajorityDynamics.Idealized.RowLimits
