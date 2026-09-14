import MajorityDynamics.Idealized.RowLimits.Approximation

/-! A.2 applied to all actual history and child row events. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation Analysis.ConditionalGaussian
variable {n : ℕ}

def eventRows (n : ℕ) : Option Bool → ℕ
  | none => n
  | some _ => n + 1

def eventIntegerMatrix (s : History (n + 1)) :
    (b : Option Bool) → Fin (eventRows n b) → History (n + 1) → ℤ
  | none => historyIntegerMatrix s
  | some b => childIntegerMatrix s b

def eventStrict (s : History (n + 1)) : (b : Option Bool) → Fin (eventRows n b) → Bool
  | none => historyStrict s
  | some b => childStrict s b

def eventSupport (sizes : Local.Sizes n) (s : History (n + 1)) :
    Option Bool → Finset (Binomial.Box (Local.trials sizes s))
  | none => Local.historySupport sizes s
  | some b => Local.childSupport sizes s b

def eventMatrix (s : History (n + 1)) (b : Option Bool) :
    Matrix (Fin (eventRows n b)) (History (n + 1)) ℝ :=
  fun j t => (eventIntegerMatrix s b j t : ℝ)

def actualNormalizedParameters (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (b : Option Bool) :
    Analysis.GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) (eventRows n b) :=
  ((WithLp.toLp 2 (normalizedMean N sizes s σ),
    WithLp.toLp 2 (normalizedVariance N sizes s)),
    normalizedThreshold N p sizes s (eventMatrix s b))

def actualGaussianMoment (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (b : Option Bool)
    (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) : ℝ :=
  ∫ x in Analysis.GaussianRegularity.event (eventMatrix s b)
      (actualNormalizedParameters N p sizes s σ b).2,
    momentValue o x.ofLp ∂Analysis.GaussianRegularity.law
      (actualNormalizedParameters N p sizes s σ b)

theorem eventIntegerMatrix_orthogonal (s : History (n + 1)) (b : Option Bool) :
    OrthogonalRows (eventIntegerMatrix s b) := by
  cases b with
  | none => exact historyIntegerMatrix_orthogonal s
  | some b => exact childIntegerMatrix_orthogonal s b

/-- Finite formulas are the actual normalized event integrals. -/
theorem eventSupport_normalized_integral (N : ℕ) (p : Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (b : Option Bool)
    (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) (σ : Row (n + 1)) :
    binomialNormalizedMoment N p sizes s (eventSupport sizes s b)
      (fun t => (p : ℝ) * Local.trials sizes s t) (scale N p) o σ =
    ∫ a in inequalityEvent (eventMatrix s b) (eventStrict s b),
      momentValue o (fun t => centered p (Local.trials sizes s) a t / scale N p)
        ∂Binomial.law (Local.trials sizes s) (rowTilt N p σ) := by
  cases b with
  | none => exact binomialNormalizedMoment_history_integral N p sizes s _ _ o σ
  | some b => exact binomialNormalizedMoment_child_integral N p sizes s b _ _ o σ

/-- Uniform normalized raw moments for every actual row and each child.
All A.2 geometric hypotheses are discharged from the paper's size assumptions.
The error tends to zero independently of the history imbalance parameter ξ. -/
theorem row_normalized_comparison (θ T R : ℝ) (ell : ℕ)
    (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Probability, Density θ T N p →
      ∀ ξ : ℝ, ξ ≤ T → ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
      AdmissibleSizes N p ell T ξ s sizes →
      ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
      ∀ b : Option Bool, ∀ o : MomentKind (Fintype.card (Fin (n + 1) → Bool)),
      |binomialNormalizedMoment N p sizes s (eventSupport sizes s b)
          (fun t => (p : ℝ) * Local.trials sizes s t) (scale N p) o σ -
        actualGaussianMoment N p sizes s σ b o| ≤
        C * Real.log N ^ (5 + Fintype.card (Fin (n + 1) → Bool)) / scale N p := by
  classical
  let K := geometryConstant n T R
  have hT0 : 0 < T := zero_lt_one.trans hT
  obtain ⟨hK, hgeom⟩ := eventual_row_geometry (n := n) θ T R ell hθ' hT0 hR
  obtain ⟨C, hC, N₁, hN₁, hA⟩ := normalized_gaussian_comparison_finite
    (ι := History (n + 1) × Option Bool) θ K hθ hθ' hK
    (Fintype.card (Fin (n + 1) → Bool)) Fintype.card_pos
    (fun j => eventRows n j.2) (fun j => eventIntegerMatrix j.1 j.2)
    (fun j => eventIntegerMatrix_orthogonal j.1 j.2) (fun j => eventStrict j.1 j.2)
  have hevent : ∀ᶠ N : ℕ in atTop, N₁ ≤ N ∧ 1 ≤ N ∧
      1 ≤ Real.log (N : ℝ) ∧
      (0 < N ∧ ∀ p : Probability, Density θ T N p →
        Density θ K N p ∧ ∀ ξ : ℝ, ∀ s : History (n + 1),
          ∀ sizes : Local.Sizes n, AdmissibleSizes N p ell T ξ s sizes →
          ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) → ∀ t,
          0 < Local.trials sizes s t ∧ K⁻¹ * N < (Local.trials sizes s t : ℝ) ∧
          (Local.trials sizes s t : ℝ) < K * N ∧ |alpha N sizes s σ t| < K ∧
          logistic (logOdds p + alpha N sizes s σ t /
            Real.sqrt ((p : ℝ) * Local.trials sizes s t)) = rowTilt N p σ t) := by
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop (1 : ℕ),
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1,
      hgeom] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨C, hC, max 1 N₀, le_max_left _ _, ?_⟩
  intro N hN p hp ξ hξ s sizes had σ hσ b o
  obtain ⟨hN1, hn1, hlog, hn, hg⟩ := hN₀ N ((le_max_right _ _).trans hN)
  obtain ⟨hden, ht⟩ := hg p hp
  have ht' := ht ξ s sizes had σ hσ
  have hsz : ∀ t, 0 < sizes t := by
    intro t
    have hh := (ht' t).1
    dsimp [Local.trials] at hh
    omega
  have hs : Real.sqrt ((p : ℝ) * N) ≤ N := by
    apply (Real.sqrt_le_left (Nat.cast_nonneg N)).mpr
    have hnreal : (1 : ℝ) ≤ N := by exact_mod_cast hn1
    have hh := mul_le_mul_of_nonneg_right p.property.2.le (Nat.cast_nonneg N)
    nlinarith
  have hbal : ∀ j, |∑ t, (eventIntegerMatrix s b j t : ℝ) *
      Local.trials sizes s t| < K * N / scale N p := by
    cases b with
    | none =>
      simpa only [eventIntegerMatrix, historyIntegerMatrix_cast, scale, eventRows, K] using
        matrix_trial_history_balance hn had hsz hT
          (geometryConstant_two_mul_lt T R hT0) hξ hs
    | some b =>
      exact matrix_trial_child_balance hn had hsz hT
        (geometryConstant_two_mul_lt T R hT0) hξ hs b
  have h := hA N hN1 p hden (Local.trials sizes s)
    (fun t => ⟨(ht' t).2.1, (ht' t).2.2.1⟩) σ.ofLp (ν n)
    (fun t => (ht' t).2.2.2.1) (s, b) hbal o
  have heq : gaussianTilt p (Local.trials sizes s)
      (fun t => σ t / ν n t * Real.sqrt ((Local.trials sizes s t : ℝ) / N)) =
      rowTilt N p σ := by
    funext t
    exact (ht' t).2.2.2.2
  rw [heq] at h
  rw [eventSupport_normalized_integral]
  have hm : (∫ x in Analysis.GaussianRegularity.event
      (fun j t => (eventIntegerMatrix s b j t : ℝ))
      (WithLp.toLp 2 (fun j => (p : ℝ) *
        (∑ t, (eventIntegerMatrix s b j t : ℝ) * Local.trials sizes s t) / scale N p)),
      momentValue o x.ofLp ∂Analysis.ConditionalGaussian.gaussianLaw
      (Matrix.diagonal (fun t => (Local.trials sizes s t : ℝ) / N))
      (WithLp.toLp 2 (fun t => σ t * Local.trials sizes s t / ((N : ℝ) * ν n t)))) =
      actualGaussianMoment N p sizes s σ b o := rfl
  change _ ≤ _ at h
  rw [hm] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_right₀ hlog (by have hh := moment_degree_le_two o; omega)

end MajorityDynamics.Idealized.RowLimits
