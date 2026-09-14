import MajorityDynamics.Idealized.RowLimits.IntegerSizes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Literal real logarithmic exponents, integer size vectors, and real densities.
The ceiling reduction affects only the logarithmic exponent, never the Gaussian
lower bound. Integer sizes become positive uniformly before conversion. -/
noncomputable section
open Set Filter
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial.Approximation
variable {n : ℕ}

structure AdmissibleRealIntegerSizes (N : ℕ) (p ell T ξ : ℝ)
    (s : History (n + 1)) (η : History (n + 1) → ℤ) : Prop where
  close : ∀ t, |(η t : ℝ) - (N : ℝ) * ν n t| ≤
    (N : ℝ) / Real.sqrt (p * N) * Real.log (N : ℝ) ^ ell
  history_balance : ∀ r : Fin n,
    |∑ t, historyMatrix s r t * (η t : ℝ)| ≤ ξ * (N : ℝ) / Real.sqrt (p * N)
  decision_balance : |integerNextImbalance η| ≤ T * (N : ℝ) / Real.sqrt (p * N)

theorem real_log_power_le_ceil (N : ℕ) (ell : ℝ) (hlog : 1 ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) ^ ell ≤ Real.log (N : ℝ) ^ (Nat.ceil ell) := by
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le hlog (Nat.le_ceil ell)

theorem AdmissibleRealIntegerSizes.ceil {N : ℕ} {p : Binomial.Probability}
    {ell T ξ : ℝ} {s : History (n + 1)} {η : History (n + 1) → ℤ}
    (h : AdmissibleRealIntegerSizes N (p : ℝ) ell T ξ s η)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    AdmissibleIntegerSizes N p (Nat.ceil ell) T ξ s η := by
  refine ⟨?_, h.history_balance, h.decision_balance⟩
  intro t
  exact (h.close t).trans (mul_le_mul_of_nonneg_left (real_log_power_le_ceil N ell hlog)
    (div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _)))

/-- The eventual density interval lies in `(0,1)` uniformly in `p`. -/
theorem eventually_real_density_probability (θ T : ℝ) (hθ : 0 < θ) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℝ,
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) → 0 < p ∧ p < 1 := by
  have ht : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-θ)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul T
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop (0 : ℕ)]
    with N hupper hN p hlo hhi
  exact ⟨(mul_pos (inv_pos.mpr hT) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)).trans hlo,
    hhi.trans hupper⟩

/-- Conclusion on the literal integer input, represented in the natural
binomial API only after proving positivity and exact preservation of every
coordinate. In particular no clipping of a negative input is hidden here. -/
def RealIntegerConclusion (N : ℕ) (p : Binomial.Probability) (ell' : ℕ)
    (T R ξ c C : ℝ) (s : History (n + 1)) (η : History (n + 1) → ℤ) : Prop :=
  (∀ t, 0 < η t) ∧ (∀ t, (((η t).toNat : ℕ) : ℝ) = (η t : ℝ)) ∧
  SmoothQuantities N p (fun t => (η t).toNat) s ∧
  ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
    c ≤ gaussianMass σ (historyEvent s) ∧
    (∀ b, c ≤ gaussianMass σ (shiftedChildEvent s b
      ((p : ℝ) * integerNextImbalance η / Real.sqrt ((p : ℝ) * N)))) ∧
    |(p : ℝ) * integerNextImbalance η / Real.sqrt ((p : ℝ) * N)| ≤ T ∧
    Estimates N p (fun t => (η t).toNat) s σ
      ((p : ℝ) * integerNextImbalance η / Real.sqrt ((p : ℝ) * N)) C (error ell' N p ξ) ∧
    (|integerNextImbalance η| ≤ ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N) →
      |(p : ℝ) * integerNextImbalance η / Real.sqrt ((p : ℝ) * N)| ≤ ξ ∧
      ξ ≤ error ell' N p ξ ∧
      (∀ b, c ≤ gaussianMass σ (childEvent s b)) ∧ Estimates N p (fun t => (η t).toNat) s σ 0 C (error ell' N p ξ))

/-- E.3 with arbitrary real `ell ≥ 1`, real density, and integer sizes.
The chosen Gaussian lower bound precedes both `ell` and `θ`. -/
def RowLimitsRealTheorem : Prop :=
  ∀ n : ℕ, ∃ lower : ℝ → ℝ → ℝ,
    ∀ ell : ℝ, 1 ≤ ell → ∃ ell' : ℕ,
    ∀ T R : ℝ, 1 < T → 0 < R → 0 < lower T R ∧
      ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
        ∀ N : ℕ, N₀ ≤ N → ∀ p : ℝ,
          T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
          ∃ hp : 0 < p ∧ p < 1,
            ∀ ξ : ℝ, 0 < ξ → ξ ≤ T → ∀ (s : History (n + 1)) (η : History (n + 1) → ℤ),
              AdmissibleRealIntegerSizes N p ell T ξ s η →
                RealIntegerConclusion N ⟨p, hp⟩ ell' T R ξ (lower T R) C s η

theorem rowLimitsReal_of_rowLimits (h : RowLimitsTheorem) : RowLimitsRealTheorem := by
  intro n
  obtain ⟨lower, hlower⟩ := h n
  refine ⟨lower, ?_⟩
  intro ell hell
  have hceil : 1 ≤ Nat.ceil ell := Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one hell)
  obtain ⟨ell', hmain⟩ := hlower (Nat.ceil ell) hceil
  refine ⟨ell', ?_⟩
  intro T R hT hR
  obtain ⟨hlow, hmain⟩ := hmain T R hT hR
  refine ⟨hlow, ?_⟩
  intro θ hθ hθ'
  obtain ⟨C, hC, N₀, hmain⟩ := hmain θ hθ hθ'
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hpos := eventually_integer_sizes_positive (n := n) θ T (Nat.ceil ell) hθ' (by linarith)
  have hp := eventually_real_density_probability θ T (by linarith) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((hlog.and hpos).and hp)
  refine ⟨C, hC, max N₀ N₁, ?_⟩
  intro N hN p hp₀ hp₁
  have hNN₀ := (le_max_left N₀ N₁).trans hN
  have hNN₁ := (le_max_right N₀ N₁).trans hN
  obtain ⟨⟨hlog, hpos⟩, hp⟩ := hN₁ N hNN₁
  have hp' := hp p hp₀ hp₁
  refine ⟨hp', ?_⟩
  intro ξ hξ hξT s η ha
  let q : Binomial.Probability := ⟨p, hp'⟩
  have hη := ha.ceil (p := q) hlog
  have hpositive : ∀ t, 0 < η t := hpos q ⟨hp₀, hp₁⟩ η hη.close
  have hnonneg : ∀ t, 0 ≤ η t := fun t => (hpositive t).le
  have hnat := hη.toNat hnonneg
  obtain ⟨hsmooth, hresult⟩ := hmain N hNN₀ q hp₀ hp₁ ξ hξ hξT s
    (fun t => (η t).toNat) hnat
  refine ⟨hpositive, ?_, hsmooth, ?_⟩
  · intro t
    exact_mod_cast Int.toNat_of_nonneg (hnonneg t)
  · intro σ hσ
    have hout := hresult σ hσ
    simpa only [shift, integerNextImbalance_toNat η hnonneg] using hout

end MajorityDynamics.Idealized.RowLimits
