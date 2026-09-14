import MajorityDynamics.Idealized.RowLimits.Basic
import MajorityDynamics.Idealized.RowLimits.Geometry

/-! Uniform error-budget bookkeeping for the E.3 endpoint. In particular the
small error used for denominator positivity excludes the bounded parameter ξ. -/

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.RowLimits
open Binomial Binomial.Approximation

theorem error_nonneg {ell N : ℕ} {p : Probability} {ξ : ℝ}
    (hN : 1 ≤ N) (hξ : 0 ≤ ξ) : 0 ≤ error ell N p ξ := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_nonneg hn
  unfold error
  positivity

theorem error_ge_xi {ell N : ℕ} {p : Probability} {ξ : ℝ}
    (hN : 1 ≤ N) : ξ ≤ error ell N p ξ := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_nonneg hn
  unfold error
  exact le_add_of_nonneg_left (by positivity)

theorem error_mono_exponent {a b N : ℕ} {p : Probability} {ξ : ℝ}
    (hab : a ≤ b) (hlog : 1 ≤ Real.log (N : ℝ)) :
    error a N p ξ ≤ error b N p ξ := by
  unfold error
  exact add_le_add
    (div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog hab) (Real.sqrt_nonneg _)) le_rfl

theorem diagonal_error_le {ell N : ℕ} {p : Probability} {ξ : ℝ}
    (hlog : 1 ≤ Real.log (N : ℝ)) (hξ : 0 ≤ ξ) :
    (p : ℝ) / scale N p ≤ error ell N p ξ := by
  have hlpow : 1 ≤ Real.log (N : ℝ) ^ ell := one_le_pow₀ hlog
  calc
    _ ≤ Real.log (N : ℝ) ^ ell / scale N p :=
      div_le_div_of_nonneg_right (p.property.2.le.trans hlpow) (Real.sqrt_nonneg _)
    _ ≤ _ := le_add_of_nonneg_right hξ

theorem eventually_error_budget (θ T c A : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ p : Probability, Density θ T N p →
        A * Real.log (N : ℝ) ^ ell / scale N p ≤ c / 2 ∧
        ∀ ξ : ℝ, ξ ≤ T → error ell N p ξ ≤ T + 1 := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hlog,
    eventually_size_error_small θ T (min 1 (c / (2 * A))) ell hθ hT (by positivity)]
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
