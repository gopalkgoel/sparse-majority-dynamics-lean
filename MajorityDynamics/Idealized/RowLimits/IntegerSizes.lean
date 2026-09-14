import MajorityDynamics.Idealized.RowLimits.Basic
import MajorityDynamics.Idealized.RowLimits.Geometry

/-! The paper allows integer size vectors. Its hypotheses force positive sizes
uniformly for large `N`, so conversion to the natural-size row model is exact. -/

noncomputable section
open Set Filter
open scoped BigOperators

namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial.Approximation
variable {n : ℕ}

def integerSizeVector (η : History (n + 1) → ℤ) : Row (n + 1) :=
  WithLp.toLp 2 (fun t => (η t : ℝ))

def integerNextImbalance (η : History (n + 1) → ℤ) : ℝ :=
  imbalance (Fin.last n) (integerSizeVector η)

structure AdmissibleIntegerSizes (N : ℕ) (p : Binomial.Probability) (ell : ℕ)
    (T ξ : ℝ) (s : History (n + 1)) (η : History (n + 1) → ℤ) : Prop where
  close : ∀ t, |(η t : ℝ) - (N : ℝ) * ν n t| ≤
    (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ ell
  history_balance : ∀ r : Fin n,
    |∑ t, historyMatrix s r t * (η t : ℝ)| ≤
      ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N)
  decision_balance : |integerNextImbalance η| ≤
    T * (N : ℝ) / Real.sqrt ((p : ℝ) * N)

theorem integerSizeVector_toNat (η : History (n + 1) → ℤ) (hη : ∀ t, 0 ≤ η t) :
    sizeVector (fun t => (η t).toNat) = integerSizeVector η := by
  ext t
  change ((η t).toNat : ℝ) = (η t : ℝ)
  exact_mod_cast Int.toNat_of_nonneg (hη t)

theorem integerNextImbalance_toNat (η : History (n + 1) → ℤ) (hη : ∀ t, 0 ≤ η t) :
    nextImbalance (fun t => (η t).toNat) = integerNextImbalance η := by
  rw [nextImbalance, integerSizeVector_toNat η hη]
  rfl

theorem AdmissibleIntegerSizes.toNat {N : ℕ} {p : Binomial.Probability} {ell : ℕ}
    {T ξ : ℝ} {s : History (n + 1)} {η : History (n + 1) → ℤ}
    (h : AdmissibleIntegerSizes N p ell T ξ s η) (hη : ∀ t, 0 ≤ η t) :
    AdmissibleSizes N p ell T ξ s (fun t => (η t).toNat) := by
  have hc : ∀ t, ((η t).toNat : ℝ) = (η t : ℝ) := by
    intro t
    exact_mod_cast Int.toNat_of_nonneg (hη t)
  constructor
  · intro t
    simpa only [hc] using h.close t
  · intro r
    simpa only [hc] using h.history_balance r
  · simpa only [integerNextImbalance_toNat η hη] using h.decision_balance

theorem eventually_integer_sizes_positive (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ (p : Binomial.Probability), Density θ T N p →
      ∀ η : History (n + 1) → ℤ,
        (∀ t, |(η t : ℝ) - (N : ℝ) * ν n t| ≤
          (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ ell) →
        ∀ t, 0 < η t := by
  have he : ∀ᶠ N : ℕ in atTop, ∀ t : History (n + 1), 0 < N ∧
      ∀ p : Binomial.Probability, Density θ T N p →
        Real.log (N : ℝ) ^ ell / scale N p + 1 / N < ν n t :=
    Filter.eventually_all.mpr fun t =>
      eventually_size_error_small θ T (ν n t) ell hθ hT (ν_positive n t)
  filter_upwards [he] with N hN p hp η hη t
  have hn : 0 < (N : ℝ) := by exact_mod_cast (hN t).1
  have hb := (hN t).2 p hp
  have hb' : Real.log (N : ℝ) ^ ell / scale N p < ν n t := by
    have : 0 ≤ (1 : ℝ) / N := by positivity
    linarith
  have he' := mul_lt_mul_of_pos_left hb' hn
  have hrad : (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ ell <
      (N : ℝ) * ν n t := by
    calc
      _ = (N : ℝ) * (Real.log (N : ℝ) ^ ell / scale N p) := by
        unfold scale
        ring
      _ < _ := he'
  have hh := (abs_le.mp (hη t)).1
  have : (0 : ℝ) < (η t : ℝ) := by linarith
  exact_mod_cast this

end MajorityDynamics.Idealized.RowLimits
