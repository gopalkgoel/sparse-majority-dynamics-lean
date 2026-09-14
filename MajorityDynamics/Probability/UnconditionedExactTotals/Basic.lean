import MajorityDynamics.Binomial.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # The unconditioned case of `thm:fourier_BE` (B.5)

The sample records each Bernoulli trial, with coordinate, copy, and trial
indices. Counts within a copy give the binomial vector, and summing copies
gives the integer-valued random vector. Clipping only makes the real-parameter
law total; the public theorem proves all its probabilities are in `(0,1)`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.UnconditionedExactTotals

def probability (q : ℝ) : unitInterval :=
  ⟨max 0 (min 1 q), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem probability_eq {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) : (probability q : ℝ) = q := by
  simp [probability, min_eq_right hq.2, max_eq_right hq.1]

def count {ι : Type*} [Fintype ι] (x : ι → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

def bitsLaw (ι : Type*) [Fintype ι] (q : unitInterval) : Measure (ι → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false q)

instance (ι : Type*) [Fintype ι] (q : unitInterval) : IsProbabilityMeasure (bitsLaw ι q) := by
  unfold bitsLaw; infer_instance

abbrev TrialArray {d : ℕ} (m : ℕ) (η : Fin d → ℕ) :=
  (t : Fin d) → Fin m → Fin (η t) → Bool

def trialLaw {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) : Measure (TrialArray m η) :=
  Measure.pi (fun t => Measure.pi (fun _ : Fin m => bitsLaw (Fin (η t)) (probability (q t))))

instance {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) :
    IsProbabilityMeasure (trialLaw m η q) := by unfold trialLaw; infer_instance

def copies {d m : ℕ} {η : Fin d → ℕ} (x : TrialArray m η) : Fin m → Fin d → ℕ :=
  fun i t => count (x t i)

def total {d m : ℕ} {η : Fin d → ℕ} (x : TrialArray m η) : Fin d → ℕ :=
  fun t => ∑ i, copies x i t

def sumLaw {d : ℕ} (m : ℕ) (η : Fin d → ℕ) (q : Fin d → ℝ) : Measure (Fin d → ℤ) :=
  (trialLaw m η q).map (fun x t => (total x t : ℤ))

def DensityWindow (θ T : ℝ) (n : ℕ) (p : ℝ) : Prop :=
  T⁻¹ * (n : ℝ) ^ (-θ) < p ∧ p < T * (n : ℝ) ^ (-θ)

def SizeWindow (T : ℝ) (n : ℕ) (a : ℤ) : Prop :=
  T⁻¹ * n < (a : ℝ) ∧ (a : ℝ) < T * n

def TiltWindow (T : ℝ) (n : ℕ) (p q : ℝ) : Prop :=
  p - T * p / Real.sqrt (p * n) < q ∧ q < p + T * p / Real.sqrt (p * n)

/-- Literal integer inputs; every conversion and central-atom interior bound
is a conclusion. The constants precede all varying parameters. -/
def UnconditionedExactTotalsTheorem : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ d : ℕ, 1 ≤ d → ∀ T : ℝ, 1 < T →
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ η : Fin d → ℤ, (∀ t, SizeWindow T n (η t)) →
      ∀ m : ℤ, SizeWindow T n m → ∀ q : Fin d → ℝ,
      (∀ t, TiltWindow T n p (q t)) → ∀ z : Fin d → ℤ,
      (∀ t, (z t : ℝ) = (m : ℝ) * (η t : ℝ) * q t) →
      0 < p ∧ p < 1 ∧ 1 ≤ m ∧ (m.toNat : ℤ) = m ∧
      (∀ t, 0 < q t ∧ q t < 1 ∧ 1 ≤ η t ∧ ((η t).toNat : ℤ) = η t ∧
        0 < z t ∧ z t < m * η t ∧ ((z t).toNat : ℤ) = z t) ∧
      c * ((n : ℝ) ^ 2 * p) ^ (-(d : ℝ) / 2) ≤
        (sumLaw m.toNat (fun t => (η t).toNat) q).real {z}

end MajorityDynamics.Probability.UnconditionedExactTotals
