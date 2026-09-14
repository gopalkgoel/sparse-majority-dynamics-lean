import MajorityDynamics.Analysis.FiniteTiltEstimate
import MajorityDynamics.Binomial.TiltUniqueness

/-!
# Exact finite binomial reweighting and quantitative expansion

This handles a fixed trial vector on any common finite conditioning/truncation
set. The full A.2 theorem allows different trial vectors and needs additional
point-probability and tail bounds; it is not asserted here.
-/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Binomial
open Analysis.FiniteTiltEstimate

variable {ι : Type*} [Fintype ι]

def centeredLogTilt (η : ι → ℕ) (q₀ q₁ : ι → Probability) (c : ι → ℝ)
    (a : Box η) : ℝ :=
  ∑ i, (logOdds (q₁ i) - logOdds (q₀ i)) * (vector a i - c i)

/-- On a fixed trial box, changing the success probabilities is exactly an
exponential tilt. The center is arbitrary and cancels in normalization. -/
theorem expectation_reweight (η : ι → ℕ) (q₀ q₁ : ι → Probability)
    (c : ι → ℝ) (S : Finset (Box η)) (hS : S.Nonempty) (f : Box η → ℝ) :
    expectation η q₁ S f =
      expectation η q₀ S (fun a => Real.exp (centeredLogTilt η q₀ q₁ c a) * f a) /
        expectation η q₀ S (fun a => Real.exp (centeredLogTilt η q₀ q₁ c a)) := by
  let C := (∑ i, (η i : ℝ) *
    (Real.log (1 - (q₁ i : ℝ)) - Real.log (1 - (q₀ i : ℝ)))) -
    Real.log (eventMass η q₁ S) + Real.log (eventMass η q₀ S) +
    ∑ i, (logOdds (q₁ i) - logOdds (q₀ i)) * c i
  have hlog (a : Box η) :
      Real.log (conditionalWeight η q₁ S a) - Real.log (conditionalWeight η q₀ S a) =
        C + centeredLogTilt η q₀ q₁ c a := by
    rw [conditionalWeight, conditionalWeight,
      Real.log_div (mass_pos η q₁ a).ne' (eventMass_pos η q₁ hS).ne',
      Real.log_div (mass_pos η q₀ a).ne' (eventMass_pos η q₀ hS).ne', log_mass, log_mass]
    dsimp [C, centeredLogTilt]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, sub_mul]
    simp_rw [mul_comm (vector a _) (logOdds _)]
    ring
  have hweight (a : Box η) : conditionalWeight η q₁ S a = Real.exp C *
      (conditionalWeight η q₀ S a * Real.exp (centeredLogTilt η q₀ q₁ c a)) := by
    have he := congrArg Real.exp (hlog a)
    rw [Real.exp_sub, Real.exp_log (conditionalWeight_pos η q₁ hS a),
      Real.exp_log (conditionalWeight_pos η q₀ hS a), Real.exp_add] at he
    have he' := (div_eq_iff (conditionalWeight_pos η q₀ hS a).ne').mp he
    calc
      _ = _ := he'
      _ = _ := by ring
  exact reweighted_average S (conditionalWeight η q₀ S) (conditionalWeight η q₁ S)
    (centeredLogTilt η q₀ q₁ c) f (Real.exp C)
    (sum_conditionalWeight η q₁ hS) (fun a _ => hweight a)

/-- A fully proved quantitative binomial expansion on any common finite set.
The first-order term is the covariance with the centered log-odds increment. -/
theorem finite_tilt_expansion (η : ι → ℕ) (q₀ q₁ : ι → Probability)
    (c : ι → ℝ) (S : Finset (Box η)) (hS : S.Nonempty) (f : Box η → ℝ)
    (H b : ℝ) (hH : 0 ≤ H) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 4)
    (hf : ∀ a ∈ S, |f a| ≤ H)
    (hz : ∀ a ∈ S, |centeredLogTilt η q₀ q₁ c a| ≤ b) :
    |expectation η q₁ S f -
      (expectation η q₀ S f +
        expectation η q₀ S (fun a => centeredLogTilt η q₀ q₁ c a * f a) -
        expectation η q₀ S (centeredLogTilt η q₀ q₁ c) * expectation η q₀ S f)| ≤
      12 * H * b ^ 2 := by
  rw [expectation_reweight η q₀ q₁ c S hS f]
  exact exponential_remainder S (conditionalWeight η q₀ S) f (centeredLogTilt η q₀ q₁ c)
    (fun a _ => (conditionalWeight_pos η q₀ hS a).le) (sum_conditionalWeight η q₀ hS)
    H b hH hb hbsmall hf hz

end MajorityDynamics.Binomial
