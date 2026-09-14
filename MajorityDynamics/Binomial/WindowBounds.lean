import MajorityDynamics.Binomial.TrialGeometry
import MajorityDynamics.Binomial.TiltedWindow

/-! # Explicit support, likelihood, and tail bounds for the common window -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation
variable {d : ℕ}

theorem likelihoodErrorBound_le (old new : Fin d → ℕ) (center : Fin d → ℝ)
    (T n p s l : ℝ) (hT : 0 < T) (hn : 0 < n) (hscale : s ^ 2 = p * n)
    (h₀ : ∀ i, n / (4 * T) ≤ (old i : ℝ) - center i)
    (h₁ : ∀ i, n / (4 * T) ≤ (new i : ℝ) - center i) :
    likelihoodErrorBound old new center (fun _ => s * l) ≤ 32 * d * T * p * l ^ 2 := by
  have hden : 0 < n / (4 * T) := by positivity
  have hinv (m c : ℝ) (h : n / (4 * T) ≤ m - c) : 1 / (m - c) ≤ 4 * T / n := by
    have hh := one_div_le_one_div_of_le hden h
    simpa only [one_div_div, div_one] using hh
  calc
    _ ≤ ∑ _i : Fin d, 4 * (s * l) ^ 2 * (4 * T / n + 4 * T / n) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (add_le_add (hinv _ _ (h₀ i)) (hinv _ _ (h₁ i))) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, hscale]; field_simp; ring

theorem rectangle_tail_of_trial_geometry (η : Fin d → ℕ) (q : Fin d → Probability)
    (center : Fin d → ℝ) (T s l : ℝ) (hT : 0 < T) (hs : 0 < s)
    (hl : 6 * T ^ 2 ≤ l) (hls : l ≤ s) (hη : ∀ i, 0 < η i)
    (hshift : ∀ i, |(η i : ℝ) * (q i : ℝ) - center i| ≤ 3 * T ^ 2 * s)
    (hmean : ∀ i, (η i : ℝ) * (q i : ℝ) ≤ 4 * T * s ^ 2) :
    (law η q).real (rectangle center (fun _ => s * l))ᶜ ≤
      2 * d * Real.exp (-(l ^ 2) / (32 * T + 4)) := by
  have hl0 : 0 ≤ l := (by positivity : 0 ≤ 6 * T ^ 2).trans hl
  have htail := rectangle_tail_le η q center (fun _ => s * l)
    (fun _ => 2 * Real.exp (-(l ^ 2) / (32 * T + 4))) (fun i => by
      have hcenter : |(η i : ℝ) * (q i : ℝ) - center i| ≤ s * l / 2 := by
        have h := mul_le_mul_of_nonneg_left hl hs.le
        nlinarith [hshift i]
      simpa only [show 8 * (4 * T) + 4 = 32 * T + 4 by ring] using
        centered_tail_scaled (η i) (q i) (hη i) (center i) s l (4 * T) hs hl0
          (by positivity) hcenter (hmean i) hls)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (d : ℝ) * (2 * Real.exp (-(l ^ 2) / (32 * T + 4))) =
      2 * d * Real.exp (-(l ^ 2) / (32 * T + 4)) by ring] using htail

end MajorityDynamics.Binomial.Approximation
