import MajorityDynamics.Idealized.LinearResponse.Moments

/-! Identification of the E.3 binomial quantities at a solved row tilt with the
finite centered moments of `Moments.lean`, and finite bounds for the universal
Gaussian functionals. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal
open MajorityDynamics.Binomial (mass eventMass vector)
open MajorityDynamics.Idealized.RowLimits

variable {n : ℕ}

theorem binomialMass_eq (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (q : History (n + 1) → Binomial.Probability)
    (htilt : rowTilt N p σ = q) (S : Finset (Binomial.Box (Local.trials sizes s))) :
    binomialMass N p sizes s S σ = eventMass (Local.trials sizes s) q S := by
  unfold binomialMass
  rw [htilt]

theorem binomialSplit_eq (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (q : History (n + 1) → Binomial.Probability)
    (htilt : rowTilt N p σ = q) (b : Bool) :
    binomialSplit N p sizes s b σ = splitProbability sizes s b q := by
  unfold binomialSplit binomialMass splitProbability childMass historyMass
  rw [htilt]

theorem binomialMean_eq (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (q : History (n + 1) → Binomial.Probability)
    (htilt : rowTilt N p σ = q) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (c : History (n + 1) → ℝ) (t : History (n + 1))
    (hE : eventMass (Local.trials sizes s) q S ≠ 0) :
    binomialMean N p sizes s S t σ =
      cfirst (Local.trials sizes s) q S c t / eventMass (Local.trials sizes s) q S + c t := by
  rw [binomialMean_eq_conditionalMean, htilt, conditionalMean_eq_cfirst _ _ _ c t hE]

theorem binomialCovariance_eq (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (q : History (n + 1) → Binomial.Probability)
    (htilt : rowTilt N p σ = q) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (c : History (n + 1) → ℝ) (t t' : History (n + 1))
    (hE : eventMass (Local.trials sizes s) q S ≠ 0) :
    binomialCovariance N p sizes s S t t' σ =
      csecond (Local.trials sizes s) q S c t t' / eventMass (Local.trials sizes s) q S -
        (cfirst (Local.trials sizes s) q S c t / eventMass (Local.trials sizes s) q S) *
          (cfirst (Local.trials sizes s) q S c t' / eventMass (Local.trials sizes s) q S) := by
  rw [← covariance_eq_csecond _ _ _ c t t' hE]
  unfold binomialCovariance binomialSecond binomialMean binomialFirst binomialMass
  rw [htilt, conditionalMean_eq_div, conditionalMean_eq_div]

/-- The finite conditional quantities of the actual law are the paper's
conditional means: `historyMean` is the first moment over the mass. -/
theorem historyMean_eq_cfirst (sizes : Local.Sizes n) (s : History (n + 1))
    (q : History (n + 1) → Binomial.Probability) (c : History (n + 1) → ℝ) (t : History (n + 1))
    (hE : historyMass sizes s q ≠ 0) :
    historyMean sizes s q t =
      cfirst (Local.trials sizes s) q (Local.historySupport sizes s) c t / historyMass sizes s q +
        c t :=
  conditionalMean_eq_cfirst _ _ _ c t hE

theorem childMean_eq_cfirst (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (q : History (n + 1) → Binomial.Probability) (c : History (n + 1) → ℝ) (t : History (n + 1))
    (hE : childMass sizes s b q ≠ 0) :
    childMean sizes s b q t =
      cfirst (Local.trials sizes s) q (Local.childSupport sizes s b) c t / childMass sizes s b q +
        c t :=
  conditionalMean_eq_cfirst _ _ _ c t hE

/-- A finite family of reals is bounded. -/
theorem finite_abs_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i, |f i| ≤ B := by
  refine ⟨∑ i, |f i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  intro i
  exact Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (f j)) (Finset.mem_univ i)

/-- One bound for all universal Gaussian means and covariances. -/
theorem universal_bounds (n : ℕ) :
    ∃ G₀ : ℝ, 0 ≤ G₀ ∧
      (∀ (s t : History (n + 1)), |∫ x, x t ∂historyLaw n s| ≤ G₀) ∧
      (∀ (s : History (n + 1)) (b : Bool) (t : History (n + 1)),
        |∫ x, x t ∂childLaw n s b| ≤ G₀) ∧
      (∀ (s t t' : History (n + 1)), |conditionalCovariance n s t t'| ≤ G₀) := by
  obtain ⟨B₁, hB₁, h₁⟩ := finite_abs_bound
    (fun st : History (n + 1) × History (n + 1) => ∫ x, x st.2 ∂historyLaw n st.1)
  obtain ⟨B₂, hB₂, h₂⟩ := finite_abs_bound
    (fun sbt : History (n + 1) × Bool × History (n + 1) =>
      ∫ x, x sbt.2.2 ∂childLaw n sbt.1 sbt.2.1)
  obtain ⟨B₃, hB₃, h₃⟩ := finite_abs_bound
    (fun stt : History (n + 1) × History (n + 1) × History (n + 1) =>
      conditionalCovariance n stt.1 stt.2.1 stt.2.2)
  refine ⟨B₁ + B₂ + B₃, add_nonneg (add_nonneg hB₁ hB₂) hB₃, ?_, ?_, ?_⟩
  · intro s t
    exact (h₁ (s, t)).trans (by linarith)
  · intro s b t
    exact (h₂ (s, b, t)).trans (by linarith)
  · intro s t t'
    exact (h₃ (s, t, t')).trans (by linarith)

end MajorityDynamics.Idealized.LinearResponse
