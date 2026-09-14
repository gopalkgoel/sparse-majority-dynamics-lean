import MajorityDynamics.Binomial.ApproximationStatements
import Mathlib.Tactic.Linarith

/-! # Original tie events can change inside a unit cell only near a boundary -/

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation

private theorem sign_stable (u v R : ℝ) (strict : Bool)
    (hd : |u - v| ≤ R) (hv : R < |v|) :
    (if strict then 0 < u else 0 ≤ u) ↔ 0 ≤ v := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hd
  rcases le_or_gt 0 v with hv0 | hv0
  · rw [abs_of_nonneg hv0] at hv
    have hu : 0 < u := by have h := (abs_le.mp hd).1; linarith
    cases strict <;> simp [hu, hu.le, hv0]
  · rw [abs_of_neg hv0] at hv
    have hu : u < 0 := by have h := (abs_le.mp hd).2; linarith
    cases strict <;> simp [hu.not_ge, hu.not_gt, hv0.not_ge]

/-- Even a strict lattice boundary versus a weak Gaussian boundary has the
same event membership away from the explicitly sized boundary strips. -/
theorem inequality_event_stable {r d : ℕ} (M : Fin r → Fin d → ℤ)
    (strict : Fin r → Bool) (p : Probability) (η a : Fin d → ℕ) (x : Fin d → ℝ)
    (hcell : ∀ i, |centered p η a i - x i| ≤ 1)
    (haway : ∀ j, (∑ i, |(M j i : ℝ)|) <
      |(∑ i, (M j i : ℝ) * x i) + (p : ℝ) * (∑ i, (M j i : ℝ) * η i)|) :
    a ∈ inequalityEvent (fun j i => (M j i : ℝ)) strict ↔ x ∈ gaussianEvent M p η := by
  change (∀ j, if strict j then 0 < ∑ i, (M j i : ℝ) * a i else 0 ≤ ∑ i, (M j i : ℝ) * a i) ↔ _
  unfold gaussianEvent
  simp only [Set.mem_ofPred_eq]
  apply forall_congr'
  intro j
  have heq : (∑ i, (M j i : ℝ) * a i) -
      ((∑ i, (M j i : ℝ) * x i) + (p : ℝ) * (∑ i, (M j i : ℝ) * η i)) =
        ∑ i, (M j i : ℝ) * (centered p η a i - x i) := by
    simp only [centered, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd : |(∑ i, (M j i : ℝ) * a i) -
      ((∑ i, (M j i : ℝ) * x i) + (p : ℝ) * (∑ i, (M j i : ℝ) * η i))| ≤ ∑ i, |(M j i : ℝ)| := by
    rw [heq]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcell i) (abs_nonneg (M j i : ℝ))
  exact (sign_stable _ _ _ (strict j) hd (haway j)).trans (by constructor <;> intro h <;> linarith)

/-- All possible lattice/Gaussian tie disagreements lie in a finite union
of boundary strips; no orthogonality assumption is needed for this inclusion. -/
theorem inequality_event_mismatch {r d : ℕ} (M : Fin r → Fin d → ℤ)
    (strict : Fin r → Bool) (p : Probability) (η a : Fin d → ℕ) (x : Fin d → ℝ)
    (hcell : ∀ i, |centered p η a i - x i| ≤ 1)
    (hne : ¬ (a ∈ inequalityEvent (fun j i => (M j i : ℝ)) strict ↔ x ∈ gaussianEvent M p η)) :
    ∃ j, |(∑ i, (M j i : ℝ) * x i) + (p : ℝ) * (∑ i, (M j i : ℝ) * η i)| ≤
      ∑ i, |(M j i : ℝ)| := by
  classical
  by_contra h
  push Not at h
  exact hne (inequality_event_stable M strict p η a x hcell h)

end MajorityDynamics.Binomial.Approximation
