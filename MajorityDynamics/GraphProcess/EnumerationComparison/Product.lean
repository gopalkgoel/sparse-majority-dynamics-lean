import MajorityDynamics.GraphProcess.EnumerationComparison.Basic
import MajorityDynamics.Literature.DegreeEnumeration.Consequences

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Literature.DegreeEnumeration

def ShiftBounds (x e P Q : ℝ) : Prop :=
  Real.exp (x-e)*Q ≤ P ∧ P ≤ Real.exp (x+e)*Q

theorem relative_half_shift {x P Q : ℝ} (hQ : 0 ≤ Q)
    (h : RelativeApproximation (1/2) P (Q*Real.exp x)) : ShiftBounds x 1 P Q := by
  have hb := h.bounds (mul_nonneg hQ (Real.exp_pos x).le)
  have htwo : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hlo : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; exact htwo)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlo (mul_nonneg (Real.exp_pos x).le hQ)
    rw [show x-1 = -1+x by ring,Real.exp_add]
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right htwo (mul_nonneg (Real.exp_pos x).le hQ)
    rw [Real.exp_add]
    nlinarith

theorem ShiftBounds.mul {x e P Q x' e' P' Q' : ℝ}
    (h : ShiftBounds x e P Q) (h' : ShiftBounds x' e' P' Q')
    (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q') :
    ShiftBounds (x+x') (e+e') (P*P') (Q*Q') := by
  have hP := (mul_nonneg (Real.exp_pos _).le hQ).trans h.1
  constructor
  · have hh := mul_le_mul h.1 h'.1 (mul_nonneg (Real.exp_pos _).le hQ') hP
    calc
      _ = Real.exp (x-e)*Q*(Real.exp (x'-e')*Q') := by
        rw [show x+x'-(e+e') = (x-e)+(x'-e') by ring, Real.exp_add]
        ring
      _ ≤ _ := hh
  · have hh := mul_le_mul h.2 h'.2 ((mul_nonneg (Real.exp_pos _).le hQ').trans h'.1)
      (mul_nonneg (Real.exp_pos _).le hQ)
    calc
      _ ≤ Real.exp (x+e)*Q*(Real.exp (x'+e')*Q') := hh
      _ = _ := by
        rw [show x+x'+(e+e') = (x+e)+(x'+e') by ring]
        simp only [Real.exp_add]
        ring

theorem shift_prod {I : Type*} (S : Finset I) (x e P Q : I → ℝ)
    (hQ : ∀ i ∈ S, 0 ≤ Q i) (h : ∀ i ∈ S, ShiftBounds (x i) (e i) (P i) (Q i)) :
    ShiftBounds (∑ i ∈ S, x i) (∑ i ∈ S, e i) (∏ i ∈ S, P i) (∏ i ∈ S, Q i) := by
  induction S using Finset.induction_on with
  | empty => simp [ShiftBounds]
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih (fun i hi => hQ i (by simp [hi]))
      (fun i hi => h i (by simp [hi]))) (hQ a (by simp))
      (Finset.prod_nonneg fun i hi => hQ i (by simp [hi]))

theorem ShiftBounds.sandwich {x e P Q C : ℝ}
    (h : ShiftBounds x e P Q) (hx : |x|+e ≤ C) (hQ : 0 ≤ Q) : Sandwich C P Q := by
  have hh := abs_le.mp (le_refl |x|)
  exact ⟨(mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hQ).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hQ)⟩

end MajorityDynamics.GraphProcess.EnumerationComparison
