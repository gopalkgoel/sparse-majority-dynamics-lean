import MajorityDynamics.Local.Admissibility
import MajorityDynamics.Universal.Nondegeneracy

noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal

theorem edgeScale_eq (N : ℕ) {p : ℝ} (hN : 0 < (N:ℝ)) (hp : 0 < p) :
    Local.edgeScale N p = (N:ℝ)*Real.sqrt (p*N) := by
  have hs := Real.sqrt_pos.mpr (mul_pos hp hN)
  unfold Local.edgeScale
  apply (div_eq_iff hs.ne').mpr
  nlinarith only [Real.sq_sqrt (mul_pos hp hN).le]

/-- LA3 and LA4 from a bounded centered mean target and macroscopic parts. -/
theorem admissible_edges_of_centered {V : Type*} [Fintype V] {n N : ℕ}
    (y : Local.CoarseData V n) (hcard : Fintype.card V = N)
    {p v M : ℝ} (hN : 0 < (N:ℝ)) (hp : 0 < p) (hv : 0 < v) (hM : 0 ≤ M)
    (hsizes : ∀ s, v*N ≤ (y.sizes s:ℝ))
    (hbound : ∀ s t, |ν n t*μ n s t| ≤ M)
    (hcenter : ∀ s t, |(y.realEdges s t / (y.sizes s:ℝ) - p*y.sizes t) /
      Real.sqrt (p*N) - ν n t*μ n s t| ≤ 1)
    (hlarge : (M+1)/v < Real.sqrt (p*N)) :
    ∀ s t, |y.realEdges s t-p*(y.sizes s:ℝ)*(y.sizes t:ℝ)| ≤
      (M+1)*Local.edgeScale N p ∧ 0 < y.realEdges s t := by
  intro s t
  let S := Real.sqrt (p*N)
  let a : ℝ := y.sizes s
  let b : ℝ := y.sizes t
  let z := (y.realEdges s t / a-p*b)/S
  have hS : 0 < S := Real.sqrt_pos.mpr (mul_pos hp hN)
  have ha : 0 < a := (mul_pos hv hN).trans_le (hsizes s)
  have haN : a ≤ N := by
    dsimp [a]
    exact_mod_cast (y.sizes_le_card s).trans_eq hcard
  have hsq : S*S = p*N := Real.mul_self_sqrt (mul_pos hp hN).le
  have hz : |z| ≤ M+1 := by
    have htri := abs_add_le (z-ν n t*μ n s t) (ν n t*μ n s t)
    have hh := hcenter s t
    change |z-ν n t*μ n s t| ≤ 1 at hh
    have hab := hbound s t
    rw [sub_add_cancel] at htri
    linarith
  have heq : y.realEdges s t-p*a*b = a*S*z := by
    dsimp [z]
    field_simp
  constructor
  · change |y.realEdges s t-p*a*b| ≤ _
    rw [heq,abs_mul,abs_mul,abs_of_pos ha,abs_of_pos hS,edgeScale_eq N hN hp]
    calc
      a*S*|z| ≤ a*S*(M+1) := mul_le_mul_of_nonneg_left hz (mul_pos ha hS).le
      _ ≤ (M+1)*((N:ℝ)*S) := by nlinarith [mul_le_mul_of_nonneg_right haN hS.le]
      _ = _ := rfl
  · have hvS : M+1 < v*S := by
      have h := (div_lt_iff₀ hv).mp hlarge
      nlinarith only [h]
    have hpb : p*(v*N) ≤ p*b := mul_le_mul_of_nonneg_left (hsizes t) hp.le
    have hzlo := (abs_le.mp hz).1
    have hpos : 0 < p*b+S*z := by
      have hh := mul_lt_mul_of_pos_right hvS hS
      rw [mul_assoc, hsq] at hh
      have hz' := mul_le_mul_of_nonneg_left hzlo hS.le
      nlinarith only [hh,hz',hpb,hsq]
    have hprod := mul_pos ha hpos
    nlinarith only [heq,hprod]

end MajorityDynamics.Idealized.CriticalDay
