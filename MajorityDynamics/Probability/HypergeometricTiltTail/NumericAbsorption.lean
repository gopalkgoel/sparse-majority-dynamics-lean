import MajorityDynamics.Probability.HypergeometricTiltTail.Numerics

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.Probability.HypergeometricTiltTail.Numerics

/-- All fixed logarithmic and linear-in-deviation costs are absorbed by half of
 the quadratic tail exponent; the threshold precedes the deviation. -/
theorem eventually_absorb {B C K : ℝ} (_hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ τ : ℝ,
      (Real.log (N:ℝ))^100 ≤ |τ| →
      B*(Real.log (N:ℝ))^4 +
        C*(|τ| *Real.log (N:ℝ)+(Real.log (N:ℝ))^2+Real.log (N:ℝ)+1)
        ≤ τ^2/(2*K) := by
  obtain ⟨X₁,_,h₁⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=1) (b:=100) (A:=4*K*C) (B:=1) (by norm_num) zero_lt_one
  obtain ⟨X₂,_,h₂⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=4) (b:=200) (A:=4*K*(B+3*C)) (B:=1) (by norm_num) zero_lt_one
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max 1 (max X₁ X₂)))
  refine ⟨N₀, ?_⟩
  intro N hN τ hτ
  let x := Real.log (N:ℝ)
  have hx1 : 1 ≤ x := (le_max_left _ _).trans (h₀ N hN)
  have hx0 : 0 ≤ x := by linarith
  have hlin : 4*K*C*x ≤ x^100 := by
    simpa [Real.rpow_one,Real.rpow_natCast] using h₁ x
      (((le_max_left _ _).trans (le_max_right _ _)).trans (h₀ N hN))
  have hquad : 4*K*(B+3*C)*x^4 ≤ x^200 := by
    simpa [Real.rpow_natCast] using h₂ x
      (((le_max_right _ _).trans (le_max_right _ _)).trans (h₀ N hN))
  have hτ' : x^100 ≤ |τ| := hτ
  have hsq : x^200 ≤ τ^2 := by
    have hh := pow_le_pow_left₀ (pow_nonneg hx0 100) hτ' 2
    simpa [← pow_mul, sq_abs] using hh
  have hx2 : x^2 ≤ x^4 := by exact pow_le_pow_right₀ hx1 (by norm_num)
  have hx4 : x ≤ x^4 := by simpa using pow_le_pow_right₀ hx1 (show 1 ≤ 4 by omega)
  have h14 : 1 ≤ x^4 := one_le_pow₀ hx1
  have hlinear : C*(|τ| *x) ≤ τ^2/(4*K) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*K)).mpr
    have hh := mul_le_mul_of_nonneg_right (hlin.trans hτ') (abs_nonneg τ)
    nlinarith [sq_abs τ]
  have hrest : (B+3*C)*x^4 ≤ τ^2/(4*K) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*K)).mpr
    nlinarith
  have hsmall : B*x^4+C*(x^2+x+1) ≤ (B+3*C)*x^4 := by
    nlinarith [mul_le_mul_of_nonneg_left hx2 hC,
      mul_le_mul_of_nonneg_left hx4 hC,mul_le_mul_of_nonneg_left h14 hC]
  have heq : τ^2/(4*K)+τ^2/(4*K)=τ^2/(2*K) := by ring
  change B*x^4+C*(|τ| *x+x^2+x+1) ≤ _
  nlinarith

theorem eventually_exp_absorb {B C K : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ τ : ℝ,
      (Real.log (N:ℝ))^100 ≤ |τ| →
      Real.exp (B*(Real.log (N:ℝ))^4) *
        Real.exp (C*(|τ| *Real.log (N:ℝ)+(Real.log (N:ℝ))^2+Real.log (N:ℝ)+1)) *
        Real.exp (-τ^2/K) ≤ Real.exp (-(1/(2*K))*τ^2) := by
  obtain ⟨N₀,h₀⟩ := eventually_absorb hB hC hK
  refine ⟨N₀, ?_⟩
  intro N hN τ hτ
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := h₀ N hN τ hτ
  have heq : -τ^2/K+(1/(2*K))*τ^2 = -(τ^2/(2*K)) := by ring
  linarith

end MajorityDynamics.Probability.HypergeometricTiltTail.Numerics
