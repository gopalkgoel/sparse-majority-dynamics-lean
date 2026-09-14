import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics
import MajorityDynamics.Local.CoarseData

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal

/-- Paper B.5's exponent h (h/2+1), with h=2^(n+1). -/
def totalExponent (n : ℕ) : ℕ := 2^(n+1) * (2^n + 1)

theorem totalExponent_eq (n : ℕ) :
    (totalExponent n : ℝ) = (Fintype.card (History (n+1)) : ℝ) *
      ((Fintype.card (History (n+1)) : ℝ)/2+1) := by
  rw [history_card]
  simp only [totalExponent, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one, pow_succ]
  ring

theorem absorb_constant {x c a : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hlarge : c⁻¹ ≤ x) : x^(-(a+1)) ≤ c*x^(-a) := by
  have hi : x⁻¹ ≤ c := (inv_le_comm₀ hx hc).mpr hlarge
  calc
    x^(-(a+1)) = x^(-a)*x⁻¹ := by
      rw [show -(a+1) = -a + (-1) by ring, Real.rpow_add hx, Real.rpow_neg_one]
    _ ≤ x^(-a)*c := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hx.le _)
    _ = c*x^(-a) := mul_comm _ _

/-- One extra atom-scale power absorbs every fixed positive block constant. -/
theorem eventually_absorb_constant {θ T c : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      0 < (N : ℝ)^2*p ∧ ∀ a : ℝ,
        ((N : ℝ)^2*p)^(-(a+1)) ≤ c*((N : ℝ)^2*p)^(-a) := by
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := c⁻¹) (inv_pos.mpr hc) (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨N₀, ?_⟩
  intro N hN p hlo hhi
  obtain ⟨hNr,hp,hN1,hmean,_⟩ := h₀ N hN p hlo hhi
  have hx : 0 < (N : ℝ)^2*p := by positivity
  refine ⟨hx, fun a => absorb_constant hx hc ?_⟩
  have hh := mul_le_mul_of_nonneg_left hN1 (mul_pos hp hNr).le
  nlinarith

theorem product_power (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (∏ _s : History (n+1), x^(-((Fintype.card (History (n+1)) : ℝ)/2+1))) =
      x^(-(totalExponent n : ℝ)) := by
  rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast,
    ← Real.rpow_mul hx.le, totalExponent_eq]
  congr 1
  ring

end MajorityDynamics.GraphProcess.RowExactTotals
