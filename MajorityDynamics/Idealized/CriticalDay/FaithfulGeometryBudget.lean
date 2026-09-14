import MajorityDynamics.Idealized.CriticalDay.Balance
import MajorityDynamics.Idealized.RowLimits.ParameterGeometryBudget

/-! Literal faithful arrays imply the terminal size/history geometry with
explicit errors; no power-law density relation is used. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (scale)

/-- Macroscopic trials and affine-support sizes follow from a relative-size
budget alone, including exact conversion of the original integer data. -/
theorem integer_geometry_of_relative_error {n N : ℕ} {e : ℝ}
    (_he : 0 ≤ e) (η : History (n+1) → ℤ)
    (herror : ∀ t, |(η t:ℝ)-(N:ℝ)*ν n t| ≤ (N:ℝ)*e)
    (hsmall : ∀ t, 4*e ≤ ν n t)
    (hlarge : ∀ t, 4*((2*n+6:ℕ):ℝ) ≤ (N:ℝ)*ν n t) :
    (∀ t, 0 < η t) ∧
    (∀ t, ((naturalSizes η t:ℕ):ℝ) = (η t:ℝ)) ∧
    (∀ t, 2*n+5 ≤ naturalSizes η t) ∧
    (∀ s t, (N:ℝ)*ν n t/2 ≤ (Local.trials (naturalSizes η) s t:ℝ)) ∧
    (∀ s t, (Local.trials (naturalSizes η) s t:ℝ) ≤ 2*N*ν n t) := by
  have hbound (t) : 3*((N:ℝ)*ν n t)/4 ≤ (η t:ℝ) ∧
      (η t:ℝ) ≤ 5*((N:ℝ)*ν n t)/4 := by
    have hh := abs_le.mp (herror t)
    have hb := mul_le_mul_of_nonneg_left (hsmall t) (Nat.cast_nonneg (α:=ℝ) N)
    constructor <;> linarith [hh.1,hh.2]
  have hη : ∀ t, 0 < η t := by
    intro t
    have hl := hlarge t
    have hb := (hbound t).1
    have hh : (0:ℝ) < η t := by push_cast at hl; linarith
    exact_mod_cast hh
  have hcast : ∀ t, ((naturalSizes η t:ℕ):ℝ) = (η t:ℝ) := by
    intro t
    exact_mod_cast Int.toNat_of_nonneg (hη t).le
  have hs : ∀ t, 0 < naturalSizes η t := by
    intro t
    have hh : (0:ℝ) < (naturalSizes η t:ℕ) := by rw [hcast]; exact_mod_cast hη t
    exact_mod_cast hh
  refine ⟨hη,hcast,?_,?_,?_⟩
  · intro t
    have hh : ((2*n+5:ℕ):ℝ) ≤ (naturalSizes η t:ℕ) := by
      rw [hcast]
      have hl := hlarge t
      have hb := (hbound t).1
      push_cast at hl ⊢
      linarith
    exact_mod_cast hh
  · intro s t
    rw [RowLimits.trials_cast _ _ _ (hs t),hcast]
    have hl := hlarge t
    have hb := (hbound t).1
    split_ifs <;> push_cast at hl <;> linarith
  · intro s t
    rw [RowLimits.trials_cast _ _ _ (hs t),hcast]
    have hl := hlarge t
    have hb := (hbound t).2
    split_ifs <;> linarith

theorem faithful_relative_size_budget {n N : ℕ} (hN : 0 < N)
    {p T δ τ R : ℝ} {a : Process.Data}
    {η : History (n+1) → ℤ} {edges : History (n+1) → History (n+1) → ℤ}
    (hT : 0 ≤ T) (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hpow : (N:ℝ)^(-δ) ≤ 1)
    (hf : FaithfulNumericalData N p T δ τ a n η edges)
    (href : ∀ t, |((a.state n).sizes t:ℝ)-(N:ℝ)*ν n t| ≤ (N:ℝ)*R) :
    ∀ t, |(η t:ℝ)-(N:ℝ)*ν n t| ≤
      (N:ℝ)*(R+comparisonConstant n T*betaScale N p n) := by
  intro t
  have hh := (abs_sub_le (η t:ℝ) ((a.state n).sizes t:ℝ) ((N:ℝ)*ν n t)).trans
    (add_le_add (faithful_size_close hT hτ hτT hpow hf t) (href t))
  rw [sizeScale_eq N hN p n] at hh
  exact hh.trans_eq (by ring)

/-- The earlier-history parameter is response times the inherited error,
not response itself: the leading perturbation cancels exactly. -/
theorem faithful_history_budget {n N : ℕ} (hN : 0 < N) {p : Binomial.Probability}
    {T δ τ : ℝ} {a : Process.Data}
    {η : History (n+1) → ℤ} {edges : History (n+1) → History (n+1) → ℤ}
    (hsym : Process.StateSymmetric (a.state n))
    (hcast : ∀ t, ((naturalSizes η t:ℕ):ℝ) = (η t:ℝ))
    (hf : FaithfulNumericalData N (p:ℝ) T δ τ a n η edges) :
    ∀ s j, |∑ t, historyMatrix s j t*(naturalSizes η t:ℝ)| ≤
      ((Fintype.card (History (n+1)):ℝ)*T*
        (betaScale N p n*scale N p)*(N:ℝ)^(-δ))*(N:ℝ)/scale N p := by
  intro s j
  have hb := PerturbedEvolution.faithful_earlier_imbalance hsym hf j
  have hs : 0 < scale N p := Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hN))
  have hid : (∑ t, historyMatrix s j t*(naturalSizes η t:ℝ)) =
      sign (bits (n+1) s j.succ)*∑ t, character j.castSucc t*(η t:ℝ) := by
    simp only [historyMatrix,hcast,Finset.mul_sum,mul_assoc,character]
  rw [hid,abs_mul]
  have hsign : |sign (bits (n+1) s j.succ)| = 1 := by
    cases bits (n+1) s j.succ <;> norm_num
  rw [hsign,one_mul]
  apply hb.trans_eq
  rw [sizeScale_eq N hN p n]
  field_simp

/-- A positive fraction of the response survives in the actual decision
shift. There is no upper bound on that response. -/
theorem faithful_shift_lower_of_budget {n N : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {T δ τ : ℝ} {a : Process.Data}
    {η : History (n+1) → ℤ} {edges : History (n+1) → History (n+1) → ℤ}
    (_hT : 0 < T) (hτ : T⁻¹ ≤ τ)
    (hsym : Process.StateSymmetric (a.state n))
    (hcast : ∀ t, ((naturalSizes η t:ℕ):ℝ) = (η t:ℝ))
    (hf : FaithfulNumericalData N (p:ℝ) T δ τ a n η edges)
    (hsmall : (Fintype.card (History (n+1)):ℝ)*T*(N:ℝ)^(-δ) ≤ T⁻¹*lead n/2) :
    (T⁻¹*lead n/2)*(betaScale N p n*scale N p) ≤ RowLimits.shift N p (naturalSizes η) := by
  have ha : 0 ≤ betaScale N p n*scale N p := by
    unfold betaScale scale
    positivity
  have herr := (abs_le.mp (faithful_shift_error hN hsym hcast hf)).1
  have hbudget := mul_le_mul_of_nonneg_right hsmall ha
  have hlead := mul_le_mul_of_nonneg_right hτ (mul_nonneg ha (lead_pos n).le)
  nlinarith only [herr,hbudget,hlead]

end MajorityDynamics.Idealized.CriticalDay
