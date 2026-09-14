import MajorityDynamics.Analysis.FiniteTiltEstimate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Finite tilt expansion stable under logarithmic likelihood errors -/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Analysis.FiniteTiltEstimate

variable {α : Type*}

/-- Combine exact exponential response with a uniformly bounded log-density
error. The normalized laws may arise from different underlying trial counts. -/
theorem approximate_exponential_remainder (S : Finset α) (hS : S.Nonempty)
    (w w' f z r : α → ℝ) (K : ℝ)
    (hw : ∀ a ∈ S, 0 < w a) (hs : ∑ a ∈ S, w a = 1) (hs' : ∑ a ∈ S, w' a = 1)
    (hchange : ∀ a ∈ S, w' a = K * (w a * Real.exp (z a + r a)))
    (H b δ : ℝ) (hH : 0 ≤ H) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hbsmall : b ≤ 1 / 4) (hδsmall : δ ≤ 1 / 4)
    (hf : ∀ a ∈ S, |f a| ≤ H) (hz : ∀ a ∈ S, |z a| ≤ b)
    (hr : ∀ a ∈ S, |r a| ≤ δ) :
    |average S w' f - (average S w f + average S w (fun a => z a * f a) -
        average S w z * average S w f)| ≤ 12 * H * b ^ 2 + 8 * H * δ := by
  let Z := average S w (fun a => Real.exp (z a))
  have hZ : 0 < Z := Finset.sum_pos (fun a ha => mul_pos (hw a ha) (Real.exp_pos _)) hS
  let v := fun a => w a * Real.exp (z a) / Z
  have hv : ∀ a ∈ S, 0 < v a := fun a ha => div_pos (mul_pos (hw a ha) (Real.exp_pos _)) hZ
  have hvs : ∑ a ∈ S, v a = 1 := by
    dsimp [v]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    change Z * Z⁻¹ = 1
    exact mul_inv_cancel₀ hZ.ne'
  have hveq : average S v f = average S w (fun a => Real.exp (z a) * f a) / Z := by
    apply reweighted_average S w v z f Z⁻¹ hvs
    intro a _
    dsimp [v]
    ring
  have hweq : average S w' f = average S v (fun a => Real.exp (r a) * f a) /
      average S v (fun a => Real.exp (r a)) := by
    apply reweighted_average S v w' r f (K * Z) hs'
    intro a ha
    rw [hchange a ha, Real.exp_add]
    dsimp [v]
    field_simp
  have he : ∀ a ∈ S, |Real.exp (r a) - 1| ≤ 2 * δ := by
    intro a ha
    exact (Real.abs_exp_sub_one_le ((hr a ha).trans (by linarith))).trans
      (mul_le_mul_of_nonneg_left (hr a ha) (by norm_num))
  have hstable := relative_weight_remainder S v f (fun a => Real.exp (r a) - 1)
    (fun a ha => (hv a ha).le) hvs H (2 * δ) hH (by positivity) (by linarith) hf he
  have hstable' : |average S w' f - average S v f| ≤ 8 * H * δ := by
    rw [hweq]
    simpa only [show ∀ a, 1 + (Real.exp (r a) - 1) = Real.exp (r a) from fun _ => by ring,
      show 4 * H * (2 * δ) = 8 * H * δ by ring] using hstable
  have hresponse := exponential_remainder S w f z (fun a ha => (hw a ha).le)
    hs H b hH hb hbsmall hf hz
  rw [← hveq] at hresponse
  calc
    _ ≤ |average S w' f - average S v f| +
        |average S v f - (average S w f + average S w (fun a => z a * f a) -
          average S w z * average S w f)| := abs_sub_le _ _ _
    _ ≤ 8 * H * δ + 12 * H * b ^ 2 := add_le_add hstable' hresponse
    _ = _ := by ring

def normalize (S : Finset α) (w : α → ℝ) (a : α) : ℝ := w a / ∑ b ∈ S, w b

theorem normalize_sum (S : Finset α) (w : α → ℝ) (h : (∑ b ∈ S, w b) ≠ 0) :
    ∑ a ∈ S, normalize S w a = 1 := by
  simp only [normalize, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ h

/-- Unnormalized positive masses: an oscillation bound for the log-likelihood
residual suffices. Its constant part is removed by normalization. -/
theorem normalized_log_tilt_expansion (S : Finset α) (a₀ : α) (ha₀ : a₀ ∈ S)
    (P₀ P₁ f z : α → ℝ) (hP₀ : ∀ a ∈ S, 0 < P₀ a) (hP₁ : ∀ a ∈ S, 0 < P₁ a)
    (H b δ : ℝ) (hH : 0 ≤ H) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hbsmall : b ≤ 1 / 4) (hδsmall : δ ≤ 1 / 4)
    (hf : ∀ a ∈ S, |f a| ≤ H) (hz : ∀ a ∈ S, |z a| ≤ b)
    (hr : ∀ a ∈ S,
      |(Real.log (P₁ a) - Real.log (P₀ a) - z a) -
        (Real.log (P₁ a₀) - Real.log (P₀ a₀) - z a₀)| ≤ δ) :
    |average S (normalize S P₁) f -
      (average S (normalize S P₀) f + average S (normalize S P₀) (fun a => z a * f a) -
        average S (normalize S P₀) z * average S (normalize S P₀) f)| ≤
      12 * H * b ^ 2 + 8 * H * δ := by
  have hS : S.Nonempty := ⟨a₀, ha₀⟩
  have hW₀ : 0 < ∑ a ∈ S, P₀ a := Finset.sum_pos hP₀ hS
  have hW₁ : 0 < ∑ a ∈ S, P₁ a := Finset.sum_pos hP₁ hS
  let r := fun a => (Real.log (P₁ a) - Real.log (P₀ a) - z a) -
    (Real.log (P₁ a₀) - Real.log (P₀ a₀) - z a₀)
  let C := Real.log (P₁ a₀) - Real.log (P₀ a₀) - z a₀ +
    Real.log (∑ a ∈ S, P₀ a) - Real.log (∑ a ∈ S, P₁ a)
  have hw₀ : ∀ a ∈ S, 0 < normalize S P₀ a := fun a ha => div_pos (hP₀ a ha) hW₀
  have hw₁ : ∀ a ∈ S, 0 < normalize S P₁ a := fun a ha => div_pos (hP₁ a ha) hW₁
  apply approximate_exponential_remainder S hS (normalize S P₀) (normalize S P₁)
    f z r (Real.exp C) hw₀ (normalize_sum S P₀ hW₀.ne') (normalize_sum S P₁ hW₁.ne')
    _ H b δ hH hb hδ hbsmall hδsmall hf hz hr
  intro a ha
  have hlog : Real.log (normalize S P₁ a) - Real.log (normalize S P₀ a) = C + (z a + r a) := by
    rw [normalize, normalize, Real.log_div (hP₁ a ha).ne' hW₁.ne',
      Real.log_div (hP₀ a ha).ne' hW₀.ne']
    dsimp [C, r]
    ring
  have he := congrArg Real.exp hlog
  rw [Real.exp_sub, Real.exp_log (hw₁ a ha), Real.exp_log (hw₀ a ha), Real.exp_add] at he
  have he' := (div_eq_iff (hw₀ a ha).ne').mp he
  calc
    _ = _ := he'
    _ = _ := by ring

end MajorityDynamics.Analysis.FiniteTiltEstimate
