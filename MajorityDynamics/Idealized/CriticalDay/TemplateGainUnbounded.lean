import MajorityDynamics.Idealized.CriticalDay.GaussianGainUnbounded
import MajorityDynamics.Idealized.CriticalDay.TemplateGain

/-! Terminal template gain with no upper bound on the decision shift. -/
noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits
variable {n : ℕ}

private theorem positive_minimum' {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ f i := by
  classical
  have aux : ∀ S : Finset ι, ∃ m : ℝ, 0 < m ∧ ∀ i ∈ S, m ≤ f i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i S _ ih =>
      obtain ⟨m, hm, hb⟩ := ih
      refine ⟨min (f i) m, lt_min (hf i) hm, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb j hj)
  obtain ⟨m, hm, hb⟩ := aux Finset.univ
  exact ⟨m, hm, fun i => hb i (Finset.mem_univ _)⟩

/-- Once the normalized decision shift is bounded below, the exact binomial
template has a fixed signed gain, uniformly for arbitrarily large shifts. -/
theorem template_gain_uniform_unbounded (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ R : ℝ, 0 ≤ R →
      (∀ s t, |γ n s t| ≤ R) → ∃ e₀ : ℝ, 0 < e₀ ∧
      ∀ (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
        (σ : History (n+1) → Row (n+1)) (u e : ℝ),
      0 ≤ e → e ≤ e₀ → a ≤ u →
      (∀ s t, |σ s t| ≤ R) → (∀ s t, |σ s t - γ n s t| ≤ e) →
      (∀ s, |(sizes s:ℝ)-(N:ℝ)*ν n s| ≤ e*N) →
      (∀ s b, |binomialSplit N p sizes s b (σ s) -
        gaussianMass (σ s) (shiftedChildEvent s b u) /
          gaussianMass (σ s) (historyEvent s)| ≤ e) →
      ∀ s b, ζ*N ≤ sign b *
        (Local.templateSizes sizes (fun s => rowTilt N p (σ s)) (append s b) -
          (N:ℝ)*ν (n+1) (append s b)) := by
  obtain ⟨g, hg, hgaussian⟩ := gaussian_gain_uniform_unbounded n ha
  obtain ⟨m, hm, hmin⟩ := positive_minimum' (ν n) (ν_positive n)
  let ζ := m*g/4
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  refine ⟨ζ, hζ, ?_⟩
  intro R hR hγ
  obtain ⟨eG, heG, hgain⟩ := hgaussian R hR hγ
  let e₀ := min eG (min (g/2) ζ)
  have he₀ : 0 < e₀ := lt_min heG (lt_min (by positivity) hζ)
  refine ⟨e₀, he₀, ?_⟩
  intro N p sizes σ u e he he0 hau hσ hclose hsizes hsplit s b
  have heG' : e ≤ eG := he0.trans (min_le_left _ _)
  have heg : e ≤ g/2 := he0.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have heζ : e ≤ ζ := he0.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hG := hgain s (σ s) u e he heG' hau (hσ s) (hclose s) b
  let q := binomialSplit N p sizes s b (σ s)
  let r := ν (n+1) (append s b) / ν n s
  have hq : g/2 ≤ sign b*(q-r) := by
    have h1 := abs_le.mp (hsplit s b)
    cases b <;> simp only [sign_false, sign_true] at hG ⊢ <;>
      dsimp [q, r] <;> nlinarith [h1.1, h1.2]
  have hqb := binomialSplit_bounds N p sizes s b (σ s)
  have hz := abs_le.mp (hsizes s)
  have habs : |sign b| = 1 := by cases b <;> norm_num [sign]
  have herror : -(e*N) ≤ sign b*((sizes s:ℝ)-(N:ℝ)*ν n s)*q := by
    have hh : |sign b*((sizes s:ℝ)-(N:ℝ)*ν n s)*q| ≤ e*N := by
      rw [abs_mul, abs_mul, habs, one_mul, abs_of_nonneg hqb.1]
      exact (mul_le_mul_of_nonneg_left hqb.2 (abs_nonneg _)).trans
        (by simpa using hsizes s)
    exact (abs_le.mp hh).1
  have hNg := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (Nat.cast_nonneg N) (ν_positive n s).le)
  have hNm := mul_le_mul_of_nonneg_right (hmin s)
    (show 0 ≤ (N:ℝ)*(g/2) by positivity)
  have hNe := mul_le_mul_of_nonneg_right heζ
    (show 0 ≤ (N:ℝ) by positivity)
  have hr : ν n s*r = ν (n+1) (append s b) := by
    dsimp [r]
    exact mul_div_cancel₀ _ (ν_positive n s).ne'
  have ht : Local.templateSizes sizes (fun s => rowTilt N p (σ s)) (append s b) =
      (sizes s:ℝ)*q := by
    simp only [Local.templateSizes, parent_append, last_append]
    rfl
  rw [ht]
  have heq : sign b*((sizes s:ℝ)*q-(N:ℝ)*ν (n+1) (append s b)) =
      sign b*((sizes s:ℝ)-(N:ℝ)*ν n s)*q +
        (N:ℝ)*ν n s*(sign b*(q-r)) := by
    rw [← hr]
    ring
  rw [heq]
  dsimp [ζ] at hNe ⊢
  nlinarith only [herror, hNg, hNm, hNe]

end MajorityDynamics.Idealized.CriticalDay
