import MajorityDynamics.Idealized.CriticalDay.GaussianGain
import MajorityDynamics.Idealized.CriticalDay.ShiftLipschitz

noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits
variable {n : ℕ}

private theorem positive_minimum {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ f i := by
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

theorem binomialSplit_bounds (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n+1)) (b : Bool) (σ : Row (n+1)) :
    0 ≤ binomialSplit N p sizes s b σ ∧ binomialSplit N p sizes s b σ ≤ 1 := by
  classical
  have hn (S : Finset (Binomial.Box (Local.trials sizes s))) :
      0 ≤ binomialMass N p sizes s S σ := by
    exact Finset.sum_nonneg (fun a _ => (Binomial.mass_pos _ _ a).le)
  have hle : binomialMass N p sizes s (Local.childSupport sizes s b) σ ≤
      binomialMass N p sizes s (Local.historySupport sizes s) σ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Local.childSupport_subset sizes s b)
      (fun a _ _ => (Binomial.mass_pos _ _ a).le)
  unfold binomialSplit
  exact ⟨div_nonneg (hn _) (hn _), div_le_one_of_le₀ hle (hn _)⟩

/-- Uniform stability of the positive macroscopic template gain. The final
critical-day theorem supplies these concrete E.3 and faithful-size bounds. -/
theorem template_gain_uniform (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ R U : ℝ, 0 ≤ R → 0 ≤ U →
      (∀ s t, |γ n s t| ≤ R) → ∃ e₀ : ℝ, 0 < e₀ ∧
      ∀ (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
        (σ : History (n+1) → Row (n+1)) (u e : ℝ),
      0 ≤ e → e ≤ e₀ → a ≤ u → u ≤ U →
      (∀ s t, |σ s t| ≤ R) → (∀ s t, |σ s t - γ n s t| ≤ e) →
      (∀ s, |(sizes s:ℝ)-(N:ℝ)*ν n s| ≤ e*N) →
      (∀ s b, |binomialSplit N p sizes s b (σ s) -
        gaussianMass (σ s) (shiftedChildEvent s b u) / gaussianMass (σ s) (historyEvent s)| ≤ e) →
      ∀ s b, ζ*N ≤ sign b * (Local.templateSizes sizes (fun s => rowTilt N p (σ s))
        (append s b) - (N:ℝ)*ν (n+1) (append s b)) := by
  obtain ⟨g, hg, hgain⟩ := gaussian_gain_uniform n ha
  obtain ⟨m, hm, hmin⟩ := positive_minimum (ν n) (ν_positive n)
  let ζ := m*g/4
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  refine ⟨ζ, hζ, ?_⟩
  intro R U hR hU hγ
  obtain ⟨K, hK, hlip⟩ := gaussian_shifted_lipschitz n R U hR hU
  let e₀ := min (g/(2*(K+1))) ζ
  have he₀ : 0 < e₀ := lt_min (by positivity) hζ
  refine ⟨e₀, he₀, ?_⟩
  intro N p sizes σ u e he he0 hau huU hσ hclose hsizes hsplit s b
  have heK : (K+1)*e ≤ g/2 := by
    have h := he0.trans (min_le_left _ _)
    have hpos : 0 < 2*(K+1) := by positivity
    have hmul := (le_div_iff₀ hpos).mp h
    nlinarith
  have heζ : e ≤ ζ := he0.trans (min_le_right _ _)
  have hu : |u| ≤ U := by simpa only [abs_of_nonneg (ha.le.trans hau)] using huU
  have hL := hlip s (σ s) (γ n s) (hσ s) (hγ s) u hu e he (hclose s) b
  have hG := hgain s u hau b
  let q := binomialSplit N p sizes s b (σ s)
  let r := ν (n+1) (append s b) / ν n s
  have hq : g/2 ≤ sign b*(q-r) := by
    have h1 := abs_le.mp (hsplit s b)
    have h2 := abs_le.mp hL
    cases b <;> simp only [sign_false, sign_true] at hG ⊢ <;>
      dsimp [q, r] <;> nlinarith [h1.1,h1.2,h2.1,h2.2]
  have hqb := binomialSplit_bounds N p sizes s b (σ s)
  have hz := abs_le.mp (hsizes s)
  have habs : |sign b| = 1 := by cases b <;> norm_num [sign]
  have herror : -(e*N) ≤ sign b*((sizes s:ℝ)-(N:ℝ)*ν n s)*q := by
    have hh : |sign b*((sizes s:ℝ)-(N:ℝ)*ν n s)*q| ≤ e*N := by
      rw [abs_mul, abs_mul, habs, one_mul, abs_of_nonneg hqb.1]
      exact (mul_le_mul_of_nonneg_left hqb.2 (abs_nonneg _)).trans (by simpa using hsizes s)
    exact (abs_le.mp hh).1
  have hNg := mul_le_mul_of_nonneg_left hq (mul_nonneg (Nat.cast_nonneg N) (ν_positive n s).le)
  have hNm := mul_le_mul_of_nonneg_right (hmin s) (show 0 ≤ (N:ℝ)*(g/2) by positivity)
  have hNe := mul_le_mul_of_nonneg_right heζ (show 0 ≤ (N:ℝ) by positivity)
  have hr : ν n s*r = ν (n+1) (append s b) := by
    dsimp [r]
    exact mul_div_cancel₀ _ (ν_positive n s).ne'
  have ht : Local.templateSizes sizes (fun s => rowTilt N p (σ s)) (append s b) =
      (sizes s:ℝ)*q := by
    simp only [Local.templateSizes, parent_append, last_append]
    rfl
  rw [ht]
  have heq : sign b*((sizes s:ℝ)*q-(N:ℝ)*ν (n+1) (append s b)) =
      sign b*((sizes s:ℝ)-(N:ℝ)*ν n s)*q + (N:ℝ)*ν n s*(sign b*(q-r)) := by
    rw [← hr]
    ring
  rw [heq]
  dsimp [ζ] at hNe ⊢
  nlinarith only [herror, hNg, hNm, hNe]

end MajorityDynamics.Idealized.CriticalDay
