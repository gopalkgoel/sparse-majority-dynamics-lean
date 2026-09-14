import MajorityDynamics.Idealized.CriticalDay.GaussianGain
import MajorityDynamics.Idealized.CriticalDay.ShiftLipschitz

/-! The signed Gaussian child gain is monotone in the decision shift.  Thus
the compactness estimate only has to be used at one fixed positive shift;
there is no upper bound on the actual terminal shift. -/
noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits
variable {n : ℕ}

private theorem decision_false_mono' {c : Bool} {x y : ℝ} (hxy : x ≤ y)
    (hx : decision c false x) : decision c false y := by
  simp only [decision, sign_false, one_mul] at hx ⊢
  rcases hx with hx | ⟨hx, hc⟩
  · exact Or.inl (hx.trans_le hxy)
  · rcases lt_or_eq_of_le hxy with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hc⟩

/-- For a fixed Gaussian mean, the signed conditional child probability is
monotone in a nonnegative decision shift. -/
theorem gaussian_shifted_signed_quotient_mono (s : History (n+1)) (σ : Row (n+1))
    {a u : ℝ} (hau : a ≤ u) (b : Bool) :
    sign b * (gaussianMass σ (shiftedChildEvent s b a) /
      gaussianMass σ (historyEvent s)) ≤
    sign b * (gaussianMass σ (shiftedChildEvent s b u) /
      gaussianMass σ (historyEvent s)) := by
  cases b
  · have hsub : shiftedChildEvent s false a ⊆ shiftedChildEvent s false u := by
      intro x hx
      have hshift : imbalance (Fin.last n) x + a ≤
          imbalance (Fin.last n) x + u := by linarith
      exact ⟨hx.1, decision_false_mono' hshift hx.2⟩
    have hm := measureReal_mono
      (μ := rowLaw (ν n) σ) hsub
    have hd : 0 ≤ gaussianMass σ (historyEvent s) := measureReal_nonneg
    simp only [sign_false, one_mul]
    exact div_le_div_of_nonneg_right hm hd
  · have hsub : shiftedChildEvent s true u ⊆ shiftedChildEvent s true a := by
      intro x hx
      refine ⟨hx.1, (decision_complement _ _).mpr ?_⟩
      intro ha
      have hshift : imbalance (Fin.last n) x + a ≤
          imbalance (Fin.last n) x + u := by linarith
      exact (decision_complement _ _).mp hx.2
        (decision_false_mono' hshift ha)
    have hm := measureReal_mono
      (μ := rowLaw (ν n) σ) hsub
    change gaussianMass σ (shiftedChildEvent s true u) ≤
      gaussianMass σ (shiftedChildEvent s true a) at hm
    have hd : 0 ≤ gaussianMass σ (historyEvent s) := measureReal_nonneg
    simpa only [sign_true, neg_one_mul] using
      (neg_le_neg (div_le_div_of_nonneg_right hm hd))

/-- Uniform positive Gaussian gain for every shift above a fixed positive
threshold.  Unlike `gaussian_shifted_lipschitz`, the actual shift has no upper
bound: compactness is used only at the fixed comparison point `a`. -/
theorem gaussian_gain_uniform_unbounded (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ R : ℝ, 0 ≤ R →
      (∀ s t, |γ n s t| ≤ R) → ∃ e₀ : ℝ, 0 < e₀ ∧
      ∀ (s : History (n+1)) (σ : Row (n+1)) (u e : ℝ),
      0 ≤ e → e ≤ e₀ → a ≤ u →
      (∀ t, |σ t| ≤ R) → (∀ t, |σ t - γ n s t| ≤ e) → ∀ b : Bool,
      ζ ≤ sign b * (gaussianMass σ (shiftedChildEvent s b u) /
        gaussianMass σ (historyEvent s) -
          ν (n+1) (append s b) / ν n s) := by
  obtain ⟨g, hg, hgain⟩ := gaussian_gain_uniform n ha
  refine ⟨g/2, by positivity, ?_⟩
  intro R hR hγ
  obtain ⟨K, hK, hlip⟩ := gaussian_shifted_lipschitz n R a hR ha.le
  let e₀ := g / (2*(K+1))
  have he₀ : 0 < e₀ := by dsimp [e₀]; positivity
  refine ⟨e₀, he₀, ?_⟩
  intro s σ u e he he0 hau hσ hclose b
  have hea : |a| ≤ a := by rw [abs_of_pos ha]
  have hL := hlip s σ (γ n s) hσ (hγ s) a hea e he hclose b
  have hG := hgain s a (le_refl a) b
  have heK : K*e ≤ g/2 := by
    have h := he0
    dsimp [e₀] at h
    have hpos : 0 < 2*(K+1) := by positivity
    have hmul := (le_div_iff₀ hpos).mp h
    nlinarith
  have hfixed : g/2 ≤ sign b *
      (gaussianMass σ (shiftedChildEvent s b a) /
        gaussianMass σ (historyEvent s) -
          ν (n+1) (append s b) / ν n s) := by
    have hLabs := abs_le.mp hL
    cases b <;> simp only [sign_false, sign_true] at hG ⊢ <;>
      nlinarith [hLabs.1, hLabs.2]
  have hmono := gaussian_shifted_signed_quotient_mono s σ hau b
  calc
    g / 2 ≤ sign b *
        (gaussianMass σ (shiftedChildEvent s b a) /
          gaussianMass σ (historyEvent s) -
            ν (n+1) (append s b) / ν n s) := hfixed
    _ ≤ sign b *
        (gaussianMass σ (shiftedChildEvent s b u) /
          gaussianMass σ (historyEvent s) -
            ν (n+1) (append s b) / ν n s) := by
      cases b <;> simp only [sign_false, sign_true] at hmono ⊢ <;> linarith

end MajorityDynamics.Idealized.CriticalDay
