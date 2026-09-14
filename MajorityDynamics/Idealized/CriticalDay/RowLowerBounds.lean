import MajorityDynamics.Idealized.CriticalDay.ShiftLipschitz

noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits

theorem row_lower_bounds (n : ℕ) (R U : ℝ) (hR : 0 ≤ R) (hU : 0 ≤ U) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 1/2 ∧ ∃ e₀ : ℝ, 0 < e₀ ∧
    ∀ (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
      (s : History (n+1)) (σ : Row (n+1)) (e : ℝ),
      (∀ t, |σ t| ≤ R) → |shift N p sizes| ≤ U → 0 ≤ e → e ≤ e₀ →
      Estimates N p sizes s σ (shift N p sizes) 1 e →
      φ ≤ Binomial.eventMass (Local.trials sizes s) (rowTilt N p σ)
        (Local.historySupport sizes s) ∧
      ∀ b, φ ≤ binomialSplit N p sizes s b σ ∧ binomialSplit N p sizes s b σ ≤ 1-φ := by
  obtain ⟨c, hc, hlower⟩ := gaussian_probabilities_uniform_lower n hR hU
  let φ := min (c/2) (1/4)
  have hφ : 0 < φ := lt_min (by positivity) (by norm_num)
  refine ⟨φ,hφ,(min_le_right _ _).trans_lt (by norm_num),c/2,by positivity,?_⟩
  intro N p sizes s σ e hσ hu he he0 hest
  have hh := (hlower s σ hσ).1
  have hmass := abs_le.mp hest.history_probability
  have hmasslow : c/2 ≤ binomialMass N p sizes s (Local.historySupport sizes s) σ := by
    simp only [one_mul] at hmass
    linarith [hmass.1,hmass.2]
  have hs : (Local.historySupport sizes s).Nonempty := by
    by_contra h
    have hz : Local.historySupport sizes s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [binomialMass,Binomial.eventMass,hz] at hmasslow
    linarith
  have hlo (b : Bool) : φ ≤ binomialSplit N p sizes s b σ := by
    have hchild := (hlower s σ hσ).2 b (shift N p sizes) hu
    have hden : 0 < gaussianMass σ (historyEvent s) := hc.trans_le hh
    have hden1 : gaussianMass σ (historyEvent s) ≤ 1 :=
      (le_abs_self _).trans (Process.gaussianMass_le_one σ _)
    have hratio : c ≤ gaussianMass σ (shiftedChildEvent s b (shift N p sizes)) /
        gaussianMass σ (historyEvent s) := by
      apply (le_div_iff₀ hden).mpr
      exact (mul_le_mul_of_nonneg_left hden1 hc.le).trans (by simpa using hchild)
    have hb := abs_le.mp (hest.split_probability b)
    have hφc : φ ≤ c/2 := min_le_left _ _
    simp only [one_mul] at hb
    linarith [hb.1,hb.2]
  refine ⟨(min_le_left _ _).trans hmasslow,?_⟩
  intro b
  have hsum := Local.splitProbability_add sizes (fun _ => rowTilt N p σ) s hs
  change binomialSplit N p sizes s false σ + binomialSplit N p sizes s true σ = 1 at hsum
  refine ⟨hlo b,?_⟩
  cases b <;> linarith [hlo false,hlo true]

end MajorityDynamics.Idealized.CriticalDay
