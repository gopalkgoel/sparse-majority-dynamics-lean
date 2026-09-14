import MajorityDynamics.Idealized.CriticalDay.GaussianGain
import MajorityDynamics.Idealized.CriticalDay.GaussianGainUnbounded
import MajorityDynamics.Analysis.ConditionalGaussian.SmallSetLower

/-! A non-sharp but quantitative small-shift gain. The exponent is the full
Gaussian row dimension, fixed before N and p. Thus an inverse-logarithmic shift
still yields inverse-logarithmic gain; no boundary derivative is needed. -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise
open MajorityDynamics.Universal MajorityDynamics.Analysis
namespace MajorityDynamics.Idealized.CriticalDay
open RowLimits
variable {n : ℕ}

theorem smul_gainSlab_one_subset (s : History (n + 1)) {u : ℝ} (hu : 0 < u) :
    u • gainSlab s 1 ⊆ gainSlab s u := by
  rintro y ⟨x, hx, rfl⟩
  have hlin (r : Fin (n + 1)) : imbalance r (u • x) = u * imbalance r x := by
    simpa only [imbalanceCLM_apply, smul_eq_mul] using (imbalanceCLM r).map_smul u x
  refine ⟨?_, ?_⟩
  · rw [mem_historyCone]
    intro r
    rw [hlin]
    have h := mul_pos hu ((mem_historyCone s x).mp hx.1 r)
    nlinarith
  · change -u < imbalance (Fin.last n) (u • x) ∧
      imbalance (Fin.last n) (u • x) < 0
    rw [hlin]
    constructor <;> nlinarith [mul_pos hu (show 0 < imbalance (Fin.last n) x + 1 by
      linarith [hx.2.1]), mul_neg_of_pos_of_neg hu hx.2.2]

theorem gainSlab_mass_polynomial_lower (s : History (n + 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      c * u ^ Fintype.card (History (n + 1)) ≤
        (rowLaw (ν n) (γ n s)).real (gainSlab s u) := by
  obtain ⟨x, hx⟩ := gainSlab_nonempty s (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (gainSlab_open s 1) x hx
  obtain ⟨c, hc, hbound⟩ := ConditionalGaussian.gaussianLaw_small_ball_lower
    (covariance (ν n)) (covariance_posDef _ (ν_positive n)) (γ n s) x hr
  refine ⟨c, hc, ?_⟩
  intro u hu hu1
  simp only [History, Fintype.card_fin]
  apply (hbound u hu hu1).trans
  exact measureReal_mono (μ := rowLaw (ν n) (γ n s))
    ((smul_set_mono hball).trans (smul_gainSlab_one_subset s hu))

theorem gaussian_gain_polynomial (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : History (n + 1)) (u : ℝ),
      0 < u → u ≤ 1 → ∀ (v : ℝ), u ≤ v → ∀ b : Bool,
      c * u ^ Fintype.card (History (n + 1)) ≤
        sign b * (gaussianMass (γ n s) (shiftedChildEvent s b v) /
          gaussianMass (γ n s) (historyEvent s) - ν (n + 1) (append s b) / ν n s) := by
  classical
  choose c hc hb using (gainSlab_mass_polynomial_lower (n := n))
  let f : History (n + 1) → ℝ := fun s => c s / gaussianMass (γ n s) (historyEvent s)
  have hden (s : History (n + 1)) : 0 < gaussianMass (γ n s) (historyEvent s) :=
    universal_history_probability_pos n s
  have hf (s : History (n + 1)) : 0 < f s := div_pos (hc s) (hden s)
  have aux : ∀ S : Finset (History (n + 1)), ∃ q : ℝ, 0 < q ∧ ∀ s ∈ S, q ≤ f s := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert s S _ ih =>
      obtain ⟨q, hq, hb⟩ := ih
      refine ⟨min (f s) q, lt_min (hf s) hq, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb t ht)
  obtain ⟨q, hq, hqbound⟩ := aux Finset.univ
  refine ⟨q, hq, ?_⟩
  intro s u hu hu1 v huv b
  have hslab := (hb s u hu hu1).trans (gaussian_signed_gain s hu huv b)
  have h := div_le_div_of_nonneg_right hslab (hden s).le
  have hqmul := mul_le_mul_of_nonneg_right (hqbound s (Finset.mem_univ s))
    (pow_nonneg hu.le (Fintype.card (History (n + 1))))
  rw [← gaussian_child_quotient]
  apply hqmul.trans
  dsimp [f]
  convert h using 1 <;> ring

/-- The loss from perturbing the Gaussian mean is additive, uniformly over
all actual shifts v above the comparison shift u. Only 0 < u ≤ 1 is compact. -/
theorem gaussian_gain_polynomial_stable (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, 0 ≤ R →
      (∀ s t, |γ n s t| ≤ R) → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (s : History (n + 1)) (σ : Row (n + 1)) (u v e : ℝ),
      0 < u → u ≤ 1 → u ≤ v → 0 ≤ e →
      (∀ t, |σ t| ≤ R) → (∀ t, |σ t - γ n s t| ≤ e) → ∀ b : Bool,
      c * u ^ Fintype.card (History (n + 1)) - K * e ≤
        sign b * (gaussianMass σ (shiftedChildEvent s b v) /
          gaussianMass σ (historyEvent s) - ν (n + 1) (append s b) / ν n s) := by
  obtain ⟨c, hc, hgain⟩ := gaussian_gain_polynomial n
  refine ⟨c, hc, ?_⟩
  intro R hR hγ
  obtain ⟨K, hK, hlip⟩ := gaussian_shifted_lipschitz n R 1 hR (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro s σ u v e hu hu1 huv he hσ hclose b
  have hL := hlip s σ (γ n s) hσ (hγ s) u
    (by simpa only [abs_of_pos hu] using hu1) e he hclose b
  have hG := hgain s u hu hu1 u le_rfl b
  have hM := gaussian_shifted_signed_quotient_mono s σ huv b
  have hA := abs_le.mp hL
  cases b <;> simp only [sign_false, sign_true] at hG hM ⊢ <;>
    nlinarith [hA.1, hA.2]

end MajorityDynamics.Idealized.CriticalDay
