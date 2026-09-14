import MajorityDynamics.Idealized.Process.SolvabilityCore
import MajorityDynamics.Idealized.RowLimits.ContractBridges
import MajorityDynamics.Idealized.RowLimits.Smooth

/-! Uniform mean-equation stability for every row at one fixed universal day.
The ambient coordinate norm remains the manuscript's infinity norm, while
the strong-bijection theorem is used with its actual Euclidean norm. -/

noncomputable section
open Set
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process
open Universal Analysis

private theorem finite_positive_lower_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  have aux : ∀ s : Finset ι, ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hbound⟩ := ih
      refine ⟨min (f a) c, lt_min (hf a) hc, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound i hi)
  obtain ⟨c, hc, hbound⟩ := aux Finset.univ
  exact ⟨c, hc, fun i => hbound i (Finset.mem_univ i)⟩

/-- Constants are uniform over the finite family of all histories. -/
theorem stable_mean_inverse (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧ (∀ s t, |γ n s t| ≤ R) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → ∀ s : History (n + 1),
      ∀ g : Row (n + 1) → Row (n + 1), Continuous g →
        (∀ σ, (∀ t, |σ t| ≤ R) → ∀ t, |g σ t - meanMap s (ν n) σ t| ≤ ε) →
        ∀ y : Row (n + 1), (∀ t, |y t - ν n t * μ n s t| ≤ ε) →
        ∃ σ : Row (n + 1), g σ = y ∧ (∀ t, |σ t| ≤ R) ∧
          ∀ t, |σ t - γ n s t| ≤ C * ε := by
  classical
  have hdim : 1 ≤ Fintype.card (Fin (n + 1) → Bool) := Fintype.card_pos
  have hsingle (s : History (n + 1)) := stable_inverse_coordinates hdim
    (meanBijection s (ν n) (ν_positive n)) (γ n s)
  choose R _hR δ hδ C _hC hsolve using hsingle
  let R' := 1 + (∑ s, |R s|) + ∑ s, ∑ t, |γ n s t|
  let C' := 1 + ∑ s, |C s|
  have hR' : 0 < R' := by dsimp [R']; positivity
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hRs : ∀ s, R s ≤ R' := by
    intro s
    have hsum := Finset.single_le_sum (fun i _ => abs_nonneg (R i)) (Finset.mem_univ s)
    have hγsum : 0 ≤ ∑ s, ∑ t, |γ n s t| := by positivity
    have hRle := le_abs_self (R s)
    dsimp [R']
    linarith
  have hCs : ∀ s, C s ≤ C' := by
    intro s
    have hsum := Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_univ s)
    have hCle := le_abs_self (C s)
    dsimp [C']
    linarith
  obtain ⟨δ', hδ', hδs⟩ := finite_positive_lower_bound δ hδ
  refine ⟨R', hR', ?_, δ', hδ', C', hC', ?_⟩
  · intro s t
    have h1 := Finset.single_le_sum (fun j _ => abs_nonneg (γ n s j)) (Finset.mem_univ t)
    have h2 := Finset.single_le_sum
      (fun i _ => show 0 ≤ ∑ j, |γ n i j| by positivity) (Finset.mem_univ s)
    have h3 : 0 ≤ ∑ s, |R s| := by positivity
    dsimp [R']
    linarith
  · intro ε hε hεδ s g hg hgclose y hy
    obtain ⟨σ, hσ, hσR, hσγ⟩ := hsolve s ε hε (hεδ.trans_le (hδs s)) g hg
      (fun z hz t => by
        simpa only [meanBijection_toFun] using
          hgclose z (fun j => (hz j).trans (hRs s)) t)
      y (fun t => by simpa only [meanBijection_toFun, γ_defining, PiLp.toLp_apply] using hy t)
    exact ⟨σ, hσ, fun t => (hσR t).trans (hRs s),
      fun t => (hσγ t).trans (mul_le_mul_of_nonneg_right (hCs s) hε.le)⟩

/-- The actual centered and normalized binomial mean map in Step 2. -/
def normalizedMeanMap {n : ℕ} (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (σ : Row (n + 1)) : Row (n + 1) :=
  WithLp.toLp 2 (fun t =>
    (RowLimits.binomialMean N p sizes s (Local.historySupport sizes s) t σ -
      (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N))

theorem normalizedMeanMap_continuous {n : ℕ} (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) :
    Continuous (normalizedMeanMap N p sizes s) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro t
  exact (((RowLimits.smooth_quantities N p sizes s).history_mean t).continuous.sub
    continuous_const).div_const _

end MajorityDynamics.Idealized.Process
