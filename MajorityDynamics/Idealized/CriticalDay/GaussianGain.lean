import MajorityDynamics.Idealized.RowLimits.EventsGaussian
import MajorityDynamics.Universal.Nondegeneracy

/-! A positive Gaussian slab gives a uniform signed child gain for every
positive decision shift bounded away from zero. -/
noncomputable section
open Set MeasureTheory
open MajorityDynamics.Universal MajorityDynamics.Analysis
namespace MajorityDynamics.Idealized.CriticalDay
open RowLimits
variable {n : ℕ}

def gainSlab (s : History (n + 1)) (a : ℝ) : Set (Row (n + 1)) :=
  historyCone s ∩ {x | -a < imbalance (Fin.last n) x ∧ imbalance (Fin.last n) x < 0}

theorem gainSlab_open (s : History (n + 1)) (a : ℝ) : IsOpen (gainSlab s a) :=
  (historyCone_isOpen s).inter ((isOpen_lt continuous_const (imbalance_continuous _)).inter
    (isOpen_lt (imbalance_continuous _) continuous_const))

theorem gainSlab_nonempty (s : History (n + 1)) {a : ℝ} (ha : 0 < a) :
    (gainSlab s a).Nonempty := by
  let d : ℝ := Fintype.card (History (n + 1))
  have hd : 0 < d := history_card_pos (n + 1)
  let v : Fin (n + 1) → ℝ := Fin.snoc
    (fun r => sign (bits (n + 1) s r.succ)) (-a / (2 * d))
  refine ⟨synthesize v, ?_, ?_⟩
  · rw [mem_historyCone]
    intro r
    rw [imbalance_synthesize]
    simp only [v, Fin.snoc_castSucc]
    nlinarith [sign_sq (bits (n + 1) s r.succ)]
  · change -a < imbalance (Fin.last n) (synthesize v) ∧ imbalance (Fin.last n) (synthesize v) < 0
    rw [imbalance_synthesize]
    simp only [v, Fin.snoc_last]
    have he : d * (-a / (2 * d)) = -a / 2 := by field_simp
    change -a < d * (-a / (2*d)) ∧ d * (-a / (2*d)) < 0
    rw [he]
    constructor <;> linarith

theorem gainSlab_mass_pos (s : History (n + 1)) {a : ℝ} (ha : 0 < a) :
    0 < (rowLaw (ν n) (γ n s)).real (gainSlab s a) := by
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  exact (ConditionalGaussian.gaussianLaw_mass_pos _ (covariance_posDef _ (ν_positive n)) _ _
    (gainSlab_open s a) (gainSlab_nonempty s ha)).ne'

private theorem cone_event {s : History (n+1)} {x : Row (n+1)}
    (hx : x ∈ historyCone s) : x ∈ historyEvent s := by
  intro r
  exact Or.inl ((mem_historyCone s x).mp hx r)

private theorem decision_false_mono {c : Bool} {x y : ℝ} (hxy : x ≤ y)
    (hx : decision c false x) : decision c false y := by
  simp only [decision, sign_false, one_mul] at hx ⊢
  rcases hx with hx | ⟨hx, hc⟩
  · exact Or.inl (hx.trans_le hxy)
  · rcases lt_or_eq_of_le hxy with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hc⟩

theorem gaussian_signed_gain (s : History (n+1)) {a u : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (b : Bool) :
    (rowLaw (ν n) (γ n s)).real (gainSlab s a) ≤
      sign b * (gaussianMass (γ n s) (shiftedChildEvent s b u) -
        gaussianMass (γ n s) (childEvent s b)) := by
  let μ := rowLaw (ν n) (γ n s)
  have hu : 0 ≤ u := le_trans ha.le hau
  have slab_false {x : Row (n+1)} (hx : x ∈ gainSlab s a) :
      decision (last s) false (imbalance (Fin.last n) x + u) := by
    apply Or.inl
    simp only [sign_false, one_mul]
    linarith [hx.2.1]
  have slab_not_false {x : Row (n+1)} (hx : x ∈ gainSlab s a) :
      ¬ decision (last s) false (imbalance (Fin.last n) x) := by
    simp only [decision, sign_false, one_mul]
    rcases hx with ⟨_, hlo, hhi⟩
    intro h
    rcases h with h | ⟨h, _⟩ <;> linarith
  cases b
  · have hdis : Disjoint (childEvent s false) (gainSlab s a) := by
      rw [Set.disjoint_left]
      intro x hx hs
      exact slab_not_false hs hx.2
    have hsub : childEvent s false ∪ gainSlab s a ⊆ shiftedChildEvent s false u := by
      intro x hx
      rcases hx with hx | hx
      · exact ⟨hx.1, decision_false_mono (by linarith) hx.2⟩
      · exact ⟨cone_event hx.1, slab_false hx⟩
    have hm := measureReal_mono (μ := μ) hsub
    rw [measureReal_union hdis (gainSlab_open s a).measurableSet] at hm
    change μ.real (gainSlab s a) ≤ 1 * (μ.real _ - μ.real _)
    linarith
  · have hdis : Disjoint (shiftedChildEvent s true u) (gainSlab s a) := by
      rw [Set.disjoint_left]
      intro x hx hs
      exact (decision_complement _ _).mp hx.2 (slab_false hs)
    have hsub : shiftedChildEvent s true u ∪ gainSlab s a ⊆ childEvent s true := by
      intro x hx
      rcases hx with hx | hx
      · refine ⟨hx.1, (decision_complement _ _).mpr ?_⟩
        intro h
        exact (decision_complement _ _).mp hx.2 (decision_false_mono (by linarith) h)
      · exact ⟨cone_event hx.1, (decision_complement _ _).mpr (slab_not_false hx)⟩
    have hm := measureReal_mono (μ := μ) hsub
    rw [measureReal_union hdis (gainSlab_open s a).measurableSet] at hm
    change μ.real (gainSlab s a) ≤ -1 * (μ.real _ - μ.real _)
    linarith

theorem gaussian_child_quotient (s : History (n+1)) (b : Bool) :
    gaussianMass (γ n s) (childEvent s b) / gaussianMass (γ n s) (historyEvent s) =
      ν (n+1) (append s b) / ν n s := by
  rw [ν_recursion]
  have hν := (ν_positive n s).ne'
  rw [mul_div_cancel_left₀ _ hν]
  unfold gaussianMass branchProbability
  rw [measure_congr (childEvent_ae_eq_cone s b (ν n) (ν_positive n) (γ n s)),
    measure_congr (historyEvent_ae_eq_cone s (ν n) (ν_positive n) (γ n s))]
  rfl

theorem gaussian_gain_uniform (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ (s : History (n+1)) (u : ℝ), a ≤ u → ∀ b : Bool,
      ζ ≤ sign b * (gaussianMass (γ n s) (shiftedChildEvent s b u) /
        gaussianMass (γ n s) (historyEvent s) - ν (n+1) (append s b) / ν n s) := by
  classical
  let f : History (n+1) → ℝ := fun s =>
    (rowLaw (ν n) (γ n s)).real (gainSlab s a) /
      gaussianMass (γ n s) (historyEvent s)
  have hden (s : History (n+1)) : 0 < gaussianMass (γ n s) (historyEvent s) :=
    universal_history_probability_pos n s
  have hf (s : History (n+1)) : 0 < f s := div_pos (gainSlab_mass_pos s ha) (hden s)
  have aux : ∀ S : Finset (History (n+1)), ∃ c : ℝ, 0 < c ∧ ∀ s ∈ S, c ≤ f s := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert s S _ ih =>
      obtain ⟨c, hc, hb⟩ := ih
      refine ⟨min (f s) c, lt_min (hf s) hc, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb t ht)
  obtain ⟨ζ, hζ, hb⟩ := aux Finset.univ
  refine ⟨ζ, hζ, ?_⟩
  intro s u hu b
  apply (hb s (Finset.mem_univ _)).trans
  rw [← gaussian_child_quotient]
  have h := div_le_div_of_nonneg_right (gaussian_signed_gain s ha hu b) (hden s).le
  dsimp [f]
  convert h using 1
  ring

end MajorityDynamics.Idealized.CriticalDay
