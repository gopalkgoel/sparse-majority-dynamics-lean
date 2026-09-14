import MajorityDynamics.GraphProcess.LocalTheorem.Assembly

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.LocalTheorem
universe u

/-- Real-density paper formulation. Interior density follows from the original
sparse window, and is returned rather than imposed as an extra hypothesis. -/
def LocalCoarseTransitionRealTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∃ hp : 0 < p ∧ p < 1,
    let pI : unitInterval := ⟨p,hp.1.le,hp.2.le⟩
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
    IsProbabilityMeasure (CoarseKernel.Kbar pI y) ∧
    (CoarseKernel.Kbar pI y).real {z | ¬ LocalTransition.LocalSuccess y q p C z} ≤ ε ∧
    1-ε ≤ (CoarseKernel.Kbar pI y).real {z | LocalTransition.LocalSuccess y q p C z}

theorem real_of_unit {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (h : LocalCoarseTransitionTheorem.{u} θ T φ n) :
    LocalCoarseTransitionRealTheorem.{u} θ T φ n := by
  obtain ⟨C,hC,h⟩ := h
  obtain ⟨Nr,hr⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1/2) (by norm_num) (M := 1) zero_lt_one
  refine ⟨C,hC,?_⟩
  intro ε hε
  obtain ⟨N₀,h₀⟩ := h ε hε
  refine ⟨max N₀ Nr,?_⟩
  intro N hN V inst hcard p hlo hhi
  have hw := hr N (by omega) p hlo hhi
  have hp : 0 < p ∧ p < 1 :=
    ⟨hw.2.1, lt_of_le_of_lt hw.2.2.2.2 (by norm_num)⟩
  refine ⟨hp,?_⟩
  dsimp only
  intro y q ha
  exact h₀ N (by omega) V hcard ⟨p,hp.1.le,hp.2.le⟩ hlo hhi y q ha

end MajorityDynamics.GraphProcess.LocalTheorem
