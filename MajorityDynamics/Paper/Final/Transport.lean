import MajorityDynamics.Probability.RandomOpinionsReduction.Main

/-! Fixed initial colorings on arbitrary finite vertex sets, under the actual
binomial graph law and simultaneous majority dynamics. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace MajorityDynamics.Paper
open Probability.RandomOpinionsReduction

def plusCountV {V : Type*} [Fintype V] (c : V → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun v => c v = false).card

def initialBiasV {V : Type*} [Fintype V] (τ : ℝ) (c : V → Bool) : Prop :=
  plusCountV c = Fintype.card V / 2 + ⌊τ * Real.sqrt (Fintype.card V : ℝ)⌋₊

def successEventV {V : Type*} [Fintype V] (θ : ℝ) (c : V → Bool) :
    Set (SimpleGraph V) :=
  {G | ∀ v, coloringOnDayV G c (convergenceDay θ) v = false}

theorem plusCount_transport {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (c : V → Bool) : plusCountV (coloringEquiv e c) = plusCountV c := by
  classical
  unfold plusCountV
  apply Finset.card_bij (fun w _ => e.symm w)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩
  · intro w hw z hz h
    exact e.symm.injective h
  · intro v hv
    refine ⟨e v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    simpa [coloringEquiv] using (Finset.mem_filter.mp hv).2

theorem successEvent_transport {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (θ : ℝ) (c : V → Bool) :
    e.simpleGraph ⁻¹' successEventV θ (coloringEquiv e c) = successEventV θ c := by
  ext G
  change (∀ w, coloringOnDayV (e.simpleGraph G) (coloringEquiv e c)
    (convergenceDay θ) w = false) ↔ _
  rw [coloringOnDay_transport]
  constructor
  · intro h v
    simpa [coloringEquiv] using h (e v)
  · intro h w
    exact h (e.symm w)

def MainFiniteTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (V : Type) [Fintype V], Fintype.card V = N →
      ∀ (p : unitInterval) (τ : ℝ) (c : V → Bool),
        densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBiasV τ c →
          SimpleGraph.binomialRandom V p (successEventV θ c)ᶜ ≤ ENNReal.ofReal ε

theorem main_finite_of_main (hmain : MainTheorem) : MainFiniteTheorem := by
  intro θ T hlo hhi hT ε hε
  obtain ⟨M, hM⟩ := hmain θ T hlo hhi hT ε hε
  refine ⟨M, ?_⟩
  intro N hN V _ hV p τ c hp hτ hτT hc
  let e : Fin N ≃ V := (Fintype.equivFinOfCardEq hV).symm
  let d : Coloring N := coloringEquiv e.symm c
  have hd : initialBias N τ d := by
    have hcount := plusCount_transport e.symm c
    change plusCountV d = _
    rw [hcount]
    simpa [initialBiasV, hV] using hc
  have hcd : coloringEquiv e d = c := by
    funext v
    simp [d, coloringEquiv]
  have hevent : e.simpleGraph ⁻¹' successEventV θ c = successEvent θ d := by
    rw [← hcd, successEvent_transport]
    rfl
  rw [← graph_law_transport e p, Measure.map_apply .of_discrete
    (Set.toFinite _).measurableSet, Set.preimage_compl, hevent]
  exact hM N hN p τ d hp hτ hτT hd

def MainFiniteRealTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (V : Type) [Fintype V], Fintype.card V = N →
      ∀ (p τ : ℝ) (c : V → Bool),
        T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-θ) →
        T⁻¹ ≤ τ → τ ≤ T → initialBiasV τ c →
        ∃ hp : 0 < p ∧ p < 1,
          SimpleGraph.binomialRandom V ⟨p, hp.1.le, hp.2.le⟩
            (successEventV θ c)ᶜ ≤ ENNReal.ofReal ε

theorem main_finite_real_of_main (hmain : MainTheorem) : MainFiniteRealTheorem := by
  intro θ T hlo hhi hT ε hε
  obtain ⟨M, hM⟩ := main_finite_of_main hmain θ T hlo hhi hT ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_density_in_unitInterval θ T (by linarith) (by linarith))
  refine ⟨max M K, ?_⟩
  intro N hN V _ hV p τ c hp₀ hp₁ hτ hτT hc
  have hp := hK N ((le_max_right _ _).trans hN) p hp₀ hp₁
  exact ⟨hp, hM N ((le_max_left _ _).trans hN) V hV
    ⟨p, hp.1.le, hp.2.le⟩ τ c ⟨hp₀, hp₁⟩ hτ hτT hc⟩

end MajorityDynamics.Paper
