import MajorityDynamics.GraphProcess.CoarseKernel.Basic
noncomputable section
open MeasureTheory ProbabilityTheory
open unitInterval (toNNReal)
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.CoarseKernel
open FineState History Local
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

theorem total_edges (π : V → Universal.History (n+1)) (G : SimpleGraph V) :
    ∑ s, ∑ t, edgeTotals π (degreeArray π G) s t = 2 * (G.edgeSet.ncard : ℤ) := by
  simp only [edgeTotals]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := block π _)]
  simp_rw [sum_degreeArray]
  rw [sum_block, ← Nat.cast_sum]
  have h := G.sum_degrees_eq_twice_card_edges
  simpa only [Nat.cast_mul, Nat.cast_ofNat, SimpleGraph.edgeFinset,
    Set.ncard_eq_toFinset_card'] using congrArg (Nat.cast : ℕ → ℤ) h

theorem E_same_edges (p : ℝ) (y : CoarseData V n) (G H : E p y) :
    G.val.edgeSet.ncard = H.val.edgeSet.ncard := by
  have hg := total_edges y.part G.val
  have hh := total_edges y.part H.val
  rw [G.property.2.1] at hg
  rw [H.property.2.1] at hh
  omega

/-- Actual Bernoulli conditioning on the coarse event has constant graph weights. -/
theorem E_conditional (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) :
    0 < SimpleGraph.binomialRandom V p (E p y) ∧
      cond (SimpleGraph.binomialRandom V p) (E p y) = uniformOn (E p y) := by
  obtain ⟨G,hG⟩ := (E_nonempty_iff p y).mpr hy
  apply conditional_eq_uniform _ _ ⟨G,hG⟩
    ((toNNReal p : ℝ≥0∞)^G.edgeSet.ncard *
      (toNNReal (unitInterval.symm p) : ℝ≥0∞)^((Nat.card V).choose 2 - G.edgeSet.ncard))
    (bernoulli_weight_ne_zero p hp hp1 _ _)
  intro H hH
  rw [SimpleGraph.binomialRandom_singleton, E_same_edges p y ⟨H,hH⟩ ⟨G,hG⟩]

/-- The total graph map is the actual state for the partition's canonical coloring.
On the conditioning event, `actual_eq_raw` identifies its literal raw state. -/
def Lambda (p : unitInterval) (y : CoarseData V n) : Measure (State V n) :=
  (cond (SimpleGraph.binomialRandom V p) (E p y)).map (fun G => actualState G (initial y) n)

theorem Lambda_uniform (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) :
    Lambda p y = (uniformOn (E p y)).map (fun G => actualState G (initial y) n) := by
  rw [Lambda,(E_conditional p y hp hp1 hy).2]

theorem Lambda_probability (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) :
    IsProbabilityMeasure (Lambda p y) := by
  have h := (E_conditional p y hp hp1 hy).1
  have : IsProbabilityMeasure (cond (SimpleGraph.binomialRandom V p) (E p y)) :=
    cond_isProbabilityMeasure h.ne'
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem canonical_compatible (y : CoarseData V n) : CompatibleInitial y.part (initial y) := fun _ => rfl

theorem E_fiber_inter (p : ℝ) (y : CoarseData V n) (σ : State V n) :
    E p y ∩ {G | actualState G (initial y) n = σ} =
      if rho p σ = y then FineKernel.realizerEvent σ else ∅ := by
  by_cases h : rho p σ = y
  · rw [if_pos h]
    have hp : σ.part = y.part := congrArg CoarseData.part h
    have hc : CompatibleInitial σ.part (initial y) := by rw [hp]; exact canonical_compatible y
    ext G
    constructor
    · rintro ⟨_,hs⟩; exact ((actualState_eq_iff G _ σ).mp hs).2
    · intro hG
      have hs := reconstruction_state σ G (initial y) hG hc
      exact ⟨actual_mem_E p y G _ (hs ▸ h),hs⟩
  · rw [if_neg h]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro G ⟨hG,hs⟩
    exact h (hs ▸ (E_iff_actual p y G _ (canonical_compatible y)).mp hG)

/-- Exact whole-graph realization counts; no independence after coarse conditioning is assumed. -/
theorem Lambda_singleton (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) (σ : State V n) :
    Lambda p y {σ} = if rho p σ = y then
      (Nat.card (FineKernel.realizerEvent σ) : ℝ≥0∞) / Nat.card (E p y) else 0 := by
  rw [Lambda_uniform p y hp hp1 hy, Measure.map_apply (measurable_of_countable _)
    (MeasurableSet.singleton _), uniform_apply]
  change ((E p y ∩ {G | actualState G (initial y) n = σ}).ncard : ℝ≥0∞) /
    (E p y).ncard = _
  rw [E_fiber_inter]
  split_ifs
  · rfl
  · simp only [Set.ncard_empty, Nat.cast_zero, ENNReal.zero_div]

theorem E_card_pos (p : ℝ) (y : CoarseData V n) (hy : pAttainable p y) :
    0 < Nat.card (E p y) := by
  have : Nonempty (E p y) := (E_nonempty_iff p y).mpr hy |>.to_subtype
  exact Nat.card_pos

theorem Lambda_support (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) :
    Lambda p y {σ | rho p σ = y} = 1 := by
  rw [Lambda, Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  have he : {G | rho (p:ℝ) (actualState G (initial y) n) = y} = E p y := by
    ext G; exact (E_iff_actual p y G _ (canonical_compatible y)).symm
  change cond (SimpleGraph.binomialRandom V p) (E p y)
    {G | rho (p:ℝ) (actualState G (initial y) n) = y} = 1
  rw [he]
  exact cond_apply_self (E_conditional p y hp hp1 hy).1.ne' (measure_ne_top _ _)

theorem Lambda_regularity (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) (hr : y.reg = true) :
    Lambda p y {σ | Regular p σ.part σ.deg} = 1 := by
  have := Lambda_probability p y hp hp1 hy
  apply le_antisymm (measure_mono (Set.subset_univ _) |>.trans_eq measure_univ)
  rw [← Lambda_support p y hp hp1 hy]
  apply measure_mono
  intro σ hσ
  apply (flag_true p σ.part σ.deg).mp
  exact (congrArg CoarseData.reg hσ).trans hr

theorem Lambda_irregularity (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) (hr : y.reg = false) :
    Lambda p y {σ | ¬ Regular p σ.part σ.deg} = 1 := by
  have := Lambda_probability p y hp hp1 hy
  apply le_antisymm (measure_mono (Set.subset_univ _) |>.trans_eq measure_univ)
  rw [← Lambda_support p y hp hp1 hy]
  apply measure_mono
  intro σ hσ
  apply (flag_false p σ.part σ.deg).mp
  exact (congrArg CoarseData.reg hσ).trans hr

theorem Lambda_unattainable (p : unitInterval) (y : CoarseData V n) (hy : ¬ pAttainable p y) :
    Lambda p y = 0 := by
  have he : E p y = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun h => hy ((E_nonempty_iff p y).mp h))
  simp [Lambda,he]

end MajorityDynamics.GraphProcess.CoarseKernel
