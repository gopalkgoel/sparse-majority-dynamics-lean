import MajorityDynamics.Probability.RandomOpinionsReduction.RealDensity
import Mathlib.Combinatorics.SimpleGraph.Maps

/-! # Finite vertex transport
All transported laws are identified with the actual independent product laws.
The update on V is defined directly by the simultaneous neighborhood majority.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.RandomOpinionsReduction

def uniformColoringLawV (V : Type*) [Fintype V] : Measure (V → Bool) :=
  Measure.pi (fun _ : V => fairBitLaw)

instance (V : Type*) [Fintype V] : IsProbabilityMeasure (uniformColoringLawV V) := by
  unfold uniformColoringLawV
  infer_instance

def jointLawV (V : Type*) [Fintype V] (p : unitInterval) : Measure ((V → Bool) × SimpleGraph V) :=
  (uniformColoringLawV V).prod (SimpleGraph.binomialRandom V p)

def nextColoringV {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → Bool) : V → Bool := by
  classical
  exact fun v =>
    let s : ℤ := ∑ w : V, if G.Adj v w then Paper.opinion (c w) else 0
    if 0 < s then false else if s < 0 then true else c v

def coloringOnDayV {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → Bool) (t : ℕ) : V → Bool :=
  (nextColoringV G)^[t-1] c

def consensusEventV (V : Type*) [Fintype V] (θ : ℝ) : Set ((V → Bool) × SimpleGraph V) :=
  {z | ∃ b : Bool, ∀ t : ℕ, Paper.convergenceDay θ ≤ t → ∀ v, coloringOnDayV z.2 z.1 t v = b}

def coloringEquiv {V W : Type*} (e : V ≃ W) : (V → Bool) ≃ (W → Bool) where
  toFun c := c ∘ e.symm
  invFun c := c ∘ e
  left_inv c := by funext v; simp
  right_inv c := by funext w; simp

theorem coloring_law_transport {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W) :
    (uniformColoringLawV V).map (coloringEquiv e) = uniformColoringLawV W := by
  classical
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply .of_discrete (measurableSet_singleton _)]
  have he : (coloringEquiv e) ⁻¹' {c} = {(coloringEquiv e).symm c} := by
    ext d
    simp [Equiv.eq_symm_apply]
  rw [he]
  simp [uniformColoringLawV, Measure.pi_singleton, fairBitLaw_singleton, Fintype.card_congr e]

theorem graph_law_transport {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W) (p : unitInterval) :
    (SimpleGraph.binomialRandom V p).map e.simpleGraph = SimpleGraph.binomialRandom W p := by
  classical
  apply Measure.ext_of_singleton
  intro G
  rw [Measure.map_apply .of_discrete (measurableSet_singleton _)]
  have hpre : e.simpleGraph ⁻¹' {G} = {e.simpleGraph.symm G} := by
    ext H
    change e.simpleGraph H = G ↔ H = e.simpleGraph.symm G
    exact e.simpleGraph.eq_symm_apply.symm
  rw [hpre, SimpleGraph.binomialRandom_singleton, SimpleGraph.binomialRandom_singleton]
  have he : (e.simpleGraph.symm G).edgeSet.ncard = G.edgeSet.ncard := by
    exact Nat.card_congr (SimpleGraph.Iso.comap e G).mapEdgeSet
  rw [he, Nat.card_congr e]

theorem joint_law_transport {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W) (p : unitInterval) :
    (jointLawV V p).map (Prod.map (coloringEquiv e) e.simpleGraph) = jointLawV W p := by
  rw [jointLawV, ← Measure.map_prod_map _ _ .of_discrete .of_discrete,
    coloring_law_transport, graph_law_transport]
  rfl

theorem nextColoring_transport {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : SimpleGraph V) (c : V → Bool) :
    nextColoringV (e.simpleGraph G) (coloringEquiv e c) = coloringEquiv e (nextColoringV G c) := by
  classical
  funext w
  have hs : (∑ z : W, if (e.simpleGraph G).Adj w z then
      Paper.opinion (coloringEquiv e c z) else 0) =
      ∑ v : V, if G.Adj (e.symm w) v then Paper.opinion (c v) else 0 := by
    simpa [Equiv.simpleGraph, coloringEquiv] using
      (e.sum_comp (fun z : W => if (e.simpleGraph G).Adj w z then
        Paper.opinion (coloringEquiv e c z) else 0)).symm
  change (if 0 < _ then false else if _ < 0 then true else _) = _
  rw [hs]
  rfl

theorem coloringOnDay_transport {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : SimpleGraph V) (c : V → Bool) (t : ℕ) :
    coloringOnDayV (e.simpleGraph G) (coloringEquiv e c) t =
      coloringEquiv e (coloringOnDayV G c t) := by
  unfold coloringOnDayV
  generalize t-1 = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, nextColoring_transport]

theorem coloringOnDay_fin {N : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N) (t : ℕ) :
    coloringOnDayV G c t = Paper.coloringOnDay G c t := rfl

theorem consensus_transport {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W) (θ : ℝ) :
    Prod.map (coloringEquiv e) e.simpleGraph ⁻¹' consensusEventV W θ = consensusEventV V θ := by
  ext ⟨c,G⟩
  change (∃ b, ∀ t, Paper.convergenceDay θ ≤ t → ∀ w,
    coloringOnDayV (e.simpleGraph G) (coloringEquiv e c) t w = b) ↔ _
  simp only [coloringOnDay_transport]
  constructor
  · rintro ⟨b,h⟩
    exact ⟨b, fun t ht v => by simpa [coloringEquiv] using h t ht (e v)⟩
  · rintro ⟨b,h⟩
    exact ⟨b, fun t ht w => h t ht (e.symm w)⟩

theorem coloringV_coordinates_independent (V : Type*) [Fintype V] :
    ProbabilityTheory.iIndepFun (fun v (c : V → Bool) => c v) (uniformColoringLawV V) :=
  ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem coloringV_coordinate_law (V : Type*) [Fintype V] (v : V) :
    (uniformColoringLawV V).map (fun c => c v) = fairBitLaw :=
  (measurePreserving_eval (fun _ : V => fairBitLaw) v).map_eq

theorem graph_coloringV_independent (V : Type*) [Fintype V] (p : unitInterval) :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd (jointLawV V p) :=
  ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id

def RandomOpinionsFiniteTheorem : Prop :=
  ∀ θ T : ℝ, 1/2 < θ → θ < 1 → 1 < T → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Type) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, Paper.densityRange θ T N p →
        jointLawV V p (consensusEventV V θ)ᶜ ≤ ENNReal.ofReal ε

theorem random_opinions_finite_of_main (main : Paper.MainTheorem) : RandomOpinionsFiniteTheorem := by
  intro θ T hlo hhi hT ε hε
  obtain ⟨M,hM⟩ := random_opinions_of_main main θ T hlo hhi hT ε hε
  refine ⟨M, ?_⟩
  intro N hN V _ hV p hp
  let e : Fin N ≃ V := (Fintype.equivFinOfCardEq hV).symm
  rw [← joint_law_transport e p, Measure.map_apply .of_discrete (Set.toFinite _).measurableSet,
    Set.preimage_compl, consensus_transport]
  exact hM N hN p hp

end MajorityDynamics.Probability.RandomOpinionsReduction
