import MajorityDynamics.GraphProcess.CoarseKernel.Main
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.CoarseKernel.Checks
open FineState History Local
variable {V : Type*} [Fintype V] {n : ℕ}

example : Finite (CoarseData V n) := inferInstance
example : Fintype (CoarseData V n) := inferInstance
example : DiscreteMeasurableSpace (CoarseData V n) := inferInstance

example (p : ℝ) (π : V → Universal.History (n+1))
    (d : V → Universal.History (n+1) → ℤ) :
    flag p π d = true ↔ ∀ v t,
      |(d v t : ℝ) - p * (partSizes π t : ℝ)| ≤
        (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ) := flag_true p π d

example (p : ℝ) (π : V → Universal.History (n+1))
    (d : V → Universal.History (n+1) → ℤ) :
    flag p π d = false ↔ ¬ ∀ v t,
      |(d v t : ℝ) - p * (partSizes π t : ℝ)| ≤
        (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ) := flag_false p π d

example (p : ℝ) (σ : State V n) :
    (rho p σ).part = σ.part ∧
    (rho p σ).edge = (fun s t => ∑ v ∈ block σ.part s, σ.deg v t) ∧
    (rho p σ).reg = decide (∀ v t,
      |(σ.deg v t : ℝ) - p * (partSizes σ.part t : ℝ)| ≤
        (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ)) := by
  refine ⟨rfl,rfl,?_⟩
  simp only [rho_reg,flag,Regular]
  congr 1

example (p : ℝ) (σ : State V n) (G : SimpleGraph V)
    (hG : degreeArray σ.part G = σ.deg) :
    rho p σ = toCoarseData σ.part G (flag p σ.part σ.deg) := rho_eq_graph p σ G hG

example (p : ℝ) (G : SimpleGraph V) (c : V → Bool) (n : ℕ)
    (s : Universal.History (n+1)) :
    (actualCoarse p G c n).edge s s =
      2 * (internalEdgeCount (actualHistory G c (n+1)) G s : ℤ) := actualCoarse_diagonal p G c n s

example (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V) :
    G ∈ E p y ↔
      (∀ v, row (degreeArray y.part G) v ∈ Universal.historyEvent (y.part v)) ∧
      (fun s t => ∑ v ∈ block y.part s, degreeArray y.part G v t) = y.edge ∧
      decide (∀ v t, |(degreeArray y.part G v t : ℝ) - p * (partSizes y.part t : ℝ)| ≤
        (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ)) = y.reg := by
  have hf : flag p y.part (degreeArray y.part G) =
      decide (∀ v t, |(degreeArray y.part G v t : ℝ) - p * (partSizes y.part t : ℝ)| ≤
        (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ)) := by
    unfold flag Regular
    congr 1
  change (_ ∧ _ ∧ flag p y.part (degreeArray y.part G) = y.reg) ↔ _
  rw [hf]
  rfl

example (p : ℝ) (y : CoarseData V n) :
    (E p y).Nonempty ↔ ∃ σ : State V n, rho p σ = y := E_nonempty_iff p y

example (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V) (hG : G ∈ E p y) :
    (actualState G (initial y) n).part = y.part ∧
    (actualState G (initial y) n).deg = degreeArray y.part G ∧
    rho p (actualState G (initial y) n) = y := raw_agreement p y G hG

example (p : unitInterval) (y : CoarseData V n) :
    Lambda p y = (cond (SimpleGraph.binomialRandom V p)
      {G | (∀ v, row (degreeArray y.part G) v ∈ Universal.historyEvent (y.part v)) ∧
        edgeTotals y.part (degreeArray y.part G) = y.edge ∧
        flag p y.part (degreeArray y.part G) = y.reg}).map
          (fun G => actualState G (fun v => Universal.bits (n+1) (y.part v) 0) n) := rfl

example (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : ∃ σ : State V n, rho p σ = y) :
    0 < SimpleGraph.binomialRandom V p (E p y) ∧
      cond (SimpleGraph.binomialRandom V p) (E p y) = uniformOn (E p y) :=
  E_conditional p y hp hp1 hy

example (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : ∃ σ : State V n, rho p σ = y)
    (σ : State V n) :
    Lambda p y {σ} = if rho p σ = y then
      (Nat.card {G : SimpleGraph V // degreeArray σ.part G = σ.deg} : ℝ≥0∞) /
        Nat.card (E p y) else 0 := Lambda_singleton p y hp hp1 hy σ

example (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : ∃ σ : State V n, rho p σ = y) :
    IsProbabilityMeasure (Lambda p y) ∧ Lambda p y {σ | rho p σ = y} = 1 ∧
      0 < Nat.card (E p y) :=
  ⟨Lambda_probability p y hp hp1 hy,Lambda_support p y hp hp1 hy,E_card_pos p y hy⟩

example (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : ∃ σ : State V n, rho p σ = y) :
    (y.reg = true → Lambda p y {σ | Regular p σ.part σ.deg} = 1) ∧
    (y.reg = false → Lambda p y {σ | ¬ Regular p σ.part σ.deg} = 1) :=
  ⟨Lambda_regularity p y hp hp1 hy,Lambda_irregularity p y hp hp1 hy⟩

example (p : unitInterval) (y : CoarseData V n) (B : Set (CoarseData V (n+1))) :
    Kbar p y B = ∑ σ : State V n,
      Lambda p y {σ} * FineKernel.K σ {τ | rho p τ ∈ B} := Kbar_apply p y B

example (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : ∃ σ : State V n, rho p σ = y) :
    IsProbabilityMeasure (Kbar p y) := Kbar_probability p y hp hp1 hy

example (p : unitInterval) (y : CoarseData V n) (hy : ¬ ∃ σ : State V n, rho p σ = y) :
    Lambda p y = 0 ∧ Kbar p y = 0 := ⟨Lambda_unattainable p y hy,Kbar_unattainable p y hy⟩

example (p : unitInterval) (c : V → Bool) (y : CoarseData V n)
    (hpos : 0 < SimpleGraph.binomialRandom V p {G | rho p (actualState G c n) = y}) :
    (∀ v, c v = Universal.bits (n+1) (y.part v) 0) ∧
    {G | rho p (actualState G c n) = y} = E p y ∧
    (cond (SimpleGraph.binomialRandom V p) {G | rho p (actualState G c n) = y}).map
      (fun G => actualState G c n) = Lambda p y := by
  have hc := compatible_of_positive p c y _ hpos
  exact ⟨hc,currentEvent_eq_E p c y hc,current_fine_law p c y hc⟩

example (p : unitInterval) (c : V → Bool) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p {G | rho p (actualState G c n) = y}) :
    (∃ σ : State V n, rho p σ = y) ∧ ∀ B : Set (CoarseData V (n+1)),
      cond (SimpleGraph.binomialRandom V p) {G | rho p (actualState G c n) = y}
        {G | rho p (actualState G c (n+1)) ∈ B} =
      ∑ σ : State V n, Lambda p y {σ} * FineKernel.K σ {τ | rho p τ ∈ B} := by
  refine ⟨attainable_of_positive p c y _ hpos,fun B => ?_⟩
  exact (coarse_transition p c y hp hp1 hpos B).trans (Kbar_apply p y B)

/-- Day one with N arbitrary, including N=0. -/
example (N : ℕ) (p : unitInterval) (c : Fin N → Bool) (y : CoarseData (Fin N) 0)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom (Fin N) p {G | rho p (actualState G c 0) = y}) :
    (cond (SimpleGraph.binomialRandom (Fin N) p) {G | rho p (actualState G c 0) = y}).map
      (fun G => rho p (actualState G c 1)) = Kbar p y := coarse_transition_law p c y hp hp1 hpos

end MajorityDynamics.GraphProcess.CoarseKernel.Checks

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.coarseFinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.coarseFinite

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.flag

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.rho

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.E

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.raw_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.raw_agreement

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.E_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.E_nonempty_iff

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.E_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.E_conditional

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Lambda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Lambda

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Lambda_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Lambda_singleton

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Lambda_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Lambda_probability

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Lambda_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Lambda_support

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Lambda_regularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Lambda_regularity

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Lambda_irregularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Lambda_irregularity

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Lambda_unattainable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Lambda_unattainable

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Kbar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Kbar

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Kbar_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Kbar_apply

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Kbar_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Kbar_probability

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.Kbar_unattainable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.Kbar_unattainable

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.compatible_of_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.compatible_of_positive

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.current_fine_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.current_fine_law

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.proposition_2_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.proposition_2_5

/-- info: 'MajorityDynamics.GraphProcess.CoarseKernel.coarse_transition_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.CoarseKernel.coarse_transition_law
