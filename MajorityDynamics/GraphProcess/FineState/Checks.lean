import MajorityDynamics.GraphProcess.FineState.Main

/-! Independently expanded contracts and foundational axiom checks. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.FineState
open Universal History

example (N n : ℕ) (σ : State (Fin N) n) (G : Paper.Graph N) (c : Paper.Coloring N)
    (hG : degreeArray σ.part G = σ.deg)
    (hc : ∀ v, c v = bits (n + 1) (σ.part v) 0)
    (r : Fin (n + 1)) (v : Fin N) :
    Paper.coloringOnDay G c (r.val + 1) v = bits (n + 1) (σ.part v) r :=
  reconstruction σ G c hG hc r v

example (N n : ℕ) (σ : State (Fin N) n) (G : Paper.Graph N) (c : Paper.Coloring N)
    (hG : degreeArray σ.part G = σ.deg)
    (hc : ∀ v, c v = bits (n + 1) (σ.part v) 0)
    (r : ℕ) (hr : 1 ≤ r ∧ r ≤ n + 1) (s : Universal.History (n + 1))
    (v : Fin N) (hv : σ.part v = s) :
    Paper.opinion (Paper.coloringOnDay G c r v) =
      Paper.opinion (bits (n + 1) s ⟨r - 1, by omega⟩) :=
  fact_state_reconstruction σ G c hG hc r hr s v ((mem_block _ _ _).mpr hv)

example (V : Type*) [Fintype V] (n : ℕ) (σ : State V n) (G : SimpleGraph V)
    (c : V → Bool) : actualState G c n = σ ↔
      (∀ v, c v = bits (n + 1) (σ.part v) 0) ∧ degreeArray σ.part G = σ.deg :=
  actualState_eq_iff G c σ

example (V : Type*) [Fintype V] (n : ℕ) (σ : State V n) (c : V → Bool)
    (hc : ∀ v, c v = bits (n + 1) (σ.part v) 0) :
    {G : SimpleGraph V | actualState G c n = σ} =
      {G : SimpleGraph V | degreeArray σ.part G = σ.deg} := conditioning_event σ c hc

example (V : Type*) [Fintype V] (n : ℕ) : Fintype (State V n) := inferInstance

example (V : Type*) [Fintype V] (n : ℕ) (σ : State V n) :
    ∃ G : SimpleGraph V, ∃ c : V → Bool, actualState G c n = σ := attained σ

example (V : Type*) [Fintype V] (m n : ℕ) (hmn : m ≤ n) (σ : State V n)
    (v : V) (u : Universal.History (m + 1)) :
    (project hmn σ).part = historyPrefix hmn ∘ σ.part ∧
      (project hmn σ).deg v u = ∑ t ∈ block (historyPrefix hmn) u, σ.deg v t :=
  ⟨project_part hmn σ, project_deg hmn σ v u⟩

example (V : Type*) [Fintype V] (m n : ℕ) (hmn : m ≤ n) (G : SimpleGraph V)
    (c : V → Bool) : project hmn (actualState G c n) = actualState G c m :=
  project_actualState hmn G c

example (V : Type*) [Fintype V] (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n)
    (σ : State V n) : project hlm (project hmn σ) = project (hlm.trans hmn) σ :=
  project_trans hlm hmn σ

example (V : Type*) [Fintype V] (n : ℕ) (σ : State V n) (v : V)
    (s : Universal.History (n + 1)) (b : Bool) :
    refinement σ v = append s b ↔ σ.part v = s ∧
      WithLp.toLp 2 (fun t => (σ.deg v t : ℝ)) ∈ childEvent s b := refinement_fiber σ v s b

example (V : Type*) [Fintype V] (n : ℕ) (σ : State V n) (G : SimpleGraph V)
    (c : V → Bool) (hG : degreeArray σ.part G = σ.deg)
    (hc : ∀ v, c v = bits (n + 1) (σ.part v) 0) :
    (nextState σ G hG).part = refinement σ ∧
      (nextState σ G hG).deg = degreeArray (refinement σ) G ∧
      nextState σ G hG = actualState G c (n + 1) :=
  ⟨rfl, rfl, nextState_eq_actual σ G c hG hc⟩

/-- info: 'MajorityDynamics.GraphProcess.FineState.actualState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualState
/-- info: 'MajorityDynamics.GraphProcess.FineState.reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reconstruction
/-- info: 'MajorityDynamics.GraphProcess.FineState.fact_state_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fact_state_reconstruction
/-- info: 'MajorityDynamics.GraphProcess.FineState.reconstruction_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reconstruction_state
/-- info: 'MajorityDynamics.GraphProcess.FineState.attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms attained
/-- info: 'MajorityDynamics.GraphProcess.FineState.actualState_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualState_eq_iff
/-- info: 'MajorityDynamics.GraphProcess.FineState.conditioning_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditioning_event
/-- info: 'MajorityDynamics.GraphProcess.FineState.project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project
/-- info: 'MajorityDynamics.GraphProcess.FineState.project_actualState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project_actualState
/-- info: 'MajorityDynamics.GraphProcess.FineState.project_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project_refl
/-- info: 'MajorityDynamics.GraphProcess.FineState.project_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project_trans
/-- info: 'MajorityDynamics.GraphProcess.FineState.refinement_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refinement_fiber
/-- info: 'MajorityDynamics.GraphProcess.FineState.refinement_actualState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refinement_actualState
/-- info: 'MajorityDynamics.GraphProcess.FineState.nextState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextState
/-- info: 'MajorityDynamics.GraphProcess.FineState.nextState_eq_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextState_eq_actual
end MajorityDynamics.GraphProcess.FineState
