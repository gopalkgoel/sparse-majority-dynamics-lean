import MajorityDynamics.GraphProcess.FineState.Refinement

/-! Public natural-day version of Fact 2.2, including the named block label. -/
noncomputable section
namespace MajorityDynamics.GraphProcess.FineState
open Universal History
open Probability.RandomOpinionsReduction (coloringOnDayV)
variable {V : Type*} [Fintype V] {n : ℕ}

theorem fact_state_reconstruction (σ : State V n) (G : SimpleGraph V) (c : V → Bool)
    (hG : degreeArray σ.part G = σ.deg) (hc : CompatibleInitial σ.part c)
    (r : ℕ) (hr : 1 ≤ r ∧ r ≤ n + 1) (s : Universal.History (n + 1))
    (v : V) (hv : v ∈ block σ.part s) :
    Paper.opinion (coloringOnDayV G c r v) =
      Paper.opinion (bits (n + 1) s ⟨r - 1, by omega⟩) := by
  have h := reconstruction_days σ G c hG hc r hr v
  simpa only [(mem_block _ _ _).mp hv] using h

end MajorityDynamics.GraphProcess.FineState
