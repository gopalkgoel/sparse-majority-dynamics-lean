import MajorityDynamics.GraphProcess.FineState.Basic

/-! Fact 2.2: every realizing graph reconstructs all prescribed histories. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.FineState
open Universal History
open Probability.RandomOpinionsReduction (coloringOnDayV nextColoringV)
variable {V : Type*} [Fintype V] {n : ℕ}

theorem reconstruction (σ : State V n) (G : SimpleGraph V) (c : V → Bool)
    (hG : degreeArray σ.part G = σ.deg) (hc : CompatibleInitial σ.part c)
    (r : Fin (n + 1)) (v : V) :
    coloringOnDayV G c (r.val + 1) v = bits (n + 1) (σ.part v) r := by
  have step : ∀ j : ℕ, (hj : j < n + 1) → ∀ w : V,
      coloringOnDayV G c (j + 1) w = bits (n + 1) (σ.part w) ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj w; simpa [coloringOnDayV] using hc w
    | succ j ih =>
      intro hj w
      have hj' : j < n := by omega
      let r' : Fin n := ⟨j, hj'⟩
      have hi := ih (by omega)
      have hs := neighborSum_of_fiber_coloring σ.part G (coloringOnDayV G c (j + 1))
        (fun t => bits (n + 1) t r'.castSucc) hi w
      have hz : (neighborSum G (coloringOnDayV G c (j + 1)) w : ℝ) =
          imbalance r'.castSucc (row σ.deg w) := by
        rw [hs, hG]
        simp [imbalance, character, Int.cast_sum, Int.cast_mul]
      rw [show j + 1 + 1 = j + 2 by omega, coloringOnDay_succ]
      apply (nextColoring_decision G _ w _).mpr
      rw [hi w, hz]
      exact σ.history w r'
  exact step r.val r.isLt v

theorem reconstruction_days (σ : State V n) (G : SimpleGraph V) (c : V → Bool)
    (hG : degreeArray σ.part G = σ.deg) (hc : CompatibleInitial σ.part c)
    (r : ℕ) (hr : 1 ≤ r ∧ r ≤ n + 1) (v : V) :
    Paper.opinion (coloringOnDayV G c r v) =
      Paper.opinion (bits (n + 1) (σ.part v) ⟨r - 1, by omega⟩) := by
  have h := reconstruction σ G c hG hc ⟨r - 1, by omega⟩ v
  have he : r - 1 + 1 = r := by omega
  simpa [he] using congrArg Paper.opinion h

theorem reconstruction_history (σ : State V n) (G : SimpleGraph V) (c : V → Bool)
    (hG : degreeArray σ.part G = σ.deg) (hc : CompatibleInitial σ.part c) :
    actualHistory G c (n + 1) = σ.part := by
  funext v
  exact (actualHistory_eq_iff G c (n + 1) v _).mpr (fun r => reconstruction σ G c hG hc r v)

theorem reconstruction_state (σ : State V n) (G : SimpleGraph V) (c : V → Bool)
    (hG : degreeArray σ.part G = σ.deg) (hc : CompatibleInitial σ.part c) :
    actualState G c n = σ := by
  have hp := reconstruction_history σ G c hG hc
  apply State.ext hp
  simpa only [actualState_deg, hp] using hG

theorem actualState_compatible (G : SimpleGraph V) (c : V → Bool) (n : ℕ) :
    CompatibleInitial (actualState G c n).part c := by
  intro v
  change c v = bits (n + 1) (actualHistory G c (n + 1) v) 0
  rw [bits_actualHistory]
  rfl

theorem attained (σ : State V n) : ∃ G c, actualState G c n = σ := by
  obtain ⟨G, hG⟩ := σ.realizable
  exact ⟨G, (initial σ), reconstruction_state σ G (initial σ) hG (initial_compatible σ)⟩

theorem actualState_eq_iff (G : SimpleGraph V) (c : V → Bool) (σ : State V n) :
    actualState G c n = σ ↔ CompatibleInitial σ.part c ∧ degreeArray σ.part G = σ.deg := by
  constructor
  · intro h
    subst σ
    exact ⟨actualState_compatible G c n, rfl⟩
  · rintro ⟨hc, hG⟩
    exact reconstruction_state σ G c hG hc

theorem conditioning_event (σ : State V n) (c : V → Bool)
    (hc : CompatibleInitial σ.part c) :
    {G : SimpleGraph V | actualState G c n = σ} =
      {G : SimpleGraph V | degreeArray σ.part G = σ.deg} := by
  ext G
  simp only [Set.mem_ofPred_eq, actualState_eq_iff, and_iff_right hc]

instance : Finite (State V n) :=
  Finite.of_surjective (fun p : SimpleGraph V × (V → Bool) => actualState p.1 p.2 n)
    (fun σ => by obtain ⟨G, c, h⟩ := attained σ; exact ⟨(G, c), h⟩)

instance : Fintype (State V n) := Fintype.ofFinite _

end MajorityDynamics.GraphProcess.FineState
