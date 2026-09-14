import MajorityDynamics.Paper.Problem

/-!
# The three proof phases

These are concrete propositions, not axioms. They split the main proof into
expansion, random-graph pseudorandomness, and deterministic cleanup. Cleanup is
proved in `CleanupAsymptotics.lean`; expansion is proved in `Expansion/Main.lean`.
`Pseudorandomness.lean` proves pseudorandomness from two named cited inputs.
No internal mathematical axiom remains in `Pending.lean`.
`DEPENDENCIES.md` records the current literature boundary.
-/

noncomputable section

namespace MajorityDynamics.Paper

/-- Every vertex has degree at least `0.9 p N`. -/
def minimumDegree {N : ℕ} (G : Graph N) (p : unitInterval) : Prop :=
  ∀ v : Fin N,
    (9 / 10 : ℝ) * (p : ℝ) * (N : ℝ) ≤
      (orderedEdgeCount G {v} Finset.univ : ℝ)

/-- The minimum-degree and jumbledness event of `lem:cklt-jumbled`. -/
def pseudorandomEvent {N : ℕ} (p : unitInterval) (CJ : ℝ) : Set (Graph N) :=
  {G | minimumDegree G p ∧ Jumbled G p (CJ * Real.sqrt ((p : ℝ) * (N : ℝ)))}

/-- The large lead reached in `cor:lead`. -/
def expansionEvent {N : ℕ} (θ : ℝ) (p : unitInterval) (c : Coloring N) :
    Set (Graph N) :=
  {G | (N : ℝ) / Real.sqrt ((p : ℝ) * (N : ℝ)) * Real.log (N : ℝ) ≤
    lead (coloringOnDay G c (expansionDay θ))}

/-- Internal obligation `cor:lead`, uniform in density and initial coloring.
This is proved by `Expansion.expansion` from the completed local-transition,
universal, critical-day and actual faithful-trajectory arguments. -/
def ExpansionPhase : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
        densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
          graphLaw N p (expansionEvent θ p c)ᶜ ≤ ENNReal.ofReal ε

/-- Obligation `lem:cklt-jumbled`. The constant `CJ` is absolute: it is chosen
before θ and T. Its minimum-degree part is elementary concentration; the
jumbledness part is the KS06/CKLT21 literature input. -/
def Pseudorandomness : Prop :=
  ∃ CJ : ℝ, 0 < CJ ∧
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ p : unitInterval, densityRange θ T N p →
          graphLaw N p (pseudorandomEvent p CJ)ᶜ ≤ ENNReal.ofReal ε

/-- The contraction lemma and final iteration/arithmetic in Section 6 turn the
large lead into unanimity. Proved by `deterministic_cleanup` in `CleanupAsymptotics.lean`.
No probability claim or initial-bias assumption is needed in this implication. -/
def DeterministicCleanup : Prop :=
  ∀ θ T CJ : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < CJ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (p : unitInterval) (G : Graph N) (c : Coloring N),
        densityRange θ T N p → G ∈ pseudorandomEvent p CJ →
          G ∈ expansionEvent θ p c → G ∈ successEvent θ c

end MajorityDynamics.Paper
