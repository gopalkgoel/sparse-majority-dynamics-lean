import MajorityDynamics.Paper.Problem

/-! Separate targets for the uniform-density proof. Defining these targets
does not prove them. The original theorem and its convergence day are unchanged. -/
noncomputable section
namespace MajorityDynamics.Paper

def uniformDensityRange (θ T : ℝ) (N : ℕ) (p : unitInterval) : Prop :=
  T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) ∧
    (p : ℝ) < T * (N : ℝ) ^ (-(1 / 2 : ℝ))

/-- The uniform-density theorem has the same convergence day as the original theorem. -/
def uniformConvergenceDay (θ : ℝ) : ℕ := 2 * expansionDay θ + 1

def uniformSuccessEvent {N : ℕ} (θ : ℝ) (c : Coloring N) : Set (Graph N) :=
  {G | ∀ v, coloringOnDay G c (uniformConvergenceDay θ) v = false}

def uniformExpansionEvent {N : ℕ} (θ : ℝ) (p : unitInterval) (c : Coloring N) : Set (Graph N) :=
  {G | ∃ d : ℕ, 1 ≤ d ∧ d ≤ expansionDay θ ∧
    (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N ≤ lead (coloringOnDay G c d)}

def UniformExpansionPhase : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
        uniformDensityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
          graphLaw N p (uniformExpansionEvent θ p c)ᶜ ≤ ENNReal.ofReal ε

/-- Internal sparse-range contract used to assemble the full uniform theorem. -/
def SparseMainTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
        uniformDensityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
          graphLaw N p (uniformSuccessEvent θ c)ᶜ ≤ ENNReal.ofReal ε

/-- Full uniform-density theorem. The unit-interval parameter includes p = 1;
there is no upper-density hypothesis beyond the probability domain. -/
def UniformMainTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
        T⁻¹ * (N : ℝ) ^ (-θ) ≤ (p : ℝ) →
        T⁻¹ ≤ τ → τ ≤ T → initialBias N τ c →
          graphLaw N p (uniformSuccessEvent θ c)ᶜ ≤ ENNReal.ofReal ε

end MajorityDynamics.Paper
