import MajorityDynamics.GraphProcess.FiberTransference.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

example {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ D : ℝ, 0 < D ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p →
      Real.exp (-D*N) ≤ (graphArrayLaw p y).real
        (RowArray.exactTotals y.part y.edge ∩ GraphicalArray.historyRegular p y.part) :=
  by
    obtain ⟨D, hD, N₀, h⟩ := uniform_denominator n hθlo hθhi hT
    refine ⟨D, hD, N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi y q φ ha
    exact h N hN V hcard p hlo hhi y q φ ha.toCore

example {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
    RowGamma.Conclusion y q C p A N ∧
    (cond (GraphicalArray.law y.part y.edge)
      (GraphicalArray.historyRegular p y.part)).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ Real.exp (-(N : ℝ)) :=
  by
    obtain ⟨C, hC, h⟩ := uniform_gamma n hθlo hθhi hT hφ
    refine ⟨C, hC, ?_⟩
    intro A hA
    obtain ⟨N₀, h⟩ := h A hA
    refine ⟨N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    exact h N hN V hcard p hlo hhi y q ha.toCore

example {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
    ∀ E : Set (RowArray.Ambient y.part),
    (CoarseKernel.Lambda p y).real {σ | σ.deg ∉ RowArray.values '' E} ≤
      Real.exp (-(N : ℝ)) + C *
        (cond (RowConcentration.conditionedLaw y q)
          (RowArray.exactTotals y.part y.edge)).real Eᶜ :=
  by
    obtain ⟨C, hC, N₀, h⟩ := uniform_transfer n hθlo hθhi hT hφ
    refine ⟨C, hC, N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    exact h N hN V hcard p hlo hhi y q ha.toCore

example {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∃ hp : 0 < p ∧ p < 1,
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
    ∀ E : Set (RowArray.Ambient y.part),
    (CoarseKernel.Lambda ⟨p,hp.1.le,hp.2.le⟩ y).real {σ | σ.deg ∉ RowArray.values '' E} ≤
      Real.exp (-(N : ℝ)) + C *
        (cond (RowConcentration.conditionedLaw y q)
          (RowArray.exactTotals y.part y.edge)).real Eᶜ :=
  by
    obtain ⟨C, hC, N₀, h⟩ := uniform_transfer_real n hθlo hθhi hT hφ
    refine ⟨C, hC, N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi
    obtain ⟨hp, h⟩ := h N hN V hcard p hlo hhi
    refine ⟨hp, ?_⟩
    intro y q ha
    exact h y q ha.toCore

end MajorityDynamics.GraphProcess.FiberTransference

/-- info: 'MajorityDynamics.GraphProcess.FiberTransference.uniform_denominator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FiberTransference.uniform_denominator
/-- info: 'MajorityDynamics.GraphProcess.FiberTransference.uniform_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FiberTransference.uniform_gamma
/-- info: 'MajorityDynamics.GraphProcess.FiberTransference.uniform_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FiberTransference.uniform_transfer
/-- info: 'MajorityDynamics.GraphProcess.FiberTransference.uniform_transfer_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FiberTransference.uniform_transfer_real
