import MajorityDynamics.GraphProcess.RowGamma.Shared

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.gamma_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.gamma_mono

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.gamma_event_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.gamma_event_mono

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.gamma_failure_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.gamma_failure_mono

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.actual_gamma_failure_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.actual_gamma_failure_mono

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.conditioned_gamma_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.conditioned_gamma_eq

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.triple_conditioning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.triple_conditioning

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.good_mass_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.good_mass_lower

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.conditioned_failure_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.conditioned_failure_two

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.gamma_regular_failure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.gamma_regular_failure_le

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.Conclusion.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.Conclusion.mono

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.conclusion_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.conclusion_of_bounds

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.rowConstant_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.rowConstant_ge_one

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.uniform_history_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.uniform_history_gamma

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.uniform_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.uniform_complete

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.exists_uniform_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.exists_uniform_constant

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.uniform_shared_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.uniform_shared_constant

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
universe u

/-- Expanded consumer contract: constants precede the decay exponent and all
varying original inputs. This explicitly displays each actual law and event. -/
example {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      let μ := cond (RowArray.law y.part q) (RowArray.history y.part)
      let E := RowArray.exactTotals y.part y.edge
      let R := {d : RowArray.Ambient y.part | RowArray.Regular p d}
      let ν := cond μ E
      let τ := cond ν R
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ IsProbabilityMeasure τ ∧
      0 < (RowArray.law y.part q).real (RowArray.history y.part) ∧
      0 < μ.real E ∧ (1:ℝ)/2 ≤ ν.real R ∧
      τ = cond (RowArray.law y.part q) (RowArray.history y.part ∩ R ∩ E) ∧
      μ.real {d | ¬ RowArray.Gamma y.part (RowArray.totals d) C p d} ≤ (N : ℝ)^(-A) ∧
      ν.real {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ (N : ℝ)^(-A) ∧
      τ.real {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ (N : ℝ)^(-A) ∧
      ν.real {d | ¬ (RowArray.Gamma y.part y.edge C p d ∧ RowArray.Regular p d)} ≤
        (N : ℝ)^(-A) ∧
      (1:ℝ)/2 ≤ ν.real {d | RowArray.Gamma y.part y.edge C p d ∧ RowArray.Regular p d} := by
  obtain ⟨C,hC,h⟩ := exists_uniform_constant n hθlo hθhi hT hφ
  refine ⟨C,hC,?_⟩
  intro A hA
  obtain ⟨N₀,h₀⟩ := h A hA
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hc := h₀ N hN V hcard p hlo hhi y q ha.toCore C le_rfl
  exact ⟨hc.history_probability,hc.totals_probability,hc.triple_probability,
    hc.history_positive,hc.totals_positive,hc.regular_lower,hc.triple_identity,
    hc.history_failure,hc.totals_failure,hc.triple_failure,hc.joint_failure,hc.joint_lower⟩

/-- No exceptional first-level hypothesis: n=0 is included. -/
example {θ T φ : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V 0) (q : Local.Tilt 0), Local.Admissible y q T φ p →
      ∀ D ≥ C, Conclusion y q D p A N :=
  by
    obtain ⟨C, hC, h⟩ := exists_uniform_constant 0 hθlo hθhi hT hφ
    refine ⟨C, hC, ?_⟩
    intro A hA
    obtain ⟨N₀, h⟩ := h A hA
    refine ⟨N₀, ?_⟩
    intro N hN V inst hcard p hlo hhi y q ha
    exact h N hN V hcard p hlo hhi y q ha.toCore

/-- One literal graph numerator and the post-kappa row failure use exactly the
same fixed C, with density positivity derived rather than assumed. -/
example {θ T φ K : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      ∃ hp : 0 < p ∧ p < 1,
      (cond (RowArray.law y.part q)
        (RowArray.history y.part ∩ {d | RowArray.Regular p d} ∩
          RowArray.exactTotals y.part y.edge)).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ (N : ℝ)^(-A) ∧
      (((SimpleGraph.binomialRandom V ⟨p,hp.1.le,hp.2.le⟩).map
        (RowArray.graphArray y.part)).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d ∧ d ∈ RowArray.history y.part ∧
          RowArray.Regular p d ∧ d ∈ RowArray.exactTotals y.part y.edge}) ≤ Real.exp (-K*N) := by
  obtain ⟨C,hC,h⟩ := uniform_shared_constant n hθlo hθhi hT hφ hK
  refine ⟨C,hC,?_⟩
  intro A hA
  obtain ⟨N₀,h₀⟩ := h A hA
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  obtain ⟨hp,hrow,_,hgraph⟩ := h₀ N hN V hcard p hlo hhi y q ha.toCore
  refine ⟨hp,?_,hgraph⟩
  rw [← hrow.triple_identity]
  exact hrow.triple_failure

end MajorityDynamics.GraphProcess.RowGamma
