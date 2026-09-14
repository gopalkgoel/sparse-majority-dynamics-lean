import MajorityDynamics.GraphProcess.EnumerationBounds.Main

/-! Literal formula checks, closed endpoint types, and exact transitive audits. -/
noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationBounds.Checks
open Universal
universe u
variable {V : Type*} [Fintype V] {n : ℕ}

example (y : Local.CoarseData V n) (s t : History (n+1)) :
    avg y s t =
    (y.edge s t : ℝ) / (y.sizes s : ℝ) := rfl

example (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) :
    squareSum y d s t =
    ∑ v ∈ History.block y.part s, ((RowArray.values d v t : ℝ) - avg y s t)^2 := rfl

example (y : Local.CoarseData V n) (s : History (n+1)) :
    muI y s =
    avg y s s / ((y.sizes s : ℝ) - 1) := rfl

example (y : Local.CoarseData V n) (s t : History (n+1)) :
    muC y s t =
    (y.edge s t : ℝ) / ((y.sizes s : ℝ) * (y.sizes t : ℝ)) := rfl

example (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s : History (n+1)) :
    gamma2 y d s =
    squareSum y d s s / ((y.sizes s : ℝ) - 1)^2 := rfl

example (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) :
    variance y d s t =
    squareSum y d s t / (y.sizes s : ℝ) := rfl

example (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s : History (n+1)) :
    internalCorrection y d s =
    1/4 - (gamma2 y d s)^2 / (4 * (muI y s)^2 * (1-muI y s)^2) := rfl

example (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) :
    crossCorrection y d s t =
    -(1/2) * (1 - variance y d s t / (avg y s t * (1-muC y s t))) *
    (1 - variance y d t s / (avg y t s * (1-muC y s t))) := rfl

example (y : Local.CoarseData V n) (d : RowArray.Ambient y.part) :
    correction y d =
    (∑ s, internalCorrection y d s) +
    ∑ z : BlockDecomposition.Pair (History (n+1)), crossCorrection y d z.val.1 z.val.2 := rfl

example {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      RowArray.totals d = y.edge → RowArray.Regular p d →
      |correction y d| ≤ C*(p*N)^(2/7:ℝ) :=
  uniform_weak_correction n hθlo hθhi hT

example {θ T CΓ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hΓ : 0 < CΓ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      RowArray.totals d = y.edge → RowArray.Regular p d →
      RowArray.Gamma y.part y.edge CΓ p d → |correction y d| ≤ C :=
  uniform_strong_correction n hθlo hθhi hT hΓ

example {θ T ε : ℝ}
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
      (Real.log (N : ℝ))^2 / Real.sqrt (N : ℝ) +
        (p*N)^(-(1:ℝ)/12) < ε :=
  scalar_error_vanishes hθlo hθhi hT hε

example {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ (n : ℕ) (p : ℝ),
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      RowArray.Regular p d → 0 < (N : ℝ) ∧ 0 < p ∧ 1 ≤ p*N ∧
      (∀ s, 2 ≤ (y.sizes s : ℝ)) ∧
      (∀ s t, p*N/(2*T^2) ≤ avg y s t ∧ avg y s t ≤ 2*T*p*N) ∧
      (∀ s t, |avg y s t-p*(y.sizes t : ℝ)| ≤ T^2*Real.sqrt (p*N)) ∧
      (∀ s, p/(2*T^2) ≤ muI y s ∧ muI y s ≤ 4*T^2*p) ∧
      (∀ s t, p/(2*T^2) ≤ muC y s t ∧ muC y s t ≤ 4*T^2*p) ∧
      4*T^2*p ≤ 1/2 ∧
      (∀ s t v, v ∈ History.block y.part s →
        |(RowArray.values d v t : ℝ)-avg y s t| ≤ 2*(p*N)^(4/7:ℝ)) ∧
      (∀ s t v, v ∈ History.block y.part s →
        |(RowArray.values d v t : ℝ)-avg y s t| ≤ (avg y s t)^(7/12:ℝ)) := by
  obtain ⟨N₀, hN₀⟩ := uniform_preparation hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard n p hlo hhi y d hsizes hcounts hreg
  have h := hN₀ N hN V hcard n p hlo hhi y d hsizes hcounts hreg
  subst N
  exact ⟨h.card_pos, h.density_pos, h.mean_one, h.size_two,
    fun s t => ⟨h.avg_lower s t, h.avg_upper s t⟩, h.avg_center,
    fun s => ⟨h.internal_lower s, h.internal_upper s⟩,
    fun s t => ⟨h.cross_lower s t, h.cross_upper s t⟩,
    h.density_small, h.entry, h.entry_enumeration⟩

end MajorityDynamics.GraphProcess.EnumerationBounds.Checks

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.size_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.size_estimates

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.pair_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.pair_estimates

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.internal_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.internal_estimates

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.eventually_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.eventually_window

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.eventually_deviation_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.eventually_deviation_regime

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.scalar_error_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.scalar_error_vanishes

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.finite_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.finite_preparation

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.uniform_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.uniform_preparation

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.squareSum_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.squareSum_gamma

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.squareSum_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.squareSum_weak

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.factors_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.factors_bound

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.weak_factors_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.weak_factors_bound

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.correction_terms_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.correction_terms_bound

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.correction_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.correction_sum_bound

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.weak_correction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.weak_correction_bound

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.strong_correction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.strong_correction_bound

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.uniform_weak_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.uniform_weak_correction

/-- info: 'MajorityDynamics.GraphProcess.EnumerationBounds.uniform_strong_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationBounds.uniform_strong_correction
