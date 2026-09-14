import MajorityDynamics.GraphProcess.EnumerationComparison.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
universe u

example {θ T : ℝ} (n : ℕ) (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
    T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n),
    (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
    (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
    ∀ (q : Local.Tilt n) (d : RowArray.Ambient y.part),
    RowArray.totals d = y.edge → RowArray.Regular p d →
    Sandwich (C*(p*N)^(2/7:ℝ)) ((GraphicalArray.law y.part y.edge).real {d})
      ((cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d}) := uniform_weak_comparison n hθlo hθhi hT

example {θ T CΓ : ℝ} (n : ℕ) (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hΓ : 0 < CΓ) :
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
    T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n),
    (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
    (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
    ∀ (q : Local.Tilt n) (E : Set (RowArray.Ambient y.part)),
    (∀ d ∈ E, RowArray.totals d = y.edge ∧ RowArray.Regular p d ∧
      RowArray.Gamma y.part y.edge CΓ p d) →
    Sandwich C ((GraphicalArray.law y.part y.edge).real E)
      ((cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real E) := uniform_strong_comparison n hθlo hθhi hT hΓ

/-- The original multiplicative constant is strictly greater than one. -/
example {θ T CΓ : ℝ} (n : ℕ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hΓ : 0 < CΓ) :
    ∃ C' : ℝ, 1 < C' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
    T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n),
    (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
    (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
    ∀ (q : Local.Tilt n) (d : RowArray.Ambient y.part),
    RowArray.totals d = y.edge → RowArray.Regular p d →
    RowArray.Gamma y.part y.edge CΓ p d →
    C'⁻¹ * (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d} ≤
      (GraphicalArray.law y.part y.edge).real {d} ∧
    (GraphicalArray.law y.part y.edge).real {d} ≤
      C' * (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d} := by
  obtain ⟨C,hC,N₀,hN₀⟩ := uniform_strong_comparison n hθlo hθhi hT hΓ
  refine ⟨Real.exp C, Real.one_lt_exp_iff.mpr hC, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts q d htot hreg hgamma
  have hh := hN₀ N hN V hcard p hlo hhi y hsizes hcounts q {d}
    (fun a ha => by obtain rfl : a=d := ha; exact ⟨htot,hreg,hgamma⟩)
  simpa only [Sandwich, Real.exp_neg] using hh

end MajorityDynamics.GraphProcess.EnumerationComparison

/-- info: 'MajorityDynamics.GraphProcess.EnumerationComparison.uniform_weak_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationComparison.uniform_weak_comparison
/-- info: 'MajorityDynamics.GraphProcess.EnumerationComparison.uniform_strong_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationComparison.uniform_strong_comparison
