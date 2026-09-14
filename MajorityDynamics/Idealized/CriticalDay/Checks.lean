import MajorityDynamics.Idealized.CriticalDay.Main

noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedEvolution
universe u

/-- The literal critical-day conclusion: global uniqueness, all original LA,
coefficient-one approximation, and every individual signed child gain. -/
example {V : Type u} [Fintype V] {n : ℕ} (N : ℕ) (p : Binomial.Probability)
    (y : Local.CoarseData V n) (T₁ δ₁ φ₁ ζ : ℝ) :
    Conclusion N p y T₁ δ₁ φ₁ ζ ↔
      (∃! q : Local.Tilt n, Local.Solves y.sizes y.realEdges q) ∧
      (∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q → Local.Admissible y q T₁ φ₁ p) ∧
      (∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q → ∀ s t,
        |(q s t:ℝ)-logitTilt N p (γ n s t) (ν n t)| ≤
          (p:ℝ)/Real.sqrt ((p:ℝ)*N)*(N:ℝ)^(-δ₁)) ∧
      (∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q → ∀ s b,
        ζ*N ≤ sign b*(Local.templateSizes y.sizes q (append s b)-(N:ℝ)*ν (n+1) (append s b))) := by
  constructor
  · intro h
    exact ⟨h.exists_unique,h.admissible,h.approximation,h.gain⟩
  · rintro ⟨hu,ha,ht,hg⟩
    exact ⟨hu,ha,ht,hg⟩

/-- ζ is chosen before δ; all later constants precede N,p,τ,V,y. -/
example :
  ∀ θ : ℝ, 1/2 < θ → θ < 1 →
  ∀ n : ℕ, (n:ℝ)+1 = 1/(1-θ) → ∀ T : ℝ, 1 < T →
  ∃ ζ : ℝ, 0 < ζ ∧ ∀ δ : ℝ, 0 < δ →
  ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ φ₁ : ℝ, 0 < φ₁ ∧ φ₁ < 1/2 ∧
  ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ p : ℝ,
    T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
  ∃ hp : 0 < p ∧ p < 1,
    Process.Specification N ⟨p,hp⟩ (responseHorizon θ) (processExponent θ T)
      (referenceDataReal θ T N p) ∧
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ y : Local.CoarseData V n,
      Faithful N p T δ τ (referenceDataReal θ T N p) y →
      Conclusion N ⟨p,hp⟩ y T₁ δ₁ φ₁ ζ := critical_day

end MajorityDynamics.Idealized.CriticalDay

/-- info: 'MajorityDynamics.Idealized.CriticalDay.critical_day' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.critical_day
