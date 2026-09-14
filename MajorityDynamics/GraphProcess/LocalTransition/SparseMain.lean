import MajorityDynamics.GraphProcess.LocalTransition.Main
import MajorityDynamics.GraphProcess.LocalTransition.SparseAlgebra
import MajorityDynamics.GraphProcess.AdmissibleFiber.Sparse

noncomputable section
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.LocalTransition
universe u
variable {V : Type*} [Fintype V] {n : ℕ}

theorem uniform_failure_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p → ∀ Cf Cs epsf epss : ℝ,
      0 ≤ Cf → 0 ≤ Cs → 0 ≤ epsf → 0 ≤ epss →
      ((CoarseKernel.Lambda p y).real {σ | ¬ FiberGood y q p Cf σ} ≤ epsf) →
      (∀ σ, CoarseKernel.rho p σ = y → FiberGood y q p Cf σ →
        (FineKernel.K σ).real {τ | ¬ KernelGood y p Cs σ τ} ≤ epss) →
      IsProbabilityMeasure (CoarseKernel.Lambda p y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      (CoarseKernel.Kbar p y).real {z | ¬ LocalSuccess y q p (Cf+Cs) z} ≤ epsf+epss := by
  obtain ⟨N₁,h₁⟩ := uniform_numerical_regime_sparse hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := AdmissibleFiber.uniform_admissible_unit_sparse n hθlo hθhi hT
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q φ ha Cf Cs epsf epss hCf hCs hef hes hf hs
  obtain ⟨hN2,hp,_,hg⟩ := h₁ N (by omega) p hlo hhi
  obtain ⟨hpi, ⟨d,G,hG⟩,hlaws⟩ := h₂ N (by omega) V hcard p hlo hhi y q φ ha.toCore
  refine ⟨hlaws.lambda_probability, hlaws.kbar_probability, hlaws.lambda_support, ?_⟩
  apply finite_failure p y q Cf Cs epsf epss hp hpi.2 hG.attainable _ _
    hCf hCs hef hes ha.solves ha.positive hf hs
  · rw [hcard]; exact_mod_cast (show 1 ≤ N by omega)
  · simpa only [hcard] using hg

theorem uniform_typical_failure_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p → ∀ Cf Cs epsf epss : ℝ,
      0 ≤ Cf → 0 ≤ Cs → 0 ≤ epsf → 0 ≤ epss →
      ((CoarseKernel.Lambda p y).real {σ | ¬ FiberTypical y q p Cf σ} ≤ epsf) →
      (∀ σ, CoarseKernel.rho p σ = y → FiberTypical y q p Cf σ →
        (FineKernel.K σ).real {τ | ¬ KernelGood y p Cs σ τ} ≤ epss) →
      IsProbabilityMeasure (CoarseKernel.Lambda p y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      (CoarseKernel.Kbar p y).real {z | ¬ LocalSuccess y q p (Cf+Cs) z} ≤ epsf+epss := by
  obtain ⟨N₁,h₁⟩ := uniform_numerical_regime_sparse hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := AdmissibleFiber.uniform_admissible_unit_sparse n hθlo hθhi hT
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q φ ha Cf Cs epsf epss hCf hCs hef hes hf hs
  obtain ⟨hN2,hp,_,hg⟩ := h₁ N (by omega) p hlo hhi
  obtain ⟨hpi, ⟨d,G,hG⟩,hlaws⟩ := h₂ N (by omega) V hcard p hlo hhi y q φ ha.toCore
  refine ⟨hlaws.lambda_probability, hlaws.kbar_probability, hlaws.lambda_support, ?_⟩
  apply Kbar_failure_le p y hp hpi.2 hG.attainable
    (FiberTypical y q p Cf) (KernelGood y p Cs) (LocalSuccess y q p (Cf+Cs))
    _ epsf epss hef hes hf hs
  intro σ hρ hF τ hS
  apply deterministic_finite y q p Cf Cs σ τ _ hp _ hCf hCs
    ha.solves ha.positive hρ hF.2 hS
  · rw [hcard]; exact_mod_cast (show 1 ≤ N by omega)
  · simpa only [hcard] using hg

end MajorityDynamics.GraphProcess.LocalTransition
