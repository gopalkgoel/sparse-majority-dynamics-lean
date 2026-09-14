import MajorityDynamics.GraphProcess.BlockCountProbability.Point
import MajorityDynamics.GraphProcess.BlockCountProbability.Regime

noncomputable section
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.BlockCountProbability
open Universal
open MajorityDynamics.Probability.FixedSizeExponential
universe u

def componentConstant (T : ℝ) : ℝ :=
  lossConstant T + |Real.log centralAtomConstant| + 1

theorem componentConstant_pos {T : ℝ} (hT : 1 < T) : 0 < componentConstant T := by
  have := lossConstant_pos hT
  unfold componentConstant
  positivity

/-- The common lower bound for the literal internal and bipartite binomial
counts, uniformly under the original density, size and count hypotheses. -/
theorem uniform_component_lower {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N)) →
      (∀ s, Real.exp (-C*N) ≤
        (ProbabilityTheory.binomial ((y.sizes s).choose 2) p).real
          {(y.edge s s/2).toNat}) ∧
      (∀ s t, s ≠ t → Real.exp (-C*N) ≤
        (ProbabilityTheory.binomial (y.sizes s*y.sizes t) p).real
          {(y.edge s t).toNat}) := by
  obtain ⟨N₀, h₀⟩ := uniform_regime n hθlo hθhi hT
  refine ⟨componentConstant T, componentConstant_pos hT, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  obtain ⟨hN1, hp0, hp1, hi, hc⟩ := h₀ N hN V hcard (p : ℝ) hlo hhi y hsizes hcounts
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  constructor
  · intro s
    obtain ⟨hk, hkm, hkN, hloss⟩ := hi s
    exact binomial_lower_of_loss p (lossConstant T) hp0 hp1 hNnat hk hkm hkN hloss
  · intro s t hst
    obtain ⟨hk, hkm, hkN, hloss⟩ := hc s t hst
    exact binomial_lower_of_loss p (lossConstant T) hp0 hp1 hNnat hk hkm hkN hloss

end MajorityDynamics.GraphProcess.BlockCountProbability
