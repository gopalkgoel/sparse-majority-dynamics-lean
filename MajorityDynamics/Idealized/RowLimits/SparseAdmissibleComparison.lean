import MajorityDynamics.Idealized.RowLimits.RowsSparse
import MajorityDynamics.Idealized.RowLimits.SparseGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis Binomial Binomial.Approximation
variable {n : ℕ}
theorem row_normalized_comparison_admissible_sparse (θ T R : ℝ) (ell : ℕ)
    (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Probability, SparseRange θ T N p →
      ∀ ξ : ℝ, ξ ≤ T → ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
      AdmissibleSizes N p ell T ξ s sizes →
      ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
      ∀ b : Option Bool, ∀ o : MomentKind (Fintype.card (Fin (n + 1) → Bool)),
      |binomialNormalizedMoment N p sizes s (eventSupport sizes s b)
          (fun t => (p : ℝ) * Local.trials sizes s t) (scale N p) o σ -
        actualGaussianMoment N p sizes s σ b o| ≤
        C * Real.log N ^ (5 + Fintype.card (Fin (n + 1) → Bool)) / scale N p := by
  obtain ⟨C,hC,N₁,hN₁,happ⟩ := row_normalized_comparison_sparse (n:=n) θ T R hθ hθ' hT hR
  have hg := eventual_trial_geometry_sparse (n:=n) θ T ell hθ' (by linarith)
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp (hg.and hl)
  refine ⟨C,hC,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN p hp ξ _hξT s sizes ha σ hσ b o
  have hh := h₂ N ((le_max_right _ _).trans hN)
  have htr := hh.1.2 p hp ξ s sizes ha
  exact happ N ((le_max_left _ _).trans hN) hh.2 p hp s sizes
    (fun t => (htr t).2.1.le) (fun t => (htr t).2.2.1.le) σ hσ b o

end MajorityDynamics.Idealized.RowLimits
