import MajorityDynamics.Idealized.RowLimits.RowsSparse
import MajorityDynamics.Idealized.RowLimits.ComparisonMoments

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped NNReal
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation Analysis
variable {n : ℕ}

/-- The mean solver needs only the compact history parameters. No bound on
the final-decision imbalance or lower bound on either child is used. -/
theorem row_history_mean_sparse (θ T R : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hR : 0 ≤ R) :
    ∃ c A C : ℝ, 0 < c ∧ 0 < A ∧ 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, 1 ≤ Real.log (N:ℝ) →
      ∀ p : Probability, SparseRange θ T N p →
      ∀ (s : History (n+1)) (sizes : Local.Sizes n),
      (∀ t, (N:ℝ)*ν n t/2 ≤ (Local.trials sizes s t:ℝ)) →
      (∀ t, (Local.trials sizes s t:ℝ) ≤ 2*N*ν n t) →
      (∀ t, 0 < sizes t) → ∀ σ : Row (n+1), (∀ t, |σ t| ≤ R) →
      actualNormalizedParameters N p sizes s σ none ∈ gaussianBox n n R 0 →
      ∀ E : ℝ,
      Real.log N ^ (5 + Fintype.card (Fin (n+1) → Bool)) / scale N p ≤ E →
      dist (actualNormalizedParameters N p sizes s σ none) (historyParameters σ) ≤ E →
      (p:ℝ)/scale N p ≤ E →
      A * (Real.log N ^ (5 + Fintype.card (Fin (n+1) → Bool)) / scale N p) ≤ c/2 →
      c/2 ≤ binomialMass N p sizes s (Local.historySupport sizes s) σ ∧
      ∀ t, |(binomialMean N p sizes s (Local.historySupport sizes s) t σ -
        (p:ℝ)*sizes t) / scale N p - gaussianMean σ (historyEvent s) t| ≤ C*E := by
  classical
  obtain ⟨B,hB,L,hctl⟩ := eventwise_compact_control n R 0
  let c := (gaussian_boxes_uniform_lower n R 0).choose
  have hc : 0 < c := (gaussian_boxes_uniform_lower n R 0).choose_spec.1
  obtain ⟨A,hA,N₀,hN₀,hraw⟩ := row_normalized_comparison_sparse (n:=n) θ T R hθlo hθhi hT hR
  let C := ratioConstant (c/2) B * (A+(L:ℝ)) + 1
  have hC : 0 < C := by dsimp [C,ratioConstant]; positivity
  refine ⟨c,A,C,hc,hA,hC,N₀,hN₀,?_⟩
  intro N hN hlog p hp s sizes hlo hhi hsz σ hσ hx E hδE hdist hcenter hsmall
  have hn : 0 < N := by omega
  have hy : historyParameters σ ∈ gaussianBox n n R 0 :=
    historyParameters_mem_box hR le_rfl hσ
  have hcomp := eventRawEstimates_of_comparison (hctl s none) hx hy hc hA.le
    (eventwise_compact_lower n R 0 s none _ hx)
    (eventwise_compact_lower n R 0 s none _ hy)
    (fun o => by
      have hh := hraw N hN hlog p hp s sizes hlo hhi σ hσ none o
      rw [actualGaussianMoment_eq_parameterMoment] at hh
      simpa only [scale,div_eq_mul_inv,mul_assoc] using hh)
    (show dist (actualNormalizedParameters N p sizes s σ none) (historyParameters σ) ≤ 1*E by
      simpa only [one_mul] using hdist)
    hδE hsmall (target_mass_eq s σ none 0) (target_first_eq s σ none 0)
    (target_second_eq s σ none 0)
  refine ⟨hcomp.binomial_lower,?_⟩
  intro t
  have hh := hcomp.mean (half_pos hc) hn t
  have hm : |(binomialMean N p sizes s (Local.historySupport sizes s) t σ -
      (p:ℝ)*Local.trials sizes s t)/scale N p - gaussianMean σ (historyEvent s) t| ≤
      (ratioConstant (c/2) B*(A+(L:ℝ)))*E := by
    simpa only [scale,eventSupport,targetEvent,mul_one,mul_assoc] using hh
  exact recenter_estimate N p sizes s t (hsz t) _ _ _ E hm hcenter

end MajorityDynamics.Idealized.RowLimits
