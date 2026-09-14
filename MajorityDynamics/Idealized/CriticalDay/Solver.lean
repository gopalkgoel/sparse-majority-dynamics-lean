import MajorityDynamics.Idealized.CriticalDay.Scaling
import MajorityDynamics.Idealized.Process.SolvabilityRows
import MajorityDynamics.Idealized.RowLimits.Main

/-! Uniform nonlinear Gaussian inversion. This helper keeps the nonzero
decision shift throughout; its hypotheses are the actual E.3 size conditions
and an explicit numerical target estimate, not an assumed mean-map estimate. -/
noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits Process
open Binomial.Approximation (Density)

theorem solve_of_row_inputs (n ell : ℕ) (hell : 1 ≤ ell) (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ R : ℝ, 0 < R ∧ (∀ s t, |γ n s t| ≤ R) ∧ ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
    ∃ ell' N₀ : ℕ, ∀ N ≥ N₀, ∀ p : Binomial.Probability, Density θ T N p →
    ∀ ξ E : ℝ, 0 < ξ → ξ ≤ T → 0 < E → E < r →
    C * error ell' N p ξ ≤ E →
    ∀ sizes : Local.Sizes n, (∀ s, 0 < sizes s) →
    (∀ s, AdmissibleSizes N p ell T ξ s sizes) →
    ∀ edges : Local.EdgeCounts n,
    (∀ s t, |(edges s t / sizes s - (p : ℝ) * sizes t) /
      Real.sqrt ((p : ℝ) * N) - ν n t * μ n s t| ≤ E) →
    ∃ σ : History (n + 1) → Row (n + 1),
      (∀ s t, |σ s t| ≤ R) ∧
      (∀ s t, |σ s t - γ n s t| ≤ C * E) ∧
      Local.Solves sizes edges (fun s => rowTilt N p (σ s)) ∧
      ∀ s, Estimates N p sizes s (σ s) (shift N p sizes) C (error ell' N p ξ) := by
  obtain ⟨R, hR, hγR, r, hr, A, hA, hinv⟩ := stable_mean_inverse n
  obtain ⟨lower, hrow⟩ := row_limits n
  obtain ⟨ell', hrow⟩ := hrow ell hell
  obtain ⟨_, hrow⟩ := hrow T R hT hR
  obtain ⟨B, hB, N₀, hrow⟩ := hrow θ hθlo hθhi
  let C := max A B
  have hC : 0 < C := hA.trans_le (le_max_left _ _)
  refine ⟨R, hR, hγR, r, hr, C, hC, ell', max 1 N₀, ?_⟩
  intro N hN p hp ξ E hξ hξT hE hEr herror sizes hs hadm edges htarget
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hN))
  have hscale : Real.sqrt ((p : ℝ) * N) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos p.property.1 hNr)).ne'
  have herror0 : 0 ≤ error ell' N p ξ := by
    unfold error
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (le_max_left 1 N₀).trans hN)
    positivity
  have hrow' := fun s => hrow N ((le_max_right _ _).trans hN) p hp.1 hp.2
    ξ hξ hξT s sizes (hadm s)
  have hsol : ∀ s : History (n + 1), ∃ σ : Row (n + 1),
      normalizedMeanMap N p sizes s σ = WithLp.toLp 2 (fun t =>
        (edges s t / sizes s - (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N)) ∧
      (∀ t, |σ t| ≤ R) ∧ ∀ t, |σ t - γ n s t| ≤ A * E := by
    intro s
    apply hinv E hE hEr s _ (normalizedMeanMap_continuous N p sizes s)
    · intro σ hσ t
      have hm := ((hrow' s).2 σ hσ).2.2.2.1.history_mean t
      have hgauss := gaussianMean_history_eq_meanMap s σ t
      change |(binomialMean N p sizes s (Local.historySupport sizes s) t σ -
        (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N) - meanMap s (ν n) σ t| ≤ E
      rw [← hgauss]
      exact hm.trans ((mul_le_mul_of_nonneg_right (le_max_right A B) herror0).trans herror)
    · exact htarget s
  choose σ hsolve hσR hσγ using hsol
  refine ⟨σ, hσR, fun s t => (hσγ s t).trans
    (mul_le_mul_of_nonneg_right (le_max_left A B) hE.le), ?_, ?_⟩
  · intro s t
    have heq := congrArg (fun x : Row (n + 1) => x t) (hsolve s)
    change (_ - _) / Real.sqrt ((p : ℝ) * N) =
      (edges s t / sizes s - (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N) at heq
    have hm := sub_left_inj.mp ((div_left_inj' hscale).mp heq)
    have hm' := (eq_div_iff (Nat.cast_pos.mpr (hs s)).ne').mp hm
    rw [binomialMean_eq_conditionalMean] at hm'
    simpa only [Local.rowMean, mul_comm] using hm'
  · intro s
    exact enlarge_estimates (((hrow' s).2 (σ s) (hσR s)).2.2.2.1)
      (mul_le_mul_of_nonneg_right (le_max_right A B) herror0)

end MajorityDynamics.Idealized.CriticalDay
