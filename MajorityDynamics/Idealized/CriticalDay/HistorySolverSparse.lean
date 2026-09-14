import MajorityDynamics.Idealized.CriticalDay.Solver
import MajorityDynamics.Idealized.RowLimits.HistorySparse

noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits Process
open Binomial.Approximation (SparseRange scale)

/-- Nonlinear inversion from actual sparse binomial history rows, allowing
an arbitrary final-decision shift. Every approximation hypothesis below is
a numerical parameter or target bound, not an assumed mean-map estimate. -/
theorem solve_of_history_parameters_sparse (n : ℕ) (θ T : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ R r c A C K : ℝ, 0 < R ∧ 0 < r ∧ 0 < c ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧
      (∀ s t, |γ n s t| ≤ R) ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, 1 ≤ Real.log (N:ℝ) →
      ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ d E : ℝ, 0 < E → E < r → C*d ≤ E →
      Real.log N ^ (5 + Fintype.card (Fin (n+1) → Bool)) / scale N p ≤ d →
      (p:ℝ)/scale N p ≤ d →
      A * (Real.log N ^ (5 + Fintype.card (Fin (n+1) → Bool)) / scale N p) ≤ c/2 →
      ∀ sizes : Local.Sizes n, (∀ t, 0 < sizes t) →
      (∀ s t, (N:ℝ)*ν n t/2 ≤ (Local.trials sizes s t:ℝ)) →
      (∀ s t, (Local.trials sizes s t:ℝ) ≤ 2*N*ν n t) →
      (∀ s σ, (∀ t, |σ t| ≤ R) →
        actualNormalizedParameters N p sizes s σ none ∈ gaussianBox n n R 0 ∧
        dist (actualNormalizedParameters N p sizes s σ none) (historyParameters σ) ≤ d) →
      ∀ edges : Local.EdgeCounts n,
      (∀ s t, |(edges s t/sizes s-(p:ℝ)*sizes t)/scale N p-ν n t*μ n s t| ≤ E) →
      ∃ σ : History (n+1) → Row (n+1),
        (∀ s t, |σ s t| ≤ R) ∧ (∀ s t, |σ s t-γ n s t| ≤ K*E) ∧
        Local.Solves sizes edges (fun s => rowTilt N p (σ s)) ∧
        ∀ s, c/2 ≤ binomialMass N p sizes s (Local.historySupport sizes s) (σ s) := by
  obtain ⟨R,hR,hγR,r,hr,K,hK,hinv⟩ := stable_mean_inverse n
  obtain ⟨c,A,C,hc,hA,hC,N₀,hN₀,hrows⟩ :=
    row_history_mean_sparse (n:=n) θ T R hθlo hθhi hT hR.le
  refine ⟨R,r,c,A,C,K,hR,hr,hc,hA,hC,hK,hγR,N₀,hN₀,?_⟩
  intro N hN hlog p hp d E hE hEr herror hraw hcenter hsmall sizes hs hlo hhi hparams edges htarget
  have hn : 0 < N := by omega
  have hscale : scale N p ≠ 0 := (Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hn))).ne'
  have hrow (s) (σ : Row (n+1)) (hσ : ∀ t, |σ t| ≤ R) :=
    hrows N hN hlog p hp s sizes (hlo s) (hhi s) hs σ hσ
      (hparams s σ hσ).1 d hraw (hparams s σ hσ).2 hcenter hsmall
  have hsol : ∀ s : History (n+1), ∃ σ : Row (n+1),
      normalizedMeanMap N p sizes s σ = WithLp.toLp 2 (fun t =>
        (edges s t/sizes s-(p:ℝ)*sizes t)/scale N p) ∧
      (∀ t, |σ t| ≤ R) ∧ ∀ t, |σ t-γ n s t| ≤ K*E := by
    intro s
    apply hinv E hE hEr s _ (normalizedMeanMap_continuous N p sizes s)
    · intro σ hσ t
      have hm := (hrow s σ hσ).2 t
      rw [gaussianMean_history_eq_meanMap s σ t] at hm
      exact hm.trans herror
    · exact htarget s
  choose σ hsolve hσR hσγ using hsol
  refine ⟨σ,hσR,hσγ,?_,fun s => (hrow s (σ s) (hσR s)).1⟩
  intro s t
  have heq := congrArg (fun x : Row (n+1) => x t) (hsolve s)
  change (_-_)/scale N p = (edges s t/sizes s-(p:ℝ)*sizes t)/scale N p at heq
  have hm := sub_left_inj.mp ((div_left_inj' hscale).mp heq)
  have hm' := (eq_div_iff (Nat.cast_pos.mpr (hs s)).ne').mp hm
  rw [binomialMean_eq_conditionalMean] at hm'
  simpa only [Local.rowMean,mul_comm] using hm'

end MajorityDynamics.Idealized.CriticalDay
