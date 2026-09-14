import MajorityDynamics.Idealized.CriticalDay.HistorySolverSparse
import MajorityDynamics.Idealized.CriticalDay.TemplateGainLinear
import MajorityDynamics.Idealized.RowLimits.ParameterGeometryBudget
import MajorityDynamics.Idealized.RowLimits.MassSparseUnbounded

/-! The actual terminal row solver and signed template gain from finite
numerical budgets. This is an ingredient, not the final trajectory theorem. -/
noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits Process
open Binomial.Approximation (SparseRange scale)
open scoped BigOperators

/-- A decision-unbounded terminal row engine. All analytic estimates, the
nonlinear solution and the gain are conclusions. The premises are explicit
finite size/history/centered-target bounds and scalar error inequalities. -/
theorem terminal_rows_of_budgets_sparse (n : ℕ) (θ T : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ R r c A C K ζ e₀ B L c' : ℝ,
      0 < R ∧ 0 < r ∧ 0 < c ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧
      0 < ζ ∧ 0 < e₀ ∧ 0 < B ∧ 0 ≤ L ∧ 0 < c' ∧
      (∀ s t, |γ n s t| ≤ R) ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, 1 ≤ Real.log (N:ℝ) →
      ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ e ξ d E x u : ℝ, 0 ≤ e → 0 ≤ ξ → 0 ≤ d → 0 < E →
      E < r → 0 < u → u ≤ 1 → 0 ≤ x → x ≤ e₀*u →
      (Fintype.card (Fin (n+1) → Bool)+n+2:ℝ) *
        (parameterErrorConstant n R*(e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p)) ≤ d →
      d ≤ 1 → 2*d ≤ 1 → C*d ≤ E → K*E ≤ x → e ≤ x →
      Real.log N ^ (5+Fintype.card (Fin (n+1) → Bool))/scale N p ≤ d →
      (p:ℝ)/scale N p ≤ d →
      A*(Real.log N ^ (5+Fintype.card (Fin (n+1) → Bool))/scale N p) ≤ c/2 →
      B*Real.log N ^ (5+Fintype.card (Fin (n+1) → Bool))/scale N p + L*(2*d) ≤ c'/2 →
      ratioConstant (c'/2) 1 *
        (B*Real.log N ^ (5+Fintype.card (Fin (n+1) → Bool))/scale N p + L*(2*d)) ≤ x →
      ∀ sizes : Local.Sizes n, (∀ t, 0 < sizes t) →
      (∀ s t, (N:ℝ)*ν n t/2 ≤ (Local.trials sizes s t:ℝ)) →
      (∀ s t, (Local.trials sizes s t:ℝ) ≤ 2*N*ν n t) →
      (∀ t, |(sizes t:ℝ)-(N:ℝ)*ν n t| ≤ (N:ℝ)*e) →
      (∀ s j, |∑ t, historyMatrix s j t*(sizes t:ℝ)| ≤ ξ*(N:ℝ)/scale N p) →
      u ≤ shift N p sizes →
      ∀ edges : Local.EdgeCounts n,
      (∀ s t, |(edges s t/sizes s-(p:ℝ)*sizes t)/scale N p-ν n t*μ n s t| ≤ E) →
      ∃ σ : History (n+1) → Row (n+1),
        (∀ s t, |σ s t| ≤ R) ∧ (∀ s t, |σ s t-γ n s t| ≤ K*E) ∧
        Local.Solves sizes edges (fun s => rowTilt N p (σ s)) ∧
        (∀ s, c/2 ≤ binomialMass N p sizes s (Local.historySupport sizes s) (σ s)) ∧
        ∀ s b, ζ*u*N ≤ sign b *
          (Local.templateSizes sizes (fun s => rowTilt N p (σ s)) (append s b)-
            (N:ℝ)*ν (n+1) (append s b)) := by
  obtain ⟨R,r,c,A,C,K,hR,hr,hc,hA,hC,hK,hγ,N₁,hN₁,hsolve⟩ :=
    solve_of_history_parameters_sparse n θ T hθlo hθhi hT
  obtain ⟨ζ,hζ,hgain⟩ := template_gain_linear n
  obtain ⟨e₀,he₀,hgain⟩ := hgain R hR.le hγ
  obtain ⟨c',B,L,hc',hB,hL,N₂,hN₂,hsplit⟩ :=
    row_split_sparse_unbounded (n:=n) θ T R hθlo hθhi hT hR.le
  refine ⟨R,r,c,A,C,K,ζ,e₀,B,L,c',hR,hr,hc,hA,hC,hK,hζ,he₀,hB,hL,hc',hγ,
    max N₁ N₂,by omega,?_⟩
  intro N hN hlog p hp e ξ d E x u he hξ hd hE hEr hu hu1 hx hxu
    hcoord hd1 hd2 hCd hKE hex hraw hpraw hAsmall hBsmall hBx
    sizes hs hlo hhi hsize hhist hushift edges htarget
  have hn : 0 < N := by omega
  let q := parameterErrorConstant n R*(e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p)
  have hq : 0 ≤ q := by
    have hk := (parameterErrorConstant_bounds (n:=n) R hR.le).1
    have hp0 := p.property.1
    have hscale := Real.sqrt_nonneg ((p:ℝ)*N)
    dsimp [q,scale]
    positivity
  have hqle : q ≤ d := by
    have hdim : (1:ℝ) ≤ Fintype.card (Fin (n+1) → Bool)+n+2 := by
      nlinarith [Nat.cast_nonneg (α:=ℝ) n,
        Nat.cast_nonneg (α:=ℝ) (Fintype.card (Fin (n+1) → Bool))]
    exact (le_mul_of_one_le_left hq hdim).trans hcoord
  have hparams (s) (σ : Row (n+1)) (hσ : ∀ t, |σ t| ≤ R) :=
    normalized_parameter_budget hn p sizes hs s he hξ hR.le hsize (hhist s) σ hσ
  have hdist (s) (σ : Row (n+1)) (hσ : ∀ t, |σ t| ≤ R) (b) :
      dist (actualNormalizedParameters N p sizes s σ b)
        (targetParameters σ b (shift N p sizes)) ≤ d := by
    obtain ⟨hm,hv,hh,hch⟩ := hparams s σ hσ
    exact (event_parameters_dist_of_budget p sizes s σ hq hm hv hh hch b).trans hcoord
  have hbox (s) (σ : Row (n+1)) (hσ : ∀ t, |σ t| ≤ R) :
      actualNormalizedParameters N p sizes s σ none ∈ gaussianBox n n R 0 := by
    exact history_parameters_mem_of_budget hn p sizes s σ hσ (hlo s) (hhi s)
      (hparams s σ hσ).2.2.1 (hqle.trans hd1)
  obtain ⟨σ,hσ,hclose,hsol,hmass⟩ := hsolve N (by omega) hlog p hp d E hE hEr hCd
    hraw hpraw hAsmall sizes hs hlo hhi (fun s σ hσ =>
      ⟨hbox s σ hσ,hdist s σ hσ none⟩) edges htarget
  refine ⟨σ,hσ,hclose,hsol,hmass,?_⟩
  apply hgain N p sizes σ u (shift N p sizes) x hu hu1 hushift hx hxu hσ
    (fun s t => (hclose s t).trans hKE)
  · intro s
    exact (hsize s).trans (by nlinarith [Nat.cast_nonneg (α:=ℝ) N])
  · intro s b
    have hnorm (b : Option Bool) :
        ‖(actualNormalizedParameters N p sizes s (σ s) b).1-
          (targetParameters (σ s) b (shift N p sizes)).1‖+
        ‖(actualNormalizedParameters N p sizes s (σ s) b).2-
          (targetParameters (σ s) b (shift N p sizes)).2‖ ≤ 2*d := by
      have hh := hdist s (σ s) (hσ s) b
      rw [Prod.dist_eq,max_le_iff,dist_eq_norm,dist_eq_norm] at hh
      linarith [hh.1,hh.2]
    exact ((hsplit N (by omega) hlog p hp s sizes (hlo s) (hhi s) (σ s)
      (hσ s) (shift N p sizes) (2*d) hd2 hnorm hBsmall).2 b).trans hBx

end MajorityDynamics.Idealized.CriticalDay
