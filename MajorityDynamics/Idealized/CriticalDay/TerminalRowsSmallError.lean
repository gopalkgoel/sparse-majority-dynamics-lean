import MajorityDynamics.Idealized.CriticalDay.TerminalRowsSparse

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits
open Binomial.Approximation (SparseRange scale)

/-- Compact terminal-row interface: a single numerical error W, small
relative to a comparison shift, pays every solver and splitting estimate.
No analytic approximation is an assumption. -/
theorem terminal_rows_small_error_sparse (n : ℕ) (θ T : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ R K φ ζ ρ : ℝ, 0 < R ∧ 0 < K ∧ 0 < φ ∧ 0 < ζ ∧ 0 < ρ ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, 1 ≤ Real.log (N:ℝ) →
      ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ W u : ℝ, 0 < W → 0 < u → u ≤ 1 → W ≤ ρ*u →
      Real.log N^(5+Fintype.card (Fin (n+1) → Bool))/scale N p ≤ W →
      1/(N:ℝ) ≤ W → (p:ℝ)/scale N p ≤ W →
      ∀ sizes : Local.Sizes n, (∀ t, 0 < sizes t) →
      (∀ s t, (N:ℝ)*ν n t/2 ≤ (Local.trials sizes s t:ℝ)) →
      (∀ s t, (Local.trials sizes s t:ℝ) ≤ 2*N*ν n t) →
      (∀ t, |(sizes t:ℝ)-(N:ℝ)*ν n t| ≤ (N:ℝ)*W) →
      (∀ s j, |∑ t, historyMatrix s j t*(sizes t:ℝ)| ≤ W*(N:ℝ)/scale N p) →
      u ≤ shift N p sizes →
      ∀ edges : Local.EdgeCounts n,
      (∀ s t, |(edges s t/sizes s-(p:ℝ)*sizes t)/scale N p-ν n t*μ n s t| ≤ W) →
      ∃ σ : History (n+1) → Row (n+1),
        (∀ s t, |σ s t| ≤ R) ∧ (∀ s t, |σ s t-γ n s t| ≤ K*W) ∧
        Local.Solves sizes edges (fun s => rowTilt N p (σ s)) ∧
        (∀ s, φ ≤ binomialMass N p sizes s (Local.historySupport sizes s) (σ s)) ∧
        ∀ s b, ζ*u*N ≤ sign b*
          (Local.templateSizes sizes (fun s => rowTilt N p (σ s)) (append s b)-
            (N:ℝ)*ν (n+1) (append s b)) := by
  obtain ⟨R,r,c,A,C,K,ζ,e₀,B,L,c',hR,hr,hc,hA,hC,hK,hζ,he₀,hB,hL,hc',hγ,
    N₀,hN₀,hrows⟩ := terminal_rows_of_budgets_sparse n θ T hθlo hθhi hT
  let D := 4*(Fintype.card (Fin (n+1) → Bool)+n+2:ℝ)*parameterErrorConstant n R
  have hP : 2 ≤ parameterErrorConstant n R := (parameterErrorConstant_bounds R hR.le).1
  have hdim : (1:ℝ) ≤ Fintype.card (Fin (n+1) → Bool)+n+2 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) n,
      Nat.cast_nonneg (α:=ℝ) (Fintype.card (Fin (n+1) → Bool))]
  have hD1 : 1 ≤ D := by
    dsimp [D]
    nlinarith [mul_le_mul hdim hP (by norm_num : (0:ℝ) ≤ 2) (by linarith)]
  have hD : 0 < D := zero_lt_one.trans_le hD1
  let Q := C*D+1
  have hQ1 : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hQ : 0 < Q := zero_lt_one.trans_le hQ1
  let S := B+2*L*D
  have hS : 0 < S := by dsimp [S]; positivity
  let J := ratioConstant (c'/2) 1
  have hJ : 0 < J := by dsimp [J,ratioConstant]; positivity
  let X := K*Q+J*S+1
  have hX : 0 < X := by dsimp [X]; positivity
  have hX1 : 1 ≤ X := by dsimp [X]; nlinarith [mul_pos hK hQ,mul_pos hJ hS]
  have hKQ : K*Q ≤ X := by dsimp [X]; nlinarith [mul_pos hJ hS]
  have hJS : J*S ≤ X := by dsimp [X]; nlinarith [mul_pos hK hQ]
  let ρ := min (1/(2*D)) (min (r/(2*Q)) (min (c/(2*A))
    (min (c'/(2*S)) (e₀/X))))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρD : ρ ≤ 1/(2*D) := min_le_left _ _
  have hρQ : ρ ≤ r/(2*Q) := (min_le_right _ _).trans (min_le_left _ _)
  have hρA : ρ ≤ c/(2*A) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρS : ρ ≤ c'/(2*S) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hρX : ρ ≤ e₀/X :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨R,X,c/2,ζ,ρ,hR,hX,half_pos hc,hζ,hρ,N₀,hN₀,?_⟩
  intro N hN hlog p hp W u hW hu hu1 hWu hraw hNat hpraw sizes hs hlo hhi
    hsize hhist hushift edges htarget
  have hWρ : W ≤ ρ := hWu.trans (by nlinarith only [hu1,hρ])
  have hDW : 2*(D*W) ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hD)).mp (hWρ.trans hρD)
    nlinarith only [hh]
  have hQW : Q*W < r := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hQ)).mp (hWρ.trans hρQ)
    nlinarith only [hh,hr]
  have hAW : A*W ≤ c/2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hA)).mp (hWρ.trans hρA)
    nlinarith only [hh]
  have hSW : S*W ≤ c'/2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hS)).mp (hWρ.trans hρS)
    nlinarith only [hh]
  have hXW : X*W ≤ e₀*u := by
    have hh := hWu.trans (mul_le_mul_of_nonneg_right hρX hu.le)
    have hh' := mul_le_mul_of_nonneg_left hh hX.le
    have hid : X*(e₀/X*u) = e₀*u := by field_simp
    rw [hid] at hh'
    nlinarith only [hh']
  have hWd : W ≤ D*W := le_mul_of_one_le_left hW.le hD1
  have hWE : W ≤ Q*W := le_mul_of_one_le_left hW.le hQ1
  have hWx : W ≤ X*W := le_mul_of_one_le_left hW.le hX1
  have hsplit :
      B*Real.log N^(5+Fintype.card (Fin (n+1) → Bool))/scale N p+
        L*(2*(D*W)) ≤ S*W := by
    have hh := mul_le_mul_of_nonneg_left hraw hB.le
    rw [← mul_div_assoc] at hh
    dsimp [S]
    nlinarith only [hh]
  obtain ⟨σ,hσ,hclose,hsol,hmass,hgain⟩ := hrows N hN hlog p hp W W (D*W)
    (Q*W) (X*W) u hW.le hW.le (mul_pos hD hW).le (mul_pos hQ hW) hQW hu hu1
    (mul_pos hX hW).le hXW
    (by
      have hh : W+1/(N:ℝ)+W+(p:ℝ)/scale N p ≤ 4*W := by linarith
      have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤
        (Fintype.card (Fin (n+1) → Bool)+n+2:ℝ)*parameterErrorConstant n R by positivity)
      dsimp [D]
      nlinarith only [hh'])
    (by linarith [mul_pos hD hW]) hDW
    (by dsimp [Q]; nlinarith only [hW.le])
    (by nlinarith only [mul_le_mul_of_nonneg_right hKQ hW.le]) hWx
    (hraw.trans hWd) (hpraw.trans hWd)
    ((mul_le_mul_of_nonneg_left hraw hA.le).trans hAW)
    (hsplit.trans hSW)
    ((mul_le_mul_of_nonneg_left hsplit hJ.le).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hJS hW.le]))
    sizes hs hlo hhi hsize hhist hushift edges (fun s t => (htarget s t).trans hWE)
  exact ⟨σ,hσ,fun s t => (hclose s t).trans
    (by nlinarith only [mul_le_mul_of_nonneg_right hKQ hW.le]),hsol,hmass,hgain⟩

end MajorityDynamics.Idealized.CriticalDay
