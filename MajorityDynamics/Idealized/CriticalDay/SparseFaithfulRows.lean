import MajorityDynamics.Idealized.CriticalDay.TerminalRowsSmallError
import MajorityDynamics.Idealized.CriticalDay.TerminalAsymptotics
import MajorityDynamics.Idealized.CriticalDay.SparseTiltBound

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt RowLimits
open Binomial.Approximation (SparseRange scale)

/-- The actual terminal row theorem from faithful data at the flexible
stopping window. No row-approximation or numerical-budget premise remains. -/
theorem terminal_faithful_rows_sparse (θ T δ r : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hr : 0 < r) (hr3 : r ≤ 1/3) (hgap : r/4 < δ) (n ell : ℕ) :
    ∃ R φ ζ : ℝ, 0 < R ∧ 0 < φ ∧ 0 < ζ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, SparseRange θ T N p →
      scale N p^r ≤ (betaScale N p n*scale N p)*scale N p →
      betaScale N p n*scale N p ≤ scale N p^r →
      ∀ a : Process.Data, Process.LevelEstimates N p ell (a.state n) →
      Process.StateSymmetric (a.state n) →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n+1) → ℤ, ∀ edges : History (n+1) → History (n+1) → ℤ,
      FaithfulNumericalData N (p:ℝ) T δ τ a n η edges →
      (∀ t, 0 < η t) ∧ (∀ t, ((naturalSizes η t:ℕ):ℝ) = (η t:ℝ)) ∧
      (∀ t, |(η t:ℝ)-(N:ℝ)*ν n t| ≤ (N:ℝ)*ε) ∧
      (∀ s j, |∑ t, historyMatrix s j t*(η t:ℝ)| ≤ ε*(N:ℝ)/scale N p) ∧
      (∀ s t, |((edges s t:ℝ)/(η s:ℝ)-(p:ℝ)*(η t:ℝ))/scale N p-
        ν n t*μ n s t| ≤ ε) ∧
      ∃ σ : History (n+1) → Row (n+1),
        (∀ s t, |σ s t| ≤ R) ∧
        Local.Solves (naturalSizes η) (realEdges edges) (fun s => rowTilt N p (σ s)) ∧
        (∀ s, φ ≤ binomialMass N p (naturalSizes η) s
          (Local.historySupport (naturalSizes η) s) (σ s)) ∧
        ∀ s b, ζ*min (betaScale N p n*scale N p) 1*N ≤ sign b*
          (Local.templateSizes (naturalSizes η) (fun s => rowTilt N p (σ s)) (append s b)-
            (N:ℝ)*ν (n+1) (append s b)) := by
  classical
  have hT0 : 0 < T := by linarith
  have hδ : 0 < δ := lt_trans (by positivity : 0 < r/4) hgap
  let k := max ell (5+Fintype.card (Fin (n+1) → Bool))
  obtain ⟨R,K,φ,ζ,ρ,hR,hK,hφ,hζ,hρ,N₀,hN₀,hrows⟩ :=
    terminal_rows_small_error_sparse n θ T hθlo hθhi hT
  obtain ⟨radius,Kt,F,hradius,hKt,hF,hcenter⟩ :=
    faithful_centered_terminal_budget n k T hT
  obtain ⟨v,hv,hvle⟩ := finite_common_positive (ν n) (ν_positive n)
  have hlead := lead_pos n
  let lam := min 1 (T⁻¹*lead n/2)
  have hlam : 0 < lam := by dsimp [lam]; exact lt_min zero_lt_one (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  let D := (Fintype.card (History (n+1)):ℝ)*T
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let U := comparisonConstant n T
  have hU : 0 ≤ U := hT0.le.trans (comparisonConstant_ge n hT0.le)
  let C := 1+U+D+F
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hCU : 1+U ≤ C := by dsimp [C]; linarith
  have hCD : D ≤ C := by dsimp [C]; linarith
  have hCF : F ≤ C := by dsimp [C]; linarith
  refine ⟨R,φ,ζ*lam,hR,hφ,mul_pos hζ hlam,?_⟩
  intro ε hε
  let b := min (ρ*lam) (min ε (v/4))
  have hb : 0 < b := by dsimp [b]; positivity
  have hbρ : b ≤ ρ*lam := min_le_left _ _
  have hbε : b ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hbv : b ≤ v/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hlarge : ∀ᶠ N : ℕ in atTop, 4*((2*n+6:ℕ):ℝ)/v ≤ N :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop N₀,
    eventually_basic_sparse θ T hθlo hθhi hT,
    Process.eventually_level_sizes_sparse (n:=n) θ T k hθhi hT0,
    terminal_error_small_uniform θ T r δ C Kt b radius k hθhi hT0 hr hr3
      hgap hC hKt hb hradius,
    eventually_rpow_neg_le δ 1 hδ zero_lt_one,
    eventually_rpow_neg_le δ ((T⁻¹*lead n/2)/(D+1)) hδ (by positivity),
    hlarge] with N hNN hbasic hlev hasym hpow hshift hlarge
  intro p hp halo hahi a hspec hsym τ hτ hτT η edges hf
  have hn := hbasic.1
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  have hs1 : 1 ≤ scale N p := (hbasic.2.2 p hp).1
  have hs : 0 < scale N p := zero_lt_one.trans_le hs1
  have hlog : 1 ≤ Real.log (N:ℝ) := by linarith [hbasic.2.1]
  have hspec' := hspec.mono hlog (show ell ≤ k from le_max_left _ _)
  have hlevel := hlev.2 p hp (a.state n) hspec'
  have ha : 0 < betaScale N p n*scale N p := by unfold betaScale; positivity
  let w := terminalError (scale N p) (betaScale N p n*scale N p) (Real.log N^k) ((N:ℝ)^(-δ))
  obtain ⟨hw,hwb,hz⟩ := hasym.2.2 p hp (betaScale N p n*scale N p) ha halo hahi
  change 0 < w at hw
  change C*w ≤ b*min (betaScale N p n*scale N p) 1 at hwb
  have hCWb : C*w ≤ b := hwb.trans (by nlinarith only [min_le_right (betaScale N p n*scale N p) 1,hb])
  have hCWε : C*w ≤ ε := hCWb.trans hbε
  have hcontrols := terminalError_controls hs ha.le
    (one_le_pow₀ hlog : 1 ≤ Real.log N^k) (Real.rpow_nonneg hNr.le (-δ))
  have hraw : Real.log N^k/scale N p ≤ w := hcontrols.2.1
  have hbeta : betaScale N p n ≤ w := by
    simpa only [mul_div_cancel_right₀ _ hs.ne'] using hcontrols.2.2.1
  have hxi : D*(betaScale N p n*scale N p)*(N:ℝ)^(-δ) ≤ C*w := by
    have hh := mul_le_mul_of_nonneg_left hcontrols.2.2.2.1 hD
    have hh' := mul_le_mul_of_nonneg_right hCD hw.le
    nlinarith only [hh,hh']
  have hCWpos : 0 < C*w := mul_pos hC hw
  have hsize : ∀ t, |(η t:ℝ)-(N:ℝ)*ν n t| ≤ (N:ℝ)*(C*w) := by
    have hh := faithful_relative_size_budget hn hT0.le
      ((inv_pos.mpr hT0).trans_le hτ).le hτT hpow hf
      (fun t => by simpa only [scale,div_mul_eq_mul_div,mul_div_assoc] using hspec'.sizes t)
    intro t
    apply (hh t).trans
    apply mul_le_mul_of_nonneg_left _ hNr.le
    have hu := mul_le_mul_of_nonneg_left hbeta hU
    have hc := mul_le_mul_of_nonneg_right hCU hw.le
    change Real.log N^k/scale N p+U*betaScale N p n ≤ C*w
    nlinarith only [hraw,hu,hc]
  obtain ⟨hη,hcast,_,hlo,hhi⟩ := integer_geometry_of_relative_error hCWpos.le η hsize
    (fun t => by linarith [hCWb.trans hbv,hvle t])
    (fun t => by
      have hl := (div_le_iff₀ hv).mp hlarge
      have hvN := mul_le_mul_of_nonneg_left (hvle t) hNr.le
      nlinarith only [hl,hvN])
  have hsizes : ∀ t, 0 < naturalSizes η t := by
    intro t
    have hh : (0:ℝ) < (naturalSizes η t:ℕ) := by rw [hcast]; exact_mod_cast hη t
    exact_mod_cast hh
  have hhist : ∀ s j, |∑ t, historyMatrix s j t*(naturalSizes η t:ℝ)| ≤
      (C*w)*N/scale N p := by
    intro s j
    exact (faithful_history_budget hn hsym hcast hf s j).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxi hNr.le) hs.le)
  have htarget : ∀ s t,
      |((edges s t:ℝ)/(η s:ℝ)-(p:ℝ)*(η t:ℝ))/scale N p-ν n t*μ n s t| ≤ C*w := by
    intro s t
    apply (hcenter N hn hlog p hs1 a hspec' (fun t => (hlevel t).1)
      (fun t => (hlevel t).2.2.le) δ τ hτ hτT η edges hη hf
      (by simpa only [mul_div_cancel_right₀ _ hs.ne'] using hz) s t).trans
    exact mul_le_mul_of_nonneg_right hCF hw.le
  have hshiftSmall : D*(N:ℝ)^(-δ) ≤ T⁻¹*lead n/2 := by
    have hh := mul_le_mul_of_nonneg_left hshift (show 0 ≤ D+1 by positivity)
    have hid : (D+1)*((T⁻¹*lead n/2)/(D+1)) = T⁻¹*lead n/2 := by field_simp
    rw [hid] at hh
    have hq : 0 ≤ (N:ℝ)^(-δ) := Real.rpow_nonneg hNr.le _
    nlinarith only [hh,hq]
  have hushift : lam*min (betaScale N p n*scale N p) 1 ≤ shift N p (naturalSizes η) := by
    apply le_trans _ (faithful_shift_lower_of_budget hn hT0 hτ hsym hcast hf hshiftSmall)
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (betaScale N p n*scale N p) 1) hlam.le
    have h2 := mul_le_mul_of_nonneg_right (show lam ≤ T⁻¹*lead n/2 from min_le_right _ _) ha.le
    exact h1.trans h2
  have hu : 0 < lam*min (betaScale N p n*scale N p) 1 := mul_pos hlam (lt_min ha zero_lt_one)
  have hu1 : lam*min (betaScale N p n*scale N p) 1 ≤ 1 := by
    have hh := mul_le_mul hlam1 (min_le_right (betaScale N p n*scale N p) 1)
      (le_of_lt (lt_min ha zero_lt_one)) zero_le_one
    simpa using hh
  have hWraw : Real.log N^(5+Fintype.card (Fin (n+1) → Bool))/scale N p ≤ C*w :=
    (div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog (le_max_right _ _)) hs.le).trans
      (hraw.trans (le_mul_of_one_le_left hw.le hC1))
  have hWnat : 1/(N:ℝ) ≤ C*w := by
    have hSN : scale N p ≤ N := (hbasic.2.2 p hp).2.1
    have hh : 1/(N:ℝ) ≤ 1/scale N p := one_div_le_one_div_of_le hs hSN
    exact hh.trans ((div_le_div_of_nonneg_right (one_le_pow₀ hlog) hs.le).trans
      (hraw.trans (le_mul_of_one_le_left hw.le hC1)))
  have hWp : (p:ℝ)/scale N p ≤ C*w :=
    (div_le_div_of_nonneg_right (p.property.2.le.trans (one_le_pow₀ hlog)) hs.le).trans
      (hraw.trans (le_mul_of_one_le_left hw.le hC1))
  obtain ⟨σ,hσ,_,hsol,hmass,hgain⟩ := hrows N hNN hlog p hp (C*w)
    (lam*min (betaScale N p n*scale N p) 1) hCWpos hu hu1
    (hwb.trans (by
      have hh := mul_le_mul_of_nonneg_right hbρ (le_of_lt (lt_min ha zero_lt_one))
      nlinarith only [hh]))
    hWraw hWnat hWp (naturalSizes η) hsizes hlo hhi
    (fun t => by simpa only [hcast] using hsize t) hhist hushift (realEdges edges)
    (fun s t => by simpa only [realEdges,hcast] using htarget s t)
  refine ⟨hη,hcast,fun t => (hsize t).trans (mul_le_mul_of_nonneg_left hCWε hNr.le),
    ?_,fun s t => (htarget s t).trans hCWε,σ,hσ,hsol,hmass,?_⟩
  · intro s j
    have hh := (hhist s j).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCWε hNr.le) hs.le)
    simpa only [hcast] using hh
  · intro s b
    simpa only [mul_assoc] using hgain s b

end MajorityDynamics.Idealized.CriticalDay
