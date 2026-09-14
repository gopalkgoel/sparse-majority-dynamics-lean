import MajorityDynamics.Idealized.CriticalDay.FiniteCenteredTarget
import MajorityDynamics.Idealized.CriticalDay.FaithfulGeometryBudget
import MajorityDynamics.Idealized.CriticalDay.ReferenceLogBudget

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (scale)

/-- The one error envelope that is small relative to the terminal gain. -/
def terminalError (s a l q : ℝ) : ℝ := (1+a+a^2)/s*l+a*q

theorem terminalError_controls {s a l q : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hl : 1 ≤ l) (hq : 0 ≤ q) :
    0 ≤ terminalError s a l q ∧ l/s ≤ terminalError s a l q ∧
    a/s ≤ terminalError s a l q ∧ a*q ≤ terminalError s a l q ∧
    a*(l/s+a/s+q) ≤ terminalError s a l q := by
  have hl0 : 0 ≤ l := by linarith
  have hls : 0 ≤ l/s := div_nonneg hl0 hs.le
  have hlin : 1 ≤ 1+a+a^2 := by nlinarith [sq_nonneg a]
  have heq : terminalError s a l q = (1+a+a^2)*(l/s)+a*q := by
    unfold terminalError
    ring
  rw [heq]
  have hal : a/s ≤ a*(l/s) := by
    apply (div_le_iff₀ hs).mpr
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left hl ha]
  have ha2 : a*(a/s) ≤ a^2*(l/s) := by
    nlinarith only [mul_le_mul_of_nonneg_left hal ha]
  have h0 : 0 ≤ (1+a+a^2)*(l/s)+a*q := by positivity
  have h1 : l/s ≤ (1+a+a^2)*(l/s)+a*q := by
    nlinarith [mul_le_mul_of_nonneg_right hlin hls,mul_nonneg ha hq]
  have h2 : a*(l/s) ≤ (1+a+a^2)*(l/s)+a*q := by
    nlinarith [mul_nonneg (sq_nonneg a) hls,mul_nonneg ha hq]
  refine ⟨h0,h1,hal.trans h2,?_,?_⟩
  · exact le_add_of_nonneg_left (mul_nonneg (by positivity) hls)
  · nlinarith only [ha2,hls]

theorem faithful_budget_of_numerical {n N : ℕ} {p T δ τ E : ℝ}
    {a : Process.Data} {η : History (n+1) → ℤ}
    {edges : History (n+1) → History (n+1) → ℤ}
    (hT : 0 < T) (hp : 0 ≤ p) (hτ : T⁻¹ ≤ τ)
    (hE : T^2*(N:ℝ)^(-δ) ≤ E)
    (hf : FaithfulNumericalData N p T δ τ a n η edges) :
    FaithfulBudgetData N p τ E a n η edges := by
  have hτ0 : 0 < τ := (inv_pos.mpr hT).trans_le hτ
  have hTτ : 1 ≤ T*τ := by
    have hh := mul_le_mul_of_nonneg_left hτ hT.le
    simpa [hT.ne'] using hh
  have hq : 0 ≤ (N:ℝ)^(-δ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hbase : T*(N:ℝ)^(-δ) ≤ τ*E := by
    have h1 := mul_le_mul_of_nonneg_left hTτ (mul_nonneg hT.le hq)
    have h2 := mul_le_mul_of_nonneg_left hE hτ0.le
    nlinarith only [h1,h2]
  constructor
  · intro t
    have hh := mul_le_mul_of_nonneg_right hbase (sizeScale_nonneg N p n)
    exact (hf.sizes t).trans (by nlinarith only [hh])
  · intro s t
    have hβ := betaScale_nonneg N p n
    have hmul := mul_le_mul_of_nonneg_right hbase
      (show 0 ≤ betaScale N p n*(N:ℝ)^2*p by positivity)
    exact (hf.edges s t).trans (by nlinarith only [hmul])

/-- Uniform finite faithful target reduction retaining the sharp raw error.
The only smallness condition is on an explicitly displayed scalar. -/
theorem faithful_centered_terminal_budget (n ell : ℕ) (T : ℝ) (hT : 1 < T) :
    ∃ radius K F : ℝ, 0 < radius ∧ 0 < K ∧ 0 < F ∧
      ∀ N : ℕ, 0 < N → 1 ≤ Real.log (N:ℝ) →
      ∀ p : Binomial.Probability, 1 ≤ scale N p →
      ∀ a : Process.Data, Process.LevelEstimates N p ell (a.state n) →
      (∀ t, 0 < (a.state n).sizes t) →
      (∀ t, ((a.state n).sizes t:ℝ) ≤ 2*N*ν n t) →
      ∀ δ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n+1) → ℤ, ∀ edges : History (n+1) → History (n+1) → ℤ,
      (∀ t, 0 < η t) →
      FaithfulNumericalData N (p:ℝ) T δ τ a n η edges →
      let z := Real.log N^ell/scale N p+betaScale N p n+(N:ℝ)^(-δ)
      K*z < radius →
      ∀ s t, |((edges s t:ℝ)/(η s:ℝ)-(p:ℝ)*(η t:ℝ))/scale N p-ν n t*μ n s t| ≤
        F*terminalError (scale N p) (betaScale N p n*scale N p)
          (Real.log N^ell) ((N:ℝ)^(-δ)) := by
  classical
  obtain ⟨radius,hradius,F,hF,hfinite⟩ := faithful_target_budget n
  obtain ⟨Kr,hKr,href⟩ := reference_coordinates_log_budget n ell
  let K := Kr+T+T^2+1
  have hT0 : 0 < T := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hKrK : Kr ≤ K := by dsimp [K]; nlinarith [sq_nonneg T]
  have hTK : T ≤ K := by dsimp [K]; nlinarith [sq_nonneg T]
  have hT2K : T^2 ≤ K := by dsimp [K]; linarith
  let M := 1+∑ s : History (n+1), ∑ t : History (n+1), abs (2*ν n t+|μ n s t|)
  have hM : 0 < M := by dsimp [M]; positivity
  have hMb (s t) : 2*ν n t+|μ n s t| ≤ M := by
    have h1 := Finset.single_le_sum (fun t _ => abs_nonneg (2*ν n t+|μ n s t|)) (Finset.mem_univ t)
    have h2 := Finset.single_le_sum (fun s _ =>
      show 0 ≤ ∑ t, abs (2*ν n t+|μ n s t|) by positivity) (Finset.mem_univ s)
    dsimp [M]
    linarith [le_abs_self (2*ν n t+|μ n s t|)]
  refine ⟨radius,K,M+T*(F+1)*K,hradius,hK,by positivity,?_⟩
  intro N hN hlog p hs1 a hspec hsizes hupper δ τ hτ hτT η edges hη hf
  dsimp only
  intro hsmall s t
  let S := scale N p
  let b := betaScale N p n
  let l := Real.log N^ell
  let q := (N:ℝ)^(-δ)
  let z := l/S+b+q
  have hs : 0 < S := zero_lt_one.trans_le hs1
  have hb : 0 < b := by dsimp [b,betaScale]; positivity
  have hl : 1 ≤ l := one_le_pow₀ hlog
  have hq : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hl0 : 0 ≤ l/S := by positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hlz : l/S ≤ z := by dsimp [z]; linarith
  have hbz : b ≤ z := by dsimp [z]; linarith
  have hqz : q ≤ z := by dsimp [z]; linarith
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hbudget := faithful_budget_of_numerical hT0 p.property.1.le hτ
    (mul_le_mul hT2K hqz hq hK.le) hf
  have hcoords := href N hN hlog p hs1 (a.state n) hspec hupper
  have htarget := hfinite N p τ (K*z) hN p.property.1 hτ0
    (mul_nonneg hK.le hz) hsmall a hsizes
    (fun s => (hcoords.1 s).trans (mul_le_mul hKrK hlz hl0 hK.le))
    (fun s t => (hcoords.2 s t).trans (mul_le_mul hKrK hlz hl0 hK.le))
    (mul_le_mul (hτT.trans hTK) hbz hb.le hK.le) η edges hη hbudget
  have hreference (s t) :
      |((a.state n).edges s t/(a.state n).sizes s-(p:ℝ)*(a.state n).sizes t)/S-
        ν n t*μ n s t| ≤ M*(l/S) :=
    (hspec.normalized_target hN (by linarith) hsizes hupper s t).trans
      (mul_le_mul_of_nonneg_right (hMb s t) hl0)
  have hcenter := centered_target_budget hN p a hτ0 (mul_nonneg hK.le hz)
    η edges hbudget hreference htarget s t
  have hctl := terminalError_controls hs (mul_pos hb hs).le hl hq
  have hbS : (b*S)/S = b := mul_div_cancel_right₀ b hs.ne'
  have hfirst := mul_le_mul_of_nonneg_left hctl.2.1 hM.le
  have hlast := mul_le_mul_of_nonneg_left hctl.2.2.2.2
    (show 0 ≤ T*(F+1)*K by positivity)
  rw [hbS] at hlast
  have ht := mul_le_mul_of_nonneg_right hτT
    (show 0 ≤ (b*S)*(F+1)*(K*z) by positivity)
  dsimp only [z] at hlast ht
  dsimp only [S,b,l,q,z] at hfirst hlast ht
  nlinarith only [hcenter,hfirst,hlast,ht]

end MajorityDynamics.Idealized.CriticalDay
