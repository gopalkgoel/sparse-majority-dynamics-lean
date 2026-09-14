import MajorityDynamics.Probability.HypergeometricTiltTail.Numerics

noncomputable section
namespace MajorityDynamics.Probability.HypergeometricTiltTail.Numerics

/-- Consequences for the actual population, subset and integer degree after casting. -/
theorem basic_bounds {N : ℕ} {p T M H h L d : ℝ} (hT : 1 < T)
    (r : Regime N p T) (hMlo : (N:ℝ)-1 ≤ M) (_hMhi : M ≤ N)
    (hhlo : (N:ℝ)/T ≤ h) (hhhi : h ≤ N-(N:ℝ)/T) (hH : |H-h| ≤ 1)
    (hL : (N:ℝ)/T ≤ L) (hd : |d-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ)) :
    0 < (N:ℝ) ∧ (N:ℝ)/(2*T) ≤ H ∧ (N:ℝ)/(2*T) ≤ M-H ∧
    0 < H ∧ H < M ∧ 0 < L ∧ 0 < d ∧ d < M ∧ d ≤ 2*p*N := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < (N:ℝ) := by linarith [r.N_large]
  have hN4 : 4 ≤ (N:ℝ) := by linarith [r.N_large]
  have hNT : 4 ≤ (N:ℝ)/T := (le_div_iff₀ hT0).mpr (by linarith [r.N_large])
  have heq : (N:ℝ)/(2*T) = ((N:ℝ)/T)/2 := by ring
  have hHab := abs_le.mp hH
  have hdab := abs_le.mp hd
  have hlo : (N:ℝ)/(2*T) ≤ H := by rw [heq]; linarith
  have hcomp : (N:ℝ)/(2*T) ≤ M-H := by rw [heq]; linarith
  have hpos : 0 < (N:ℝ)/(2*T) := by positivity
  have hps := mul_le_mul_of_nonneg_right r.p_small hN0.le
  refine ⟨hN0,hlo,hcomp,hpos.trans_le hlo,by linarith, (div_pos hN0 hT0).trans_le hL,?_,?_,?_⟩
  · linarith [r.degree_error,r.degree_large]
  · nlinarith [r.degree_error]
  · linarith [r.degree_error,r.degree_large]

/-- The hypergeometric center differs from the original paper center by at most
 twice the original degree-window radius, including one deleted vertex. -/
theorem center_error {N p M H h d : ℝ} (_hN : 0 < N) (hp : 0 < p)
    (hp1 : p ≤ 1/8) (hx : 4 ≤ p*N) (hlog : 1 ≤ Real.log N)
    (hM : 0 < M) (hMlo : N-1 ≤ M) (hMhi : M ≤ N)
    (hH0 : 0 ≤ H) (hHM : H ≤ M) (hH : |H-h| ≤ 1)
    (hd : |d-p*N| ≤ Real.sqrt (p*N)*Real.log N) :
    |(d/M)*H-p*h| ≤ 2*Real.sqrt (p*N)*Real.log N := by
  have hratio0 : 0 ≤ H/M := div_nonneg hH0 hM.le
  have hratio1 : H/M ≤ 1 := (div_le_one hM).mpr hHM
  have hdiff0 : 0 ≤ N-M := by linarith
  have hdiff1 : N-M ≤ 1 := by linarith
  have heq : (d/M)*H-p*h = (d-p*N)*(H/M)+p*(N-M)*(H/M)+p*(H-h) := by
    field_simp
    ring
  rw [heq]
  have hfirst : |(d-p*N)*(H/M)| ≤ Real.sqrt (p*N)*Real.log N := by
    rw [abs_mul, abs_of_nonneg hratio0]
    exact (mul_le_mul_of_nonneg_left hratio1 (abs_nonneg _)).trans (by simpa using hd)
  have hsecond : |p*(N-M)*(H/M)| ≤ p := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hratio1 (mul_nonneg hp.le hdiff0)]
  have hthird : |p*(H-h)| ≤ p := by
    rw [abs_mul, abs_of_pos hp]
    simpa using mul_le_mul_of_nonneg_left hH hp.le
  have hs : 2 ≤ Real.sqrt (p*N) := by
    have := Real.sqrt_le_sqrt hx
    norm_num at this
    exact this
  have hsl : 2 ≤ Real.sqrt (p*N)*Real.log N := by nlinarith
  calc
    _ ≤ |(d-p*N)*(H/M)|+|p*(N-M)*(H/M)|+|p*(H-h)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2*Real.sqrt (p*N)*Real.log N := by linarith

theorem deviation_conversion {N : ℕ} {p T M H h d t : ℝ} (hT : 1 < T)
    (r : Regime N p T) (hN : 0 < (N:ℝ)) (hM : 0 < M)
    (hMlo : (N:ℝ)-1 ≤ M) (hMhi : M ≤ N)
    (hH0 : 0 ≤ H) (hHM : H ≤ M) (hh : (N:ℝ)/T ≤ h) (hH : |H-h| ≤ 1)
    (hd : |d-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ))
    (htau : (Real.log (N:ℝ))^100 ≤ |(t-p*h)/Real.sqrt (p*h)|) :
    |(t-p*h)/Real.sqrt (p*h)| *Real.sqrt (p*h)/2 ≤ |t-(d/M)*H| := by
  have hT0 : 0 < T := by linarith
  have hh0 : 0 < h := (div_pos hN hT0).trans_le hh
  have hs0 : 0 < Real.sqrt (p*h) := Real.sqrt_pos.mpr (mul_pos r.p_pos hh0)
  have hs : Real.sqrt (p*N) ≤ Real.sqrt T*Real.sqrt (p*h) := by
    rw [← Real.sqrt_mul hT0.le]
    apply Real.sqrt_le_sqrt
    have hh' := (div_le_iff₀ hT0).mp hh
    nlinarith [mul_le_mul_of_nonneg_left hh' r.p_pos.le]
  have hcenter := center_error hN r.p_pos r.p_small r.degree_large r.log_large
    hM hMlo hMhi hH0 hHM hH hd
  have hgap : 4*Real.sqrt T*Real.log (N:ℝ) ≤ |(t-p*h)/Real.sqrt (p*h)| := by
    have hprod : 0 ≤ Real.sqrt T*Real.log (N:ℝ) := by positivity
    linarith [r.log_gap]
  have herr : 2*Real.sqrt (p*N)*Real.log (N:ℝ) ≤
      |(t-p*h)/Real.sqrt (p*h)| *Real.sqrt (p*h)/2 := by
    have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ Real.log (N:ℝ) by linarith [r.log_large])
    have h2 := mul_le_mul_of_nonneg_right hgap hs0.le
    nlinarith
  have hidentity : |(t-p*h)/Real.sqrt (p*h)| *Real.sqrt (p*h) = |t-p*h| := by
    rw [abs_div,abs_of_pos hs0,div_mul_cancel₀ _ hs0.ne']
  have htriangle : |t-p*h| ≤ |t-(d/M)*H|+|(d/M)*H-p*h| := by
    calc
      _ = |(t-(d/M)*H)+((d/M)*H-p*h)| := congrArg abs (by ring)
      _ ≤ _ := abs_add_le _ _
  linarith

theorem draw_below_child {N : ℕ} {p T J d : ℝ} (hT : 1 < T)
    (r : Regime N p T) (hJ : (N:ℝ)/(2*T) ≤ J) (hd : d ≤ 2*p*N) : d < J := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < (N:ℝ) := by linarith [r.N_large]
  have hh := mul_le_mul_of_nonneg_right r.p_tiny hN0.le
  have heq : 2*(1/(8*T)*(N:ℝ)) = (N:ℝ)/(4*T) := by ring
  have hstrict : (N:ℝ)/(4*T) < (N:ℝ)/(2*T) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 4*T) (by positivity : 0 < 2*T)).mpr
    nlinarith
  linarith

theorem coefficient_bound {N : ℕ} {p T L : ℝ} (hT : 1 < T)
    (r : Regime N p T) (hL : (N:ℝ)/T ≤ L) :
    (1+p)*Real.log (N:ℝ)/Real.sqrt (p*L) ≤ 1 := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < (N:ℝ) := by linarith [r.N_large]
  have hL0 : 0 < L := (div_pos hN0 hT0).trans_le hL
  have hsL : 0 < Real.sqrt (p*L) := Real.sqrt_pos.mpr (mul_pos r.p_pos hL0)
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hs : Real.sqrt (p*N) ≤ Real.sqrt T*Real.sqrt (p*L) := by
    rw [← Real.sqrt_mul hT0.le]
    apply Real.sqrt_le_sqrt
    have hh := (div_le_iff₀ hT0).mp hL
    nlinarith [mul_le_mul_of_nonneg_left hh r.p_pos.le]
  have hc : 2*Real.log (N:ℝ) ≤ Real.sqrt (p*L) := by
    have hh := r.coefficient.trans hs
    nlinarith
  apply (div_le_one hsL).mpr
  have hl : 0 ≤ Real.log (N:ℝ) := by linarith [r.log_large]
  nlinarith [mul_le_mul_of_nonneg_right r.p_small hl]

/-- A generous quadratic exponent valid for the complete feasible count range. -/
theorem tail_exponent {x T h N p τ r μ : ℝ} (hT : 1 < T) (hx : 0 < x)
    (hxid : x = p*N) (hp : 0 < p) (hN : 0 < N)
    (hh : N/T ≤ h) (hr : 0 ≤ r) (hμ : 0 < μ) (hμhi : μ ≤ 2*x)
    (hrhi : r ≤ 4*x) (hrlo : |τ| *Real.sqrt (p*h)/2 ≤ r) :
    τ^2/(32*T) ≤ r^2/(2*μ+2*r/3) := by
  have hT0 : 0 < T := by linarith
  have hh0 : 0 < h := (div_pos hN hT0).trans_le hh
  have hden : 0 < 2*μ+2*r/3 := by linarith
  have hph : x/T ≤ p*h := by
    rw [hxid]
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hh hp.le
  have hsq : τ^2*(p*h) ≤ 4*r^2 := by
    have hs := Real.sq_sqrt (show 0 ≤ p*h by positivity)
    have hh' := mul_self_le_mul_self (show 0 ≤ |τ| * Real.sqrt (p*h)/2 by positivity) hrlo
    nlinarith [sq_abs τ]
  have hlower : τ^2*x ≤ 4*T*r^2 := by
    have hh' := (div_le_iff₀ hT0).mp hph
    have hm := mul_le_mul_of_nonneg_left hh' (sq_nonneg τ)
    nlinarith [mul_le_mul_of_nonneg_left hsq hT0.le]
  apply (div_le_div_iff₀ (by positivity : 0 < 32*T) hden).mpr
  have hdenhi : 2*μ+2*r/3 ≤ 8*x := by linarith
  have hm := mul_le_mul_of_nonneg_left hdenhi (sq_nonneg τ)
  nlinarith

theorem hypergeometric_bounds {x M H d t : ℝ} (hx : 0 < x) (hM : 0 < M)
    (hH : 0 < H) (hHM : H ≤ M) (hd : 0 < d) (hdx : d ≤ 2*x)
    (ht : 0 ≤ t) (htd : t ≤ d) :
    0 < (d/M)*H ∧ (d/M)*H ≤ 2*x ∧ |t-(d/M)*H| ≤ 4*x := by
  have hq : 0 < d/M := div_pos hd hM
  have hμ : 0 < (d/M)*H := mul_pos hq hH
  have hμd : (d/M)*H ≤ d := by
    have hh := mul_le_mul_of_nonneg_left hHM hq.le
    simpa [div_mul_cancel₀ _ hM.ne'] using hh
  refine ⟨hμ,hμd.trans hdx,?_⟩
  rw [abs_le]
  constructor <;> linarith

end MajorityDynamics.Probability.HypergeometricTiltTail.Numerics
