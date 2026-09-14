import MajorityDynamics.Probability.HypergeometricTiltTail.NumericData
import MajorityDynamics.GraphProcess.KernelInputs.SparseNumerics
import MajorityDynamics.Binomial.SparseRange

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.Probability.HypergeometricTiltTail.Numerics

structure SparseRegime (N : ℕ) (p T : ℝ) : Prop where
  N_large : 4*T ≤ (N:ℝ)
  log_large : 1 ≤ Real.log (N:ℝ)
  p_pos : 0 < p
  p_small : p ≤ 1/8
  p_tiny : p ≤ 1/(8*T)
  degree_large : 4 ≤ p*N
  degree_error : Real.sqrt (p*N)*Real.log (N:ℝ) ≤ p*N/2
  normalized_density : p*Real.sqrt (p*N) ≤ 1
  coefficient : 2*Real.sqrt T*Real.log (N:ℝ) ≤ Real.sqrt (p*N)
  log_gap : 16*Real.sqrt T*Real.log (N:ℝ) ≤ (Real.log (N:ℝ))^100


theorem uniform_regime_sparse {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-(1/2 : ℝ)) → SparseRegime N p T := by
  have hT0 : 0 < T := by linarith
  obtain ⟨N₁,h₁⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L:=4) (by norm_num) (U:=1/(8*T)) (by positivity) (M:=4*T) (by positivity)
  obtain ⟨N₂,h₂⟩ := GraphProcess.KernelInputs.Numerics.eventually_log_degree_sparse
    (a:=1) (b:=1/2) (C:=1/(2*Real.sqrt T)) hθlo hθhi hT (by norm_num) (by positivity)
  obtain ⟨N₃,h₃⟩ := eventually_atTop.mp
    (Binomial.Approximation.sparseRange_small_parameters θ T hT0)
  obtain ⟨X,_,hX⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=1) (b:=100) (A:=16*Real.sqrt T) (B:=1) (by norm_num) zero_lt_one
  obtain ⟨N₄,h₄⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max 1 X))
  refine ⟨max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro N hN p hlo hhi
  have hn1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hn2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hn3 : N₃ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hn4 : N₄ ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  obtain ⟨hN0,hp,hsize,hdegree,hps⟩ := h₁ N hn1 p hlo hhi
  have hlog : 1 ≤ Real.log (N:ℝ) := (le_max_left _ _).trans (h₄ N hn4)
  have hcoeff := h₂ N hn2 p hlo hhi
  rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at hcoeff
  have hsT : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT.le
  have hcoeff' : 2*Real.sqrt T*Real.log (N:ℝ) ≤ Real.sqrt (p*N) := by
    have hh := (le_div_iff₀ (show 0 < 2*Real.sqrt T by positivity)).mp
      (show Real.log (N:ℝ) ≤ Real.sqrt (p*N)/(2*Real.sqrt T) by simpa [div_eq_mul_inv,mul_comm] using hcoeff)
    nlinarith
  have herror : Real.sqrt (p*N)*Real.log (N:ℝ) ≤ p*N/2 := by
    have hbase : 2*Real.log (N:ℝ) ≤ Real.sqrt (p*N) := by
      nlinarith [mul_le_mul_of_nonneg_right hsT (show 0 ≤ Real.log (N:ℝ) by linarith)]
    have hh := mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg (p*N))
    nlinarith [Real.sq_sqrt (show 0 ≤ p*N by positivity)]
  have hps1 : p ≤ 1/8 := hps.trans ((div_le_div_iff₀ (by positivity : (0:ℝ)<8*T) (by norm_num : (0:ℝ)<8)).mpr (by nlinarith))
  refine ⟨hsize,hlog,hp,hps1,hps,hdegree,herror,(h₃ N hn3 ⟨p,hp,by linarith⟩ ⟨hlo,hhi⟩).2,hcoeff',?_⟩
  simpa [Real.rpow_one, Real.rpow_natCast] using hX (Real.log (N:ℝ))
    ((le_max_right _ _).trans (h₄ N hn4))


theorem basic_bounds_sparse {N : ℕ} {p T M H h L d : ℝ} (hT : 1 < T)
    (r : SparseRegime N p T) (hMlo : (N:ℝ)-1 ≤ M) (_hMhi : M ≤ N)
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

theorem deviation_conversion_sparse {N : ℕ} {p T M H h d t : ℝ} (hT : 1 < T)
    (r : SparseRegime N p T) (hN : 0 < (N:ℝ)) (hM : 0 < M)
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

theorem draw_below_child_sparse {N : ℕ} {p T J d : ℝ} (hT : 1 < T)
    (r : SparseRegime N p T) (hJ : (N:ℝ)/(2*T) ≤ J) (hd : d ≤ 2*p*N) : d < J := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < (N:ℝ) := by linarith [r.N_large]
  have hh := mul_le_mul_of_nonneg_right r.p_tiny hN0.le
  have heq : 2*(1/(8*T)*(N:ℝ)) = (N:ℝ)/(4*T) := by ring
  have hstrict : (N:ℝ)/(4*T) < (N:ℝ)/(2*T) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 4*T) (by positivity : 0 < 2*T)).mpr
    nlinarith
  linarith

theorem coefficient_bound_sparse {N : ℕ} {p T L : ℝ} (hT : 1 < T)
    (r : SparseRegime N p T) (hL : (N:ℝ)/T ≤ L) :
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

end MajorityDynamics.Probability.HypergeometricTiltTail.Numerics
