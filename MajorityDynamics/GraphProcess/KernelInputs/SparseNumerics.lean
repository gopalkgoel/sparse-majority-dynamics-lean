import MajorityDynamics.GraphProcess.KernelInputs.Numerics
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Sparse-range scalar inputs for actual kernel splitting. -/
noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.GraphProcess.KernelInputs.Numerics

theorem eventually_log_degree_sparse {θ T a b C : ℝ}
    (_hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hb : 0 < b) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-(1/2 : ℝ)) →
      (Real.log (N:ℝ))^a ≤ C*(p*N)^b := by
  have hT0 : 0 < T := by linarith
  have he : 0 < (1-θ)*b := mul_pos (by linarith) hb
  have hc : 0 < C*(T⁻¹)^b := by positivity
  have ht := (isLittleO_log_rpow_rpow_atTop a he).tendsto_div_nhds_zero
  have hnat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp
    ((ht.comp hnat).eventually (eventually_lt_nhds hc))
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo hhi
  have hw := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hl := h₁ N ((le_max_left _ _).trans hN)
  have hlow : T⁻¹*(N:ℝ)^(1-θ) ≤ p*N := by
    have hh := (mul_lt_mul_of_pos_right hlo hw.1).le
    have heq : T⁻¹*(N:ℝ)^(1-θ) = T⁻¹*(N:ℝ)^(-θ)*(N:ℝ) := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (N:ℝ)^(-θ+1) := by congr 1; ring
        _ = (N:ℝ)^(-θ)*(N:ℝ)^(1:ℝ) := Real.rpow_add hw.1 _ _
        _ = _ := by rw [Real.rpow_one]
    rwa [heq]
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ T⁻¹*(N:ℝ)^(1-θ)) hlow hb.le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hw.1.le] at hpow
  have hl' := (div_lt_iff₀ (Real.rpow_pos_of_pos hw.1 _)).mp hl
  exact hl'.le.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow hC.le])



theorem relative_density_sparse {θ N T φ r p : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hφ : 0 < φ) (hφ1 : φ < 1/2) (hN : 0 < N)
    (hr : N/T ≤ r) (hrN : r ≤ N)
    (hlo : T⁻¹*N^(-θ) < p) (hhi : p < T*N^(-(1/2 : ℝ))) :
    (parameter T φ)⁻¹*r^(-θ) < p ∧ p < parameter T φ*r^(-(1/2 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  have hu := parameter_bounds hT hφ hφ1
  have hu0 : 0 < parameter T φ := by linarith [hu.1]
  have hr0 : 0 < r := (div_pos hN hT0).trans_le hr
  have hpow0 : 0 < r^(-θ) := Real.rpow_pos_of_pos hr0 _
  have hNT : N ≤ T*r := by nlinarith [(div_le_iff₀ hT0).mp hr]
  have hmon := Real.rpow_le_rpow_of_nonpos hN hNT (by linarith : -θ ≤ 0)
  rw [Real.mul_rpow hT0.le hr0.le] at hmon
  have hTp : T⁻¹ ≤ T^(-θ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
  have hinv : (parameter T φ)⁻¹ ≤ T⁻¹*T⁻¹ := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < T^2) hu.2.1
    simpa [pow_two, one_div, mul_inv] using hh
  constructor
  · apply lt_of_le_of_lt ?_ hlo
    calc
      _ ≤ (T⁻¹*T⁻¹)*r^(-θ) := mul_le_mul_of_nonneg_right hinv hpow0.le
      _ ≤ T⁻¹*(T^(-θ)*r^(-θ)) := by
        have hh := mul_le_mul_of_nonneg_right hTp hpow0.le
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hT0.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hmon (inv_nonneg.mpr hT0.le)
  · apply hhi.trans_le
    have hm := Real.rpow_le_rpow_of_nonpos hr0 hrN (by norm_num : -(1/2 : ℝ) ≤ 0)
    have hUT : T ≤ parameter T φ := by nlinarith [sq_nonneg (T-1),hu.2.1]
    exact (mul_le_mul_of_nonneg_left hm hT0.le).trans
      (mul_le_mul_of_nonneg_right hUT (Real.rpow_nonneg hr0.le _))


/-- Numerical preparation discharged uniformly from the original window. -/
structure SparseRegime (N : ℕ) (p θ T φ Cf : ℝ) : Prop where
  N_pos : 0 < (N:ℝ)
  p_pos : 0 < p
  p_lt_one : p < 1
  size_large : 2*T ≤ (N:ℝ)
  log_large : 1 ≤ Real.log (N:ℝ)
  size_error : Cf*Real.sqrt (N:ℝ)*Real.log (N:ℝ) ≤ φ*N/(2*T)
  block_size : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N → 2 ≤ r
  density : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    (parameter T φ)⁻¹*r^(-θ) < p ∧ p < parameter T φ*r^(-(1/2 : ℝ))
  degree_window : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    Real.sqrt (p*N)*(Real.log (N:ℝ))^((2:ℝ)/3) ≤ (p*r)^((4:ℝ)/7)
  log_window : ∀ r ell : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    (N:ℝ)/T ≤ ell → ell ≤ N →
    Real.sqrt (p*N)*(Real.log (N:ℝ))^((2:ℝ)/3) ≤ Real.sqrt (p*ell)*Real.log r
  growth : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    (Real.log r)^100 ≤ (p*N)^((1:ℝ)/14)




theorem uniform_regime_sparse {θ T φ Cf : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hφ : 0 < φ) (hφ1 : φ < 1/2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-(1/2 : ℝ)) → SparseRegime N p θ T φ Cf := by
  have hT0 : 0 < T := by linarith
  obtain ⟨N₁,h₁⟩ := eventually_size_log (Cf:=Cf) hT hφ
  obtain ⟨N₂,h₂⟩ := eventually_log_degree_sparse (a:=(2:ℝ)/3) (b:=(1:ℝ)/14)
    (C:=T^(-(4:ℝ)/7)) hθlo hθhi hT (by norm_num) (by positivity)
  obtain ⟨N₃,h₃⟩ := eventually_log_degree_sparse (a:=100) (b:=(1:ℝ)/14)
    (C:=1) hθlo hθhi hT (by norm_num) zero_lt_one
  obtain ⟨N₄,h₄⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L:=1) zero_lt_one (U:=1/2) (by norm_num) (M:=1) zero_lt_one
  refine ⟨max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro N hN p hlo hhi
  have hn1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hn3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hn4 : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hs := h₁ N hn1
  have hd := h₂ N hn2 p hlo hhi
  have hg := h₃ N hn3 p hlo hhi
  have hw := h₄ N hn4 p hlo hhi
  have hbl := fun r hr hrN => block_log hT hs.1 (r:=r) hr hrN hs.2.2.2.1
  refine ⟨hw.1,hw.2.1,by linarith [hw.2.2.2.2],hs.1,hs.2.1,hs.2.2.1,
    fun r hr hrN => (hbl r hr hrN).1,
    fun r hr hrN => relative_density_sparse hθlo hθhi hT hφ hφ1 hw.1 hr hrN hlo hhi,
    fun r hr _ => degree_window_of_log hw.1 hT0 hw.2.1 hr hd,
    fun r ell hr hrN hell _ => log_window_of_log hw.1 hT0 hw.2.1 hell
      (hbl r hr hrN).2.1 (by linarith [hs.2.1]) hs.2.2.2.2,?_⟩
  intro r hr hrN
  have hb := hbl r hr hrN
  have hrlog : 0 ≤ Real.log r := Real.log_nonneg (by linarith [hb.1])
  have hm := pow_le_pow_left₀ hrlog hb.2.2 100
  exact hm.trans (by simpa [Real.rpow_natCast] using hg)


/-- The literal conservative vertex/child/value union factor is absorbed by
stretched-exponential decay, uniformly over the original density window. -/
theorem union_absorption_sparse (n : ℕ) {θ T c A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hc : 0 < c)
    (_hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-(1/2 : ℝ)) →
      (N:ℝ)*2^(n+2)*(N+1)*Real.exp (-c*(p*N)^((1:ℝ)/7)) ≤ (N:ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := eventually_log_degree_sparse (a:=2) (b:=(1:ℝ)/7)
    (C:=c) hθlo hθhi hT (by norm_num) hc
  obtain ⟨N₂,h₂⟩ := RowConcentration.eventually_log_tail
    (C:=(2:ℝ)^(n+3)) (c:=1) (r:=2) (b:=2) (A:=A)
    (by positivity) zero_lt_one (by norm_num)
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro N hN p hlo hhi
  have hn1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hn2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hn : 1 ≤ N := (le_max_right _ _).trans hN
  have hnR : (1:ℝ) ≤ N := by exact_mod_cast hn
  have hlog := h₁ N hn1 p hlo hhi
  have htail := h₂ N hn2
  have he : Real.exp (-c*(p*N)^((1:ℝ)/7)) ≤ Real.exp (-(Real.log (N:ℝ))^(2:ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hfactor : (N:ℝ)*2^(n+2)*(N+1) ≤ (2:ℝ)^(n+3)*(N:ℝ)^2 := by
    have hpw : (2:ℝ)^(n+3) = 2*(2:ℝ)^(n+2) := by
      calc
        _ = (2:ℝ)^((n+2)+1) := by congr 1
        _ = (2:ℝ)^(n+2)*2 := pow_succ _ _
        _ = _ := by ring
    rw [hpw]
    have hp : 0 ≤ (2:ℝ)^(n+2) := by positivity
    nlinarith [mul_nonneg hp (show 0 ≤ (N:ℝ)^2-N by nlinarith)]
  calc
    _ ≤ ((2:ℝ)^(n+3)*(N:ℝ)^2)*Real.exp (-(Real.log (N:ℝ))^(2:ℝ)) :=
      mul_le_mul hfactor he (Real.exp_nonneg _) (by positivity)
    _ ≤ _ := by simpa [Real.rpow_two] using htail


end MajorityDynamics.GraphProcess.KernelInputs.Numerics

