import MajorityDynamics.GraphProcess.KernelInputs.Numerics

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.Probability.HypergeometricTiltTail.Numerics

structure Regime (N : ℕ) (p T : ℝ) : Prop where
  N_large : 4*T ≤ (N:ℝ)
  log_large : 1 ≤ Real.log (N:ℝ)
  p_pos : 0 < p
  p_small : p ≤ 1/8
  p_tiny : p ≤ 1/(8*T)
  degree_large : 4 ≤ p*N
  degree_error : Real.sqrt (p*N)*Real.log (N:ℝ) ≤ p*N/2
  square_density : p^2*N ≤ 1
  coefficient : 2*Real.sqrt T*Real.log (N:ℝ) ≤ Real.sqrt (p*N)
  log_gap : 16*Real.sqrt T*Real.log (N:ℝ) ≤ (Real.log (N:ℝ))^100

theorem eventually_square_density {θ T : ℝ} (hθ : 1/2 < θ) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, 0 < p → p < T*(N:ℝ)^(-θ) → p^2*N ≤ 1 := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => T^2*(N:ℝ)^(1-2*θ)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by linarith : 0 < 2*θ-1)).comp hn
    simpa [neg_sub] using hh.const_mul (T^2)
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1:ℕ)).and (ht.eventually (eventually_lt_nhds zero_lt_one)))
  refine ⟨N₀, ?_⟩
  intro N hN p hp hhi
  obtain ⟨hN1,hsmall⟩ := h₀ N hN
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hu0 : 0 < T*(N:ℝ)^(-θ) := by positivity
  have hsq : p^2 ≤ (T*(N:ℝ)^(-θ))^2 := by nlinarith
  have heq : (T*(N:ℝ)^(-θ))^2*(N:ℝ) = T^2*(N:ℝ)^(1-2*θ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hN0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show T^2*(N:ℝ)^(-θ*2)*(N:ℝ) = T^2*((N:ℝ)^(-θ*2)*(N:ℝ)^(1:ℝ)) by rw [Real.rpow_one]; ring]
    rw [← Real.rpow_add hN0]
    congr 2
    ring
  have hh := mul_le_mul_of_nonneg_right hsq hN0.le
  rw [heq] at hh
  exact hh.trans hsmall.le

theorem uniform_regime {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) → Regime N p T := by
  have hT0 : 0 < T := by linarith
  obtain ⟨N₁,h₁⟩ := GraphProcess.EnumerationBounds.eventually_window hθlo hθhi hT
    (L:=4) (by norm_num) (U:=1/(8*T)) (by positivity) (M:=4*T) (by positivity)
  obtain ⟨N₂,h₂⟩ := GraphProcess.KernelInputs.Numerics.eventually_log_degree
    (a:=1) (b:=1/2) (C:=1/(2*Real.sqrt T)) hθlo hθhi hT (by norm_num) (by positivity)
  obtain ⟨N₃,h₃⟩ := eventually_square_density hθlo hT
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
  refine ⟨hsize,hlog,hp,hps1,hps,hdegree,herror,h₃ N hn3 p hp hhi,hcoeff',?_⟩
  simpa [Real.rpow_one, Real.rpow_natCast] using hX (Real.log (N:ℝ))
    ((le_max_right _ _).trans (h₄ N hn4))

end MajorityDynamics.Probability.HypergeometricTiltTail.Numerics
