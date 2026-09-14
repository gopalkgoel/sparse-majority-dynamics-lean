import MajorityDynamics.GraphProcess.KernelInputs.Numerics
import MajorityDynamics.Probability.HypergeometricTiltTail.Numerics

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics

/-- The paper's relative edge error. -/
def epsilon (N p : ℝ) : ℝ := (p*N)^((1:ℝ)/7)/N

/-- The C.1 threshold before its final logarithm. -/
def scale (N p : ℝ) : ℝ := N^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)

theorem eventually_degree_gap {θ T A B K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      A*(p*N)^((4:ℝ)/7)+B ≤ (p*N/K)^((7:ℝ)/12) := by
  obtain ⟨X₁,hX₁,h₁⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=(4:ℝ)/7) (b:=(7:ℝ)/12) (A:=A) (B:=(K^((7:ℝ)/12))⁻¹/2)
    (by norm_num) (by positivity)
  obtain ⟨X₂,hX₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=0) (b:=(7:ℝ)/12) (A:=B) (B:=(K^((7:ℝ)/12))⁻¹/2)
    (by norm_num) (by positivity)
  obtain ⟨N₀,h₀⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L:=max X₁ X₂) (lt_of_lt_of_le hX₁ (le_max_left _ _))
    (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨N₀, ?_⟩
  intro N hN p hlo hhi
  have hw := h₀ N hN p hlo hhi
  have hx : 0 < p*N := mul_pos hw.2.1 hw.1
  have ha := h₁ (p*N) ((le_max_left _ _).trans hw.2.2.2.1)
  have hb := h₂ (p*N) ((le_max_right _ _).trans hw.2.2.2.1)
  rw [Real.rpow_zero, mul_one] at hb
  rw [Real.div_rpow hx.le hK.le]
  calc
    _ ≤ (K ^ ((7:ℝ)/12))⁻¹ / 2 * (p*N)^((7:ℝ)/12) +
        (K ^ ((7:ℝ)/12))⁻¹ / 2 * (p*N)^((7:ℝ)/12) := add_le_add ha hb
    _ = _ := by ring

/-- The relative error vanishes uniformly; the threshold is before the density. -/
theorem eventually_epsilon {θ T η : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      0 < epsilon N p ∧ epsilon N p ≤ η := by
  obtain ⟨X,hX,hsmall⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=(1:ℝ)/7) (b:=1) (A:=1) (B:=η) (by norm_num) hη
  obtain ⟨N₀,h₀⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=X) hX
  refine ⟨N₀, ?_⟩
  intro N hN p hlo hhi
  have hw := h₀ N hN p hlo hhi
  have hpN : p*N ≤ (N:ℝ) := by nlinarith [hw.2.2.2.2]
  have hpow := Real.rpow_le_rpow (mul_pos hw.2.1 hw.1).le hpN
    (by norm_num : (0:ℝ) ≤ 1/7)
  have hn := hsmall (N:ℝ) hw.2.2.1
  simp only [one_mul, Real.rpow_one] at hn
  constructor
  · exact div_pos (Real.rpow_pos_of_pos (mul_pos hw.2.1 hw.1) _) hw.1
  · exact (div_le_iff₀ hw.1).mpr (hpow.trans hn)

theorem scale_pos {N p : ℝ} (hN : 0 < N) (hp : 0 < p) : 0 < scale N p := by
  unfold scale
  positivity

theorem scale_sq {N p : ℝ} (hN : 0 < N) (hp : 0 < p) :
    (scale N p)^2 = N^3*p^2*(p*N)^((1:ℝ)/7) := by
  unfold scale
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- Exact identity relating the bias to the variance scale. -/
theorem bias_ratio {N p : ℝ} (hN : 0 < N) (hp : 0 < p) :
    ((p*N)^((8:ℝ)/7))^2 = epsilon N p * (scale N p)^2 := by
  rw [scale_sq hN hp]
  unfold epsilon
  have hx : 0 < p*N := mul_pos hp hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  have he : (16:ℝ)/7 = 2+(1/7+1/7) := by norm_num
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.rpow_add hx, Real.rpow_add hx, Real.rpow_two]
  field_simp

/-- The final strict Chebyshev absorption uses the paper's coefficient-one threshold. -/
theorem chebyshev_absorption {S b C l : ℝ}
    (hS : 0 < S) (hb : b ≤ S) (_hC : 0 ≤ C)
    (hl : 2 ≤ l) (hCl : 4*C < l) :
    0 < S*l-b ∧ C*S^2/(S*l-b)^2 < 1/l := by
  have hl0 : 0 < l := by linarith
  have hgap : S*l/2 ≤ S*l-b := by nlinarith
  have hg0 : 0 < S*l-b := lt_of_lt_of_le (by positivity) hgap
  refine ⟨hg0, ?_⟩
  apply (div_lt_div_iff₀ (sq_pos_of_pos hg0) hl0).mpr
  have hsq := sq_le_sq₀ (by positivity : 0 ≤ S*l/2) hg0.le |>.mpr hgap
  have hc := mul_lt_mul_of_pos_right hCl (by positivity : 0 < S^2*l)
  nlinarith

/-- Bias and the strict probability cost are absorbed uniformly in the original window. -/
theorem eventually_final_absorption {θ T B C : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (_hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      0 < scale N p ∧ B*(p*N)^((8:ℝ)/7) ≤ scale N p ∧
      0 < scale N p * Real.log N - B*(p*N)^((8:ℝ)/7) ∧
      C*(scale N p)^2 /
        (scale N p * Real.log N - B*(p*N)^((8:ℝ)/7))^2 < 1/Real.log N := by
  obtain ⟨N₁,h₁⟩ := eventually_epsilon hθlo hθhi hT
    (η:=1/(B^2+1)) (by positivity)
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_window hθlo hθhi hT
    (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  obtain ⟨N₃,h₃⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      (max 2 (4*C)))
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hlo hhi
  have he := h₁ N ((le_max_left _ _).trans hN) p hlo hhi
  have hw := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hlo hhi
  have hl := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN)
  have hS := scale_pos hw.1 hw.2.1
  have hBe : B^2*epsilon N p ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < B^2+1)).mp he.2
    nlinarith [he.1]
  have hb : B*(p*N)^((8:ℝ)/7) ≤ scale N p := by
    have hh := mul_le_mul_of_nonneg_right hBe (sq_nonneg (scale N p))
    rw [show B^2*epsilon N p*(scale N p)^2 =
      (B*(p*N)^((8:ℝ)/7))^2 by rw [mul_pow,bias_ratio hw.1 hw.2.1]; ring] at hh
    nlinarith [Real.rpow_nonneg (mul_pos hw.2.1 hw.1).le ((8:ℝ)/7)]
  exact ⟨hS,hb,chebyshev_absorption hS hb hC
    ((le_max_left _ _).trans hl.le) ((le_max_right _ _).trans_lt hl)⟩

/-- Sparse source-error simplifications, uniformly in every comparable actual dimension. -/
theorem eventually_sparse_source {θ T K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      1 ≤ p*N ∧ (p*N)^2 ≤ (N:ℝ) ∧
      ∀ n : ℝ, 0 < n → n ≤ K*N → Real.log n ≤ p*N := by
  have hK0 : 0 < K := by linarith
  obtain ⟨N₁,h₁⟩ := HypergeometricTiltTail.Numerics.eventually_square_density hθlo hT
  obtain ⟨N₂,h₂⟩ := GraphProcess.KernelInputs.Numerics.eventually_log_degree
    hθlo hθhi hT (a:=1) (b:=1) (C:=1/2) zero_lt_one (by norm_num)
  obtain ⟨N₃,h₃⟩ := GraphProcess.EnumerationBounds.eventually_window hθlo hθhi hT
    (L:=max 1 (2*Real.log K)) (by positivity) (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hlo hhi
  have hw := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hlo hhi
  have hsq := h₁ N ((le_max_left _ _).trans hN) p hw.2.1 hhi
  have hlog := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hlo hhi
  simp only [Real.rpow_one] at hlog
  refine ⟨(le_max_left _ _).trans hw.2.2.2.1, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hsq hw.1.le
    nlinarith
  · intro n hn hnK
    have hh := Real.log_le_log hn hnK
    rw [Real.log_mul hK0.ne' hw.1.ne'] at hh
    have hlK := (le_max_right _ _).trans hw.2.2.2.1
    linarith

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
