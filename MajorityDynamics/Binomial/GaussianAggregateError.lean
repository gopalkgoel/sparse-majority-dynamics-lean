import MajorityDynamics.Binomial.ExpansionError
import MajorityDynamics.Binomial.GaussianMomentBounds

/-! # Local and tail error aggregation for the Gaussian comparison -/

noncomputable section
namespace MajorityDynamics.Binomial.Approximation

theorem finite_gaussian_error (a d T s l B δ ε τ : ℝ) (D : ℕ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hT : 0 ≤ T) (hs : 1 ≤ s) (hl : 1 ≤ l)
    (hB : 0 ≤ B) (hδ : δ ≤ 16*d*T^2*l^3/s)
    (hε : ε ≤ 8*T*l/s) (hτ : τ ≤ B/s) :
    8*(a*(s*l+1)^D)*δ + 32*(a*(s*l+1)^D)*d*ε +
      a*(D:ℝ)*(s*l+1)^D/(s*l+1) + 2*(a*(s*l+1)^D)*τ ≤
    (a*2^D*(128*d*T^2+256*d*T+(D:ℝ)+2*B)) *
      (s^D/s)*l^(D+3) := by
  have hs0 : 0 < s := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hsl : 1 ≤ s*l := one_le_mul_of_one_le_of_one_le hs hl
  have hpow : (s*l+1)^D ≤ 2^D*s^D*l^D := by
    calc
      _ ≤ (2*(s*l))^D := pow_le_pow_left₀ (by positivity) (by linarith) D
      _ = _ := by simp only [mul_pow]; ring
  have hden : s ≤ s*l+1 := by nlinarith
  have hp1 : l^D*l ≤ l^(D+3) := by
    rw [←pow_succ]
    exact pow_le_pow_right₀ hl (by omega)
  have hp0 : l^D ≤ l^(D+3) := pow_le_pow_right₀ hl (by omega)
  have h1 : 8*(a*(s*l+1)^D)*δ ≤
      (a*2^D*(128*d*T^2))*(s^D/s)*l^(D+3) := by
    calc
      _ ≤ 8*(a*(s*l+1)^D)*(16*d*T^2*l^3/s) := mul_le_mul_of_nonneg_left hδ (by positivity)
      _ ≤ 8*(a*(2^D*s^D*l^D))*(16*d*T^2*l^3/s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow ha) (by norm_num)) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have h2 : 32*(a*(s*l+1)^D)*d*ε ≤
      (a*2^D*(256*d*T))*(s^D/s)*l^(D+3) := by
    calc
      _ ≤ 32*(a*(s*l+1)^D)*d*(8*T*l/s) := mul_le_mul_of_nonneg_left hε (by positivity)
      _ ≤ 32*(a*(2^D*s^D*l^D))*d*(8*T*l/s) := by gcongr
      _ = (a*2^D*(256*d*T))*(s^D/s)*(l^D*l) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp1 (by positivity)
  have h3 : a*(D:ℝ)*(s*l+1)^D/(s*l+1) ≤
      (a*2^D*(D:ℝ))*(s^D/s)*l^(D+3) := by
    calc
      _ ≤ a*(D:ℝ)*(s*l+1)^D/s := div_le_div_of_nonneg_left (by positivity) hs0 hden
      _ ≤ a*(D:ℝ)*(2^D*s^D*l^D)/s := by gcongr
      _ = (a*2^D*(D:ℝ))*(s^D/s)*l^D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp0 (by positivity)
  have h4 : 2*(a*(s*l+1)^D)*τ ≤
      (a*2^D*(2*B))*(s^D/s)*l^(D+3) := by
    calc
      _ ≤ 2*(a*(s*l+1)^D)*(B/s) := mul_le_mul_of_nonneg_left hτ (by positivity)
      _ ≤ 2*(a*(2^D*s^D*l^D))*(B/s) := by gcongr
      _ = (a*2^D*(2*B))*(s^D/s)*l^D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp0 (by positivity)
  calc
    _ ≤ _ := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring

theorem tail_gaussian_error (a d T n s l K τ₀ τ₁ M t : ℝ) (D : ℕ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hT : 0 ≤ T) (hn : 1 ≤ n)
    (hs : 1 ≤ s) (hsn : s ≤ n) (hl : 1 ≤ l) (hln : l ≤ n)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hτ₀ : τ₀ ≤ 2*d*t^2) (hτ₁ : τ₁ ≤ 2*d*t^2)
    (hM : M ≤ K*(T*s)^(2*D)) :
    2*(a*(T*n)^D)*τ₀ + Real.sqrt M * Real.sqrt τ₁ +
      (a*(s*l+1)^D)*τ₁ ≤
    (4*a*T^D*d + Real.sqrt K*T^D*Real.sqrt (2*d) + 2*a*2^D*d + 1) *
      n^(2*D+1)*t := by
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hl0 : 0 ≤ l := by linarith
  have ht2 : t^2 ≤ t := by nlinarith
  have hpD : n^D ≤ n^(2*D+1) := pow_le_pow_right₀ hn (by omega)
  have hp2D : n^(2*D) ≤ n^(2*D+1) := pow_le_pow_right₀ hn (by omega)
  have hpow : (s*l+1)^D ≤ 2^D*n^(2*D) := by
    calc
      _ ≤ (2*n^2)^D := by
        apply pow_le_pow_left₀ (by positivity)
        have hsl := mul_le_mul hsn hln hl0 hn0
        nlinarith [sq_nonneg (n-1)]
      _ = _ := by rw [mul_pow, ←pow_mul]
  have hroot : Real.sqrt M ≤ Real.sqrt K*T^D*n^D := by
    calc
      _ ≤ Real.sqrt (K*(T*s)^(2*D)) := Real.sqrt_le_sqrt hM
      _ = Real.sqrt K*(T*s)^D := by
        rw [Real.sqrt_mul hK, mul_comm 2 D, pow_mul, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ (T*s)^D)]
      _ ≤ Real.sqrt K*(T*n)^D := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hrootτ : Real.sqrt τ₁ ≤ Real.sqrt (2*d)*t := by
    calc
      _ ≤ Real.sqrt (2*d*t^2) := Real.sqrt_le_sqrt hτ₁
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg ht]
  have h1 : 2*(a*(T*n)^D)*τ₀ ≤ (4*a*T^D*d)*n^(2*D+1)*t := by
    calc
      _ ≤ 2*(a*(T*n)^D)*(2*d*t^2) := mul_le_mul_of_nonneg_left hτ₀ (by positivity)
      _ ≤ 2*(a*(T*n)^D)*(2*d*t) := by gcongr
      _ = (4*a*T^D*d)*n^D*t := by rw [mul_pow]; ring
      _ ≤ _ := by gcongr
  have h2 : Real.sqrt M*Real.sqrt τ₁ ≤
      (Real.sqrt K*T^D*Real.sqrt (2*d))*n^(2*D+1)*t := by
    calc
      _ ≤ (Real.sqrt K*T^D*n^D)*(Real.sqrt (2*d)*t) :=
        mul_le_mul hroot hrootτ (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt K*T^D*Real.sqrt (2*d))*n^D*t := by ring
      _ ≤ _ := by gcongr
  have h3 : (a*(s*l+1)^D)*τ₁ ≤ (2*a*2^D*d)*n^(2*D+1)*t := by
    calc
      _ ≤ (a*(s*l+1)^D)*(2*d*t^2) := mul_le_mul_of_nonneg_left hτ₁ (by positivity)
      _ ≤ (a*(2^D*n^(2*D)))*(2*d*t) := by gcongr
      _ = (2*a*2^D*d)*n^(2*D)*t := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hn0 (2*D+1)) ht]

/-- The common Gaussian and binomial tail is the square of the slower envelope. -/
theorem gaussian_tail_envelope (l C : ℝ) (hC : 0 < C) :
    0 ≤ Real.exp (-l^2/(2*C)) ∧ Real.exp (-l^2/(2*C)) ≤ 1 ∧
    Real.exp (-l^2/C) = (Real.exp (-l^2/(2*C)))^2 := by
  refine ⟨(Real.exp_pos _).le, ?_, ?_⟩
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg l)) (by positivity)
  · rw [←Real.exp_nat_mul]
    congr 1
    ring

end MajorityDynamics.Binomial.Approximation
