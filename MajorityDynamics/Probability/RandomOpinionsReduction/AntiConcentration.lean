import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # An elementary central-binomial upper bound

The squared bound below follows by induction from the exact central-binomial
recurrence. In particular it needs neither Stirling nor a limit theorem.
-/
noncomputable section
namespace MajorityDynamics.Probability.RandomOpinionsReduction

theorem central_binomial_sq_bound (n : ℕ) :
    (n + 1 : ℝ) * (n.centralBinom : ℝ) ^ 2 ≤ (4 : ℝ) ^ (2 * n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he := Nat.succ_mul_centralBinom_succ n
    have he' : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by exact_mod_cast he
    have hi := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ 4 * (2 * n + 1)^2 by positivity)
    have hpoly : (n + 2 : ℝ) * (2 * n + 1)^2 ≤ 4 * (n + 1)^3 := by
      nlinarith [sq_nonneg (n : ℝ)]
    have hb := mul_le_mul_of_nonneg_right hpoly (show (0 : ℝ) ≤ (4 : ℝ)^(2*n) by positivity)
    have hs := congrArg (fun x : ℝ => x^2) he'
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    push_cast
    norm_num only [pow_two, pow_succ] at hs
    have hpos : 0 < (n + 1 : ℝ) ^ 3 := by positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ n + 2 by positivity)]

theorem binomial_sq_bound (N a : ℕ) :
    (N : ℝ) * (N.choose a : ℝ)^2 ≤ 2 * (2 : ℝ)^(2*N) := by
  have even_bound (n a : ℕ) :
      (n + 1 : ℝ) * ((2*n).choose a : ℝ)^2 ≤ (4 : ℝ)^(2*n) := by
    have hc : ((2*n).choose a : ℝ) ≤ (n.centralBinom : ℝ) :=
      by exact_mod_cast Nat.choose_le_centralBinom a n
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2)
      (by positivity)).trans (central_binomial_sq_bound n)
  obtain ⟨n, hn⟩ | ⟨n, hn⟩ := Nat.even_or_odd N
  · rw [hn]
    have h := even_bound n a
    have he : (4 : ℝ)^(2*n) = (2 : ℝ)^(2*(n+n)) := by
      rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul]
      congr 1
      omega
    rw [show n+n = 2*n by omega]
    rw [show n+n = 2*n by omega] at he
    push_cast
    rw [he] at h
    nlinarith [sq_nonneg (((2*n).choose a : ℕ) : ℝ)]
  · rw [hn]
    have hc : (2*n+1).choose a ≤ 2 * n.centralBinom := by
      cases a with
      | zero => simp only [Nat.choose_zero_right]; have := Nat.centralBinom_pos n; omega
      | succ a =>
        rw [Nat.choose_succ_succ]
        have := Nat.choose_le_centralBinom a n
        have := Nat.choose_le_centralBinom (a+1) n
        simp only [Nat.succ_eq_add_one]
        omega
    have hc' : ((2*n+1).choose a : ℝ) ≤ 2 * (n.centralBinom : ℝ) := by exact_mod_cast hc
    have hs := pow_le_pow_left₀ (by positivity) hc' 2
    have h := central_binomial_sq_bound n
    have hi := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2*n+1 by positivity)
    have he : (2 : ℝ)^(2*(2*n+1)) = 4 * (4 : ℝ)^(2*n) := by
      rw [show 2*(2*n+1) = 2 + 2*(2*n) by omega, pow_add, pow_mul]
      norm_num
    rw [he]
    push_cast
    nlinarith [sq_nonneg (n.centralBinom : ℝ)]

theorem binomial_point_bound {N : ℕ} (hN : 0 < N) (a : ℕ) :
    (N.choose a : ℝ) / (2 : ℝ)^N ≤ 2 / Real.sqrt N := by
  have h := binomial_sq_bound N a
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Real.sq_sqrt hNr.le
  have hsp := Real.sqrt_pos.mpr hNr
  have hp : (0 : ℝ) < (2 : ℝ)^N := by positivity
  apply (div_le_div_iff₀ hp hsp).mpr
  rw [mul_comm]
  rw [show 2*N = N*2 by omega, pow_mul] at h
  have hsq : (Real.sqrt N * (N.choose a : ℝ))^2 = (N : ℝ) * (N.choose a : ℝ)^2 := by
    rw [mul_pow, hs]
  nlinarith [sq_nonneg ((2 : ℝ)^N),
    mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (show 0 ≤ (N.choose a : ℝ) by positivity)]

end MajorityDynamics.Probability.RandomOpinionsReduction
