import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialFourier

/-- Literal characteristic function of the uniform consecutive interval `{0,...,L-1}`. -/
def intervalChi (L : ℕ) (t : ℝ) : ℂ :=
  (L : ℂ)⁻¹ * ∑ k : Fin L, Complex.exp (Complex.I * ((t * (k : ℕ) : ℝ) : ℂ))

theorem intervalChi_eq_sum (L : ℕ) (t : ℝ) :
    intervalChi L t = (L : ℂ)⁻¹ *
      ∑ k : Fin L, Complex.exp (Complex.I * ((t * (k : ℕ) : ℝ) : ℂ)) := rfl

private def S (L : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range L, Complex.exp (Complex.I * ((t * k : ℝ) : ℂ))

private lemma chi_eq (L : ℕ) (t : ℝ) : intervalChi L t = (L : ℂ)⁻¹ * S L t := by
  unfold intervalChi S
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => Complex.exp (Complex.I * ((t*k : ℝ) : ℂ))) L

private lemma norm_S (L : ℕ) (t : ℝ) : ‖S L t‖ ≤ L := by
  calc
    ‖S L t‖ ≤ ∑ k ∈ Finset.range L,
        ‖Complex.exp (Complex.I * ((t * k : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ = L := by simp only [Complex.norm_exp_I_mul_ofReal, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem intervalChi_norm_le_one {L : ℕ} (hL : 1 ≤ L) (t : ℝ) :
    ‖intervalChi L t‖ ≤ 1 := by
  have h : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  rw [chi_eq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (L : ℝ)⁻¹ * ‖S L t‖ ≤ (L : ℝ)⁻¹ * L := mul_le_mul_of_nonneg_left (norm_S L t) (by positivity)
    _ = 1 := inv_mul_cancel₀ h.ne'

private lemma S_add (a b : ℕ) (t : ℝ) :
    S (a+b) t = S a t + Complex.exp (Complex.I * ((t*a : ℝ) : ℂ)) * S b t := by
  rw [S, Finset.sum_range_add, S, S, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_pair (x : ℝ) :
    ‖1 + Complex.exp (Complex.I * (x : ℂ))‖ = 2 * |Real.cos (x/2)| := by
  have he : 1 + Complex.exp (Complex.I * (x : ℂ)) =
      Complex.exp ((x/2 : ℝ) * Complex.I) * (2 * Complex.cos (x/2 : ℝ)) := by
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have h1 : (↑(x/2) : ℂ)*Complex.I + ↑(x/2)*Complex.I = Complex.I * ↑x := by push_cast; ring
    have h0 : (↑(x/2) : ℂ)*Complex.I + -(↑(x/2) : ℂ)*Complex.I = 0 := by ring
    rw [h1, h0, Complex.exp_zero, add_comm]
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
  norm_cast

private lemma norm_S_pair (q r : ℕ) (t : ℝ) :
    ‖S (q+q+r) t‖ ≤ (q : ℝ) * (2 * |Real.cos (t*q/2)|) + r := by
  rw [S_add (q+q) r, S_add q q]
  have hp : S q t + Complex.exp (Complex.I * ((t*q : ℝ) : ℂ)) * S q t =
      (1 + Complex.exp (Complex.I * ((t*q : ℝ) : ℂ))) * S q t := by ring
  rw [hp]
  calc
    _ ≤ ‖(1 + Complex.exp (Complex.I * ((t*q : ℝ) : ℂ))) * S q t‖ +
        ‖Complex.exp (Complex.I * ((t*((q+q : ℕ) : ℝ) : ℝ) : ℂ)) * S r t‖ := norm_add_le _ _
    _ = 2 * |Real.cos (t*q/2)| * ‖S q t‖ + ‖S r t‖ := by rw [norm_mul, norm_mul, norm_pair, Complex.norm_exp_I_mul_ofReal, one_mul]
    _ ≤ 2 * |Real.cos (t*q/2)| * q + r := by
      gcongr
      · exact norm_S q t
      · exact norm_S r t
    _ = _ := by ring

private lemma cosine_small {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x| ≤ 1 - x^2/8 := by
  have hp := Real.two_le_pi
  have hp4 := Real.pi_le_four
  have hc0 : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc (by
    have := abs_le.mp hx
    constructor <;> linarith)
  rw [abs_of_nonneg hc0]
  have hc := Real.cos_le_one_sub_mul_cos_sq (hx.trans (by linarith))
  have hcoef : (1:ℝ)/8 ≤ 2/Real.pi^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [sq_nonneg (Real.pi - 4)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)]

/-- Pair two adjacent blocks of length `floor(L/4)`; bound the leftover terms
by one. The cosine estimate is uniform up to `L*|t|=5`. -/
private lemma small_gap {L : ℕ} (hL : 16 ≤ L) {t : ℝ}
    (ht : (L:ℝ)*|t| ≤ 5) :
    ‖intervalChi L t‖ ≤ 1 - (L:ℝ)^2*t^2/8192 := by
  let q := L/4
  let r := L-2*q
  have hdecomp : q+q+r = L := by dsimp [r,q]; omega
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hql : (L:ℝ)/8 ≤ q := by
    have : L ≤ q*8 := by dsimp [q]; omega
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<8)).mpr (by exact_mod_cast this)
  have hqu : 4*(q:ℝ) ≤ L := by exact_mod_cast (by dsimp [q]; omega : 4*q≤L)
  have hqr : (q:ℝ)+(q:ℝ)+(r:ℝ) = L := by exact_mod_cast hdecomp
  have hx : |t*q/2| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_nonneg hq0]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right hqu (abs_nonneg t)]
  have hc := cosine_small hx
  have hs := norm_S_pair q r t
  rw [hdecomp] at hs
  have hcub : (L:ℝ)^3 ≤ 512*(q:ℝ)^3 := by
    have : ((L:ℝ)/8)^3 ≤ (q:ℝ)^3 := by gcongr
    nlinarith
  have hsq : 0 ≤ t^2 := sq_nonneg t
  have hb : ‖S L t‖ ≤ L - (L:ℝ)^3*t^2/8192 := by
    have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*(q:ℝ) by positivity)
    have ht' := mul_le_mul_of_nonneg_right hcub hsq
    nlinarith
  rw [chi_eq, norm_mul, norm_inv, Complex.norm_natCast]
  apply (inv_mul_le_iff₀ hL0).mpr
  nlinarith

private lemma S_geom (L : ℕ) (t : ℝ) :
    S L t * (Complex.exp (Complex.I * (t:ℂ)) - 1) =
      Complex.exp (Complex.I * ((t*L:ℝ):ℂ)) - 1 := by
  have he (k:ℕ) : Complex.exp (Complex.I * ((t*k:ℝ):ℂ)) =
      Complex.exp (Complex.I * (t:ℂ))^k := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold S
  simp_rw [he]
  exact geom_sum_mul _ _

/-- The geometric-series identity and the linear sine lower bound cover
the rest of the fundamental interval, with no division by a vanishing phase. -/
private lemma large_gap {L : ℕ} (hL : 1 ≤ L) {t : ℝ}
    (htlo : 5 ≤ (L:ℝ)*|t|) (hthi : |t| ≤ Real.pi) :
    ‖intervalChi L t‖ ≤ Real.pi/5 := by
  have hL0 : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hs : ‖S L t‖ * (2*|Real.sin (t/2)|) ≤ 2 := by
    have h := congrArg norm (S_geom L t)
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one] at h
    have hb := norm_sub_le (Complex.exp (Complex.I * ((t*L:ℝ):ℂ))) (1:ℂ)
    rw [Complex.norm_exp_I_mul_ofReal, norm_one] at hb
    rw [← h] at hb
    norm_num only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), one_add_one_eq_two] at hb
    exact hb
  have hsin : |t|/Real.pi ≤ |Real.sin (t/2)| := by
    have h := Real.mul_abs_le_abs_sin (x:=t/2) (by
      rw [abs_div]; norm_num; linarith)
    simpa [abs_div] using h
  have hb : ‖S L t‖ * (2* (|t|/Real.pi)) ≤ 2 := by
    exact (mul_le_mul_of_nonneg_left (by linarith : 2*(|t|/Real.pi) ≤ 2*|Real.sin (t/2)|) (norm_nonneg _)).trans hs
  have hb' : ‖S L t‖ * (2*|t|) ≤ 2*Real.pi := by
    have := (div_le_iff₀ Real.pi_pos).mp (show ‖S L t‖ * (2*|t|)/Real.pi ≤ 2 by convert hb using 1; ring)
    exact this
  have hchi : ‖intervalChi L t‖ * (L:ℝ) = ‖S L t‖ := by
    rw [chi_eq, norm_mul, norm_inv, Complex.norm_natCast]
    field_simp
  have := mul_le_mul_of_nonneg_left htlo (norm_nonneg (intervalChi L t))
  rw [← hchi] at hb'
  nlinarith

/-- Absolute interval gap constant, independent of length and frequency. -/
def intervalConstant : ℝ := 1/8192

theorem intervalConstant_pos : 0 < intervalConstant := by
  unfold intervalConstant
  norm_num

theorem intervalConstant_le_one : intervalConstant ≤ 1 := by
  norm_num [intervalConstant]

/-- Complete quantitative gap on `[-pi,pi]`, including zero and frequencies
of order `1/L`; no Taylor remainder or asymptotic hypothesis is used. -/
theorem intervalChi_norm_gap {L : ℕ} (hL : 16 ≤ L) {t : ℝ}
    (ht : |t| ≤ Real.pi) :
    ‖intervalChi L t‖ ≤ 1 - intervalConstant * min ((L:ℝ)^2*t^2) 1 := by
  by_cases hs : (L:ℝ)*|t| ≤ 5
  · have h := small_gap hL hs
    have hc : intervalConstant ≤ 1/8192 := le_rfl
    have hm : 0 ≤ min ((L:ℝ)^2*t^2) 1 := le_min (by positivity) (by norm_num)
    have hm' := min_le_left ((L:ℝ)^2*t^2) 1
    have := mul_le_mul_of_nonneg_right hc hm
    nlinarith
  · have h := large_gap (show 1≤L by omega) (le_of_not_ge hs) ht
    have hc : intervalConstant ≤ 1-Real.pi/5 := by
      unfold intervalConstant
      linarith [Real.pi_le_four]
    have hm := min_le_right ((L:ℝ)^2*t^2) 1
    have := mul_le_mul_of_nonneg_left hm intervalConstant_pos.le
    nlinarith

end MajorityDynamics.Probability.ConditionedBinomialFourier
