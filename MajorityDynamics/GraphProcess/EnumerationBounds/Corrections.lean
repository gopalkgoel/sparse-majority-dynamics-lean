import MajorityDynamics.GraphProcess.EnumerationBounds.Basic

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationBounds
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

def internalFactor (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s : History (n+1)) : ℝ := gamma2 y d s / (muI y s * (1-muI y s))

def crossFactor (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) : ℝ := variance y d s t / (avg y s t * (1-muC y s t))

theorem squareSum_nonneg (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) : 0 ≤ squareSum y d s t := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem squareSum_gamma {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {T p C : ℝ} (h : Prepared y d T p)
    (hG : RowArray.Gamma y.part y.edge C p d) (s t : History (n+1)) :
    squareSum y d s t ≤ C*p*(Fintype.card V : ℝ)^2 := by
  have hpN : 0 < p*(Fintype.card V : ℝ)^2 := mul_pos h.density_pos (sq_pos_of_pos h.card_pos)
  have hg : squareSum y d s t / (p*(Fintype.card V : ℝ)^2) ≤ C := by
    simpa [RowArray.Gamma, squareSum, avg, Local.CoarseData.sizes, div_eq_mul_inv,
      mul_comm] using hG s t
  have := (div_le_iff₀ hpN).mp hg
  nlinarith

private theorem ratio_bound {S D N p T K : ℝ}
    (hT : 0 < T) (hp : 0 < p) (hN : 0 < N) (hK : 0 ≤ K)
    (hS : 0 ≤ S) (hSK : S ≤ K*p*N^2)
    (hD : p*N^2/(16*T^4) ≤ D) :
    0 ≤ S/D ∧ S/D ≤ 16*T^4*K := by
  have hb : 0 < p*N^2/(16*T^4) := by positivity
  have hd : 0 < D := lt_of_lt_of_le hb hD
  refine ⟨div_nonneg hS hd.le, (div_le_iff₀ hd).mpr ?_⟩
  have hm := mul_le_mul_of_nonneg_left hD (show 0 ≤ 16*T^4*K by positivity)
  have he : (16*T^4*K)*(p*N^2/(16*T^4)) = K*p*N^2 := by
    field_simp
  rw [he] at hm
  exact hSK.trans hm

theorem factors_bound {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {T p K : ℝ} (hT : 1 < T) (h : Prepared y d T p) (hK : 0 ≤ K)
    (hS : ∀ s t, squareSum y d s t ≤ K*p*(Fintype.card V : ℝ)^2) :
    (∀ s, 0 ≤ internalFactor y d s ∧ internalFactor y d s ≤ 16*T^4*K) ∧
    (∀ s t, 0 ≤ crossFactor y d s t ∧ crossFactor y d s t ≤ 16*T^4*K) := by
  have ht : 0 < T := lt_trans zero_lt_one hT
  have hpp := h.density_pos
  have hNN := h.card_pos
  have hi (s) : 1/2 ≤ 1-muI y s := by linarith [h.internal_upper s, h.density_small]
  have hc (s t) : 1/2 ≤ 1-muC y s t := by linarith [h.cross_upper s t, h.density_small]
  constructor
  · intro s
    have hp : 0 < (y.sizes s : ℝ)-1 := by linarith [h.size_two s]
    have ha : ((Fintype.card V : ℝ)/(2*T))^2 ≤ ((y.sizes s : ℝ)-1)^2 :=
      pow_le_pow_left₀ (by positivity) (h.size_pred_lower s) 2
    have hb := mul_le_mul ha (h.internal_lower s) (by positivity : 0 ≤ p/(2*T^2))
      (sq_nonneg ((y.sizes s : ℝ)-1))
    have hd := mul_le_mul hb (hi s) (by norm_num : (0:ℝ) ≤ 1/2)
      (mul_nonneg (sq_nonneg _) ((h.internal_lower s).trans' (by positivity)))
    have he : ((Fintype.card V : ℝ)/(2*T))^2*(p/(2*T^2))*(1/2) =
        p*(Fintype.card V : ℝ)^2/(16*T^4) := by field_simp; ring
    rw [he] at hd
    have hr := ratio_bound ht h.density_pos h.card_pos hK (squareSum_nonneg y d s s) (hS s s) hd
    simpa [internalFactor, gamma2, div_div, mul_assoc] using hr
  · intro s t
    have hb := mul_le_mul (h.size_lower s) (h.avg_lower s t)
      (by positivity : 0 ≤ p*Fintype.card V/(2*T^2))
      (show 0 ≤ (y.sizes s : ℝ) by positivity)
    have hd := mul_le_mul hb (hc s t) (by norm_num : (0:ℝ) ≤ 1/2)
      (mul_nonneg (by positivity) ((h.avg_lower s t).trans' (by positivity)))
    have he : ((Fintype.card V : ℝ)/T)*(p*Fintype.card V/(2*T^2))*(1/2) =
        p*(Fintype.card V : ℝ)^2/(4*T^3) := by field_simp; ring
    rw [he] at hd
    have hden : p*(Fintype.card V : ℝ)^2/(16*T^4) ≤ p*(Fintype.card V : ℝ)^2/(4*T^3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [pow_pos ht 3]
    have hr := ratio_bound ht h.density_pos h.card_pos hK (squareSum_nonneg y d s t)
      (hS s t) (hden.trans hd)
    simpa [crossFactor, variance, div_div, mul_assoc] using hr

theorem internalCorrection_factor (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s : History (n+1)) : internalCorrection y d s = 1/4 - (internalFactor y d s)^2/4 := by
  simp only [internalCorrection, internalFactor, mul_pow, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem crossCorrection_factor (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) :
    crossCorrection y d s t = -(1/2)*(1-crossFactor y d s t)*(1-crossFactor y d t s) := by
  have he : muC y t s = muC y s t := by simp [muC, y.edge_symm t s, mul_comm]
  simp [crossCorrection, crossFactor, he]

theorem correction_terms_bound {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀ s, 0 ≤ internalFactor y d s ∧ internalFactor y d s ≤ B)
    (hc : ∀ s t, 0 ≤ crossFactor y d s t ∧ crossFactor y d s t ≤ B) :
    (∀ s, |internalCorrection y d s| ≤ (1+B)^2) ∧
    (∀ s t, |crossCorrection y d s t| ≤ (1+B)^2) := by
  constructor
  · intro s
    rw [internalCorrection_factor]
    have hs : (internalFactor y d s)^2 ≤ B^2 := pow_le_pow_left₀ (hi s).1 (hi s).2 2
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (internalFactor y d s), sq_nonneg B]
  · intro s t
    have h1 : |1-crossFactor y d s t| ≤ 1+B := abs_le.mpr ⟨by linarith [(hc s t).2], by linarith [(hc s t).1]⟩
    have h2 : |1-crossFactor y d t s| ≤ 1+B := abs_le.mpr ⟨by linarith [(hc t s).2], by linarith [(hc t s).1]⟩
    rw [crossCorrection_factor, abs_mul, abs_mul]
    norm_num
    have hm := mul_le_mul h1 h2 (abs_nonneg _) (by linarith : 0 ≤ 1+B)
    nlinarith [mul_nonneg (abs_nonneg (1-crossFactor y d s t)) (abs_nonneg (1-crossFactor y d t s))]

def correctionCount (n : ℕ) : ℝ :=
  Fintype.card (History (n+1)) + Fintype.card (BlockDecomposition.Pair (History (n+1)))

theorem correctionCount_pos (n : ℕ) : 0 < correctionCount n := by
  have hi : 0 < Fintype.card (History (n+1)) := Fintype.card_pos
  unfold correctionCount
  positivity

theorem correction_sum_bound {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {B : ℝ} (hi : ∀ s, |internalCorrection y d s| ≤ B)
    (hc : ∀ s t, |crossCorrection y d s t| ≤ B) :
    |correction y d| ≤ correctionCount n * B := by
  unfold correction
  calc
    _ ≤ (∑ s, |internalCorrection y d s|) +
        ∑ z : BlockDecomposition.Pair (History (n+1)), |crossCorrection y d z.val.1 z.val.2| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ _s : History (n+1), B) + (∑ _z : BlockDecomposition.Pair (History (n+1)), B) :=
      add_le_add (Finset.sum_le_sum fun s _ => hi s) (Finset.sum_le_sum fun z _ => hc z.val.1 z.val.2)
    _ = correctionCount n * B := by simp [correctionCount]; ring

def strongConstant (n : ℕ) (T C : ℝ) : ℝ := correctionCount n * (1+16*T^4*C)^2

theorem strongConstant_pos (n : ℕ) {T C : ℝ} (hC : 0 < C) : 0 < strongConstant n T C := by
  unfold strongConstant
  exact mul_pos (correctionCount_pos n) (sq_pos_of_pos (by positivity))

theorem strong_correction_bound {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {T p C : ℝ} (hT : 1 < T) (h : Prepared y d T p) (hC : 0 < C)
    (hG : RowArray.Gamma y.part y.edge C p d) : |correction y d| ≤ strongConstant n T C := by
  obtain ⟨hi,hc⟩ := factors_bound hT h hC.le (squareSum_gamma h hG)
  obtain ⟨hi,hc⟩ := correction_terms_bound (by positivity : 0 ≤ 16*T^4*C) hi hc
  exact correction_sum_bound hi hc

theorem squareSum_weak {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {T p : ℝ} (h : Prepared y d T p) (s t : History (n+1)) :
    squareSum y d s t ≤ (4*(p*Fintype.card V)^(1/7:ℝ))*p*(Fintype.card V : ℝ)^2 := by
  have hx : 0 < p*(Fintype.card V : ℝ) := mul_pos h.density_pos h.card_pos
  have he : ((p*Fintype.card V)^(4/7:ℝ))^2 =
      (p*Fintype.card V)*(p*Fintype.card V)^(1/7:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    rw [show (8/7:ℝ) = 1+1/7 by norm_num, Real.rpow_add hx, Real.rpow_one]
  have hb (v) (hv : v ∈ History.block y.part s) :
      ((RowArray.values d v t : ℝ)-avg y s t)^2 ≤
        4*(p*Fintype.card V)*(p*Fintype.card V)^(1/7:ℝ) := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (h.entry s t v hv) 2
    rw [sq_abs, mul_pow, he] at hh
    nlinarith
  have hs := Finset.sum_le_sum hb
  have hcard : ((History.block y.part s).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_univ (History.block y.part s)
  have hh := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ 4*(p*Fintype.card V)*(p*Fintype.card V)^(1/7:ℝ) by positivity)
  calc
    squareSum y d s t ≤ ((History.block y.part s).card : ℝ)*
        (4*(p*Fintype.card V)*(p*Fintype.card V)^(1/7:ℝ)) := by
      simpa [squareSum] using hs
    _ ≤ (Fintype.card V : ℝ)*(4*(p*Fintype.card V)*(p*Fintype.card V)^(1/7:ℝ)) := hh
    _ = _ := by ring

def weakConstant (n : ℕ) (T : ℝ) : ℝ := correctionCount n * (1+64*T^4)^2

theorem weakConstant_pos (n : ℕ) (T : ℝ) : 0 < weakConstant n T := by
  unfold weakConstant
  exact mul_pos (correctionCount_pos n) (sq_pos_of_pos (by positivity))

theorem weak_factors_bound {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {T p : ℝ} (hT : 1 < T) (h : Prepared y d T p) :
    (∀ s, 0 ≤ internalFactor y d s ∧
      internalFactor y d s ≤ 64*T^4*(p*Fintype.card V)^(1/7:ℝ)) ∧
    (∀ s t, 0 ≤ crossFactor y d s t ∧
      crossFactor y d s t ≤ 64*T^4*(p*Fintype.card V)^(1/7:ℝ)) := by
  have hpp := h.density_pos
  have hNN := h.card_pos
  have he : 16*T^4*(4*(p*Fintype.card V)^(1/7:ℝ)) =
      64*T^4*(p*Fintype.card V)^(1/7:ℝ) := by ring
  simpa only [he] using factors_bound hT h
    (by positivity : 0 ≤ 4*(p*Fintype.card V)^(1/7:ℝ)) (squareSum_weak h)

theorem weak_correction_bound {y : Local.CoarseData V n} {d : RowArray.Ambient y.part}
    {T p : ℝ} (hT : 1 < T) (h : Prepared y d T p) :
    |correction y d| ≤ weakConstant n T * (p*Fintype.card V)^(2/7:ℝ) := by
  have hpp := h.density_pos
  have hNN := h.card_pos
  obtain ⟨hi,hc⟩ := weak_factors_bound hT h
  obtain ⟨hi,hc⟩ := correction_terms_bound
    (by positivity : 0 ≤ 64*T^4*(p*Fintype.card V)^(1/7:ℝ)) hi hc
  have hh := correction_sum_bound hi hc
  have hx := Real.one_le_rpow h.mean_one (by norm_num : (0:ℝ) ≤ 1/7)
  have hp : 0 ≤ p*(Fintype.card V : ℝ) := (mul_pos h.density_pos h.card_pos).le
  have he : ((p*Fintype.card V)^(1/7:ℝ))^2 = (p*Fintype.card V)^(2/7:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
    congr 1
    norm_num
  have hs : (1+64*T^4*(p*Fintype.card V)^(1/7:ℝ))^2 ≤
      ((1+64*T^4)*(p*Fintype.card V)^(1/7:ℝ))^2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (correctionCount_pos n).le
  rw [mul_pow, he] at hm
  unfold weakConstant
  exact hh.trans (by simpa [mul_assoc] using hm)

end MajorityDynamics.GraphProcess.EnumerationBounds
