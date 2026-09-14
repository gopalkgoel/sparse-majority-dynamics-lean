import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Geometry
import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics

noncomputable section
open Filter Topology MeasureTheory

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
namespace Scaling

def delta (d : ℕ) : ℝ := 1 / (100*((d : ℝ)+3))

theorem delta_pos (d : ℕ) : 0 < delta d := by unfold delta; positivity
theorem delta_lt_half (d : ℕ) : delta d < 1/2 := by
  unfold delta
  apply (div_lt_iff₀ (by positivity)).2
  have := Nat.cast_nonneg (α := ℝ) d
  linarith
theorem delta_exponent (d : ℕ) : ((d : ℝ)+3)*delta d - 1/2 < 0 := by
  unfold delta
  have hd : (d : ℝ)+3 ≠ 0 := by positivity
  field_simp
  have := Nat.cast_nonneg (α := ℝ) d
  nlinarith

theorem sqrt_scale {n p : ℝ} (hn : 0 < n) (_hp : 0 < p) :
    Real.sqrt (n^2*p) = Real.sqrt n * Real.sqrt (p*n) := by
  rw [← Real.sqrt_mul hn.le]
  congr 1
  ring

theorem scaled_radius {n p δ : ℝ} (hn : 0 < n) (hp : 0 < p) :
    Real.sqrt (p*n) * (n^δ / Real.sqrt (n^2*p)) = n^(δ-1/2) := by
  rw [sqrt_scale hn hp]
  have hs : Real.sqrt (p*n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (mul_pos hp hn))
  rw [Real.rpow_sub hn, ← Real.sqrt_eq_rpow]
  field_simp

theorem cube_scale (d : ℕ) {n p δ : ℝ} (hn : 0 < n) (hp : 0 < p) :
    (2*(n^δ / Real.sqrt (n^2*p)))^d =
      (2:ℝ)^d * n^((d:ℝ)*δ) * (n^2*p)^(-(d:ℝ)/2) := by
  have hx : 0 < n^2*p := by positivity
  have hnum : (n^δ)^d = n^((d:ℝ)*δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have hden : (Real.sqrt (n^2*p))^d = (n^2*p)^((d:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [mul_pow, div_pow, hnum, hden, div_eq_mul_inv,
    ← Real.rpow_neg hx.le, mul_assoc]
  congr 2
  ring

theorem small_cube_scale (d : ℕ) {n p : ℝ} (hn : 0 < n) (hp : 0 < p) :
    (2*(1 / Real.sqrt (n^2*p)))^d = (2:ℝ)^d * (n^2*p)^(-(d:ℝ)/2) := by
  simpa using cube_scale d (δ := 0) hn hp

/-- The low-frequency radius is eventually within the fundamental cube,
uniformly throughout the original density window. -/
theorem radius_eventually (θ T δ : ℝ) (hθ : θ < 1) (hT : 0 < T)
    (hδ : δ < 1/2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p →
      1 ≤ N ∧ 0 < p ∧ (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p) ≤ Real.pi := by
  have he : δ - 1 + θ/2 < 0 := by linarith
  have ht := ((tendsto_rpow_neg_atTop (by linarith : 0 < -(δ-1+θ/2))).comp
    tendsto_natCast_atTop_atTop).const_mul (Real.sqrt T)
  simp only [neg_neg, mul_zero] at ht
  obtain ⟨N₀, hh⟩ := eventually_atTop.1
    ((ht.eventually (eventually_lt_nhds Real.pi_pos)).and (eventually_ge_atTop (1:ℕ)))
  refine ⟨N₀, fun N hN p hlo => ?_⟩
  have hN1 := (hh N hN).2
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN1
  have hp : 0 < p := (mul_pos (inv_pos.2 hT) (Real.rpow_pos_of_pos hn _)).trans hlo
  refine ⟨hN1, hp, le_trans ?_ (hh N hN).1.le⟩
  have hlo' : (N:ℝ)^2*(T⁻¹*(N:ℝ)^(-θ)) ≤ (N:ℝ)^2*p :=
    mul_le_mul_of_nonneg_left hlo.le (sq_nonneg _)
  have hden := Real.sqrt_le_sqrt hlo'
  have hbase : 0 < (N:ℝ)^2*(T⁻¹*(N:ℝ)^(-θ)) := by positivity
  have hbound := div_le_div_of_nonneg_left (Real.rpow_nonneg hn.le δ)
    (Real.sqrt_pos.2 hbase) hden
  apply hbound.trans_eq
  rw [Real.sqrt_eq_rpow, Real.mul_rpow (sq_nonneg _) (by positivity),
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hn.le _),
    Real.inv_rpow hT.le, ← Real.rpow_natCast, ← Real.rpow_mul hn.le,
    ← Real.rpow_mul hn.le]
  norm_num
  rw [div_eq_mul_inv, mul_inv_rev, mul_inv_rev, inv_inv,
    ← Real.rpow_neg hn.le, ← Real.rpow_neg_one]
  rw [← Real.sqrt_eq_rpow]
  calc
    _ = Real.sqrt T * ((N:ℝ)^δ * (N:ℝ)^(-(-θ*(1/2))) * (N:ℝ)^(-1:ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
      congr 2
      ring


/-- The low radius in the natural one-row standard-deviation units is at most one. -/
theorem scaled_radius_le_one (d : ℕ) {n p : ℝ} (hn : 1 ≤ n) (hp : 0 < p) :
    Real.sqrt (p*n) * (n^(delta d) / Real.sqrt (n^2*p)) ≤ 1 := by
  rw [scaled_radius (lt_of_lt_of_le zero_lt_one hn) hp]
  exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith [delta_lt_half d])

/-- Uniformly vanishing integrated Taylor error, relative to the local atom scale. -/
theorem integrated_error_eventually (d : ℕ) (D a : ℝ) (_hD : 0 < D) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, 0 < p →
      1 ≤ N ∧
      D*(N:ℝ)^(3*delta d-1/2) *
          (2*((N:ℝ)^(delta d)/Real.sqrt ((N:ℝ)^2*p)))^d ≤
        (a/4)*((N:ℝ)^2*p)^(-(d:ℝ)/2) ∧
      (N:ℝ)^(-1:ℝ) ≤ a/4 := by
  have he := delta_exponent d
  have ht := ((tendsto_rpow_neg_atTop (neg_pos.2 he)).comp
    tendsto_natCast_atTop_atTop).const_mul (D*(2:ℝ)^d)
  simp only [neg_neg, mul_zero] at ht
  have ht' := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hh⟩ := eventually_atTop.1
    (((ht.eventually (eventually_lt_nhds (by positivity : 0 < a/4))).and
      (ht'.eventually (eventually_lt_nhds (by positivity : 0 < a/4)))).and
      (eventually_ge_atTop (1:ℕ)))
  refine ⟨N₀, fun N hN p hp => ?_⟩
  have hN1 := (hh N hN).2
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN1
  refine ⟨hN1, ?_, (hh N hN).1.2.le⟩
  rw [cube_scale d hn hp]
  have hid : D*(N:ℝ)^(3*delta d-1/2) *
      ((2:ℝ)^d*(N:ℝ)^((d:ℝ)*delta d)*((N:ℝ)^2*p)^(-(d:ℝ)/2)) =
      (D*(2:ℝ)^d*(N:ℝ)^(((d:ℝ)+3)*delta d-1/2)) *
        ((N:ℝ)^2*p)^(-(d:ℝ)/2) := by
    rw [show ((d:ℝ)+3)*delta d-1/2 = (3*delta d-1/2)+(d:ℝ)*delta d by ring,
      Real.rpow_add hn]
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right (hh N hN).1.1.le (Real.rpow_nonneg (by positivity) _)

/-- The fixed Gaussian comparison cube has uniformly bounded quadratic exponent. -/
theorem small_gaussian_scale {n p m T : ℝ} (hn : 0 < n) (hp : 0 < p)
    (hm : m ≤ T*n) :
    m*(p*n)*(1/Real.sqrt (n^2*p))^2 ≤ T := by
  have hid : m*(p*n)*(1/Real.sqrt (n^2*p))^2 = m/n := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [hid]
  exact (div_le_iff₀ hn).2 hm

end Scaling
end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
