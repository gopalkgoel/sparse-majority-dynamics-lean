import MajorityDynamics.Idealized.Process.Basic
import MajorityDynamics.Idealized.RowLimits.Geometry

/-! Uniform size geometry and the normalized target in the mean equation. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.Process
open Universal Binomial Binomial.Approximation
variable {n : ℕ}

/-- Relative size control follows from the literal size error in Theorem 5.2. -/
theorem LevelEstimates.relative_sizes {N ell : ℕ} {p : Probability} {x : State n}
    (h : LevelEstimates N p ell x) (hN : 0 < N) (t : History (n + 1)) :
    |(x.sizes t : ℝ) / N - ν n t| ≤ Real.log N ^ ell / scale N p := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh := h.sizes t
  have he : (x.sizes t : ℝ) / N - ν n t = ((x.sizes t : ℝ) - N * ν n t) / N := by
    field_simp [hn.ne']
  rw [he, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  exact hh.trans_eq (by dsimp [scale]; ring)

/-- The constants and threshold are uniform in all approximately universal states. -/
theorem eventually_level_sizes (θ T : ℝ) (ell : ℕ) (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Probability, Density θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ t,
        0 < x.sizes t ∧ (N : ℝ) * ν n t / 2 < x.sizes t ∧
        (x.sizes t : ℝ) < 2 * N * ν n t := by
  have he : ∀ᶠ N : ℕ in atTop, ∀ t : History (n + 1), 0 < N ∧
      ∀ p : Probability, Density θ T N p →
        Real.log N ^ ell / scale N p + 1 / N < ν n t / 2 :=
    Filter.eventually_all.mpr fun t => RowLimits.eventually_size_error_small θ T
      (ν n t / 2) ell hθ hT (half_pos (ν_positive n t))
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N he hN
  refine ⟨hN, ?_⟩
  intro p hp x hx t
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh := hx.relative_sizes hN t
  have hb := (he t).2 p hp
  have hi : (0 : ℝ) ≤ 1 / N := by positivity
  have hv := ν_positive n t
  have hlo : ν n t / 2 < (x.sizes t : ℝ) / N := by
    have hh' := (abs_le.mp hh).1
    linarith
  have hhi : (x.sizes t : ℝ) / N < 2 * ν n t := by
    have hh' := (abs_le.mp hh).2
    linarith
  have hl := (lt_div_iff₀ hn).mp hlo
  have hu := (div_lt_iff₀ hn).mp hhi
  have hz : (0 : ℝ) < x.sizes t := by nlinarith
  exact ⟨by exact_mod_cast hz, by nlinarith, by nlinarith⟩

/-- Algebraic core of the normalized target comparison. -/
theorem normalized_target_scalar {N p a ns nt v m edge L : ℝ}
    (hN : 0 < N) (hp : 0 < p) (ha : 0 < a) (hasq : a ^ 2 = p * N)
    (hns : 0 < ns) (_hnt : 0 ≤ nt) (hL : 0 ≤ L)
    (hsize : |nt / N - v| ≤ L / a) (hupper : nt ≤ 2 * N * v)
    (hedge : |edge - p * ns * nt * (1 + m / a)| ≤ p * ns * nt * (L / (p * N))) :
    |(edge / ns - p * nt) / a - v * m| ≤ (2 * v + |m|) * (L / a) := by
  have hpa : p / a / a = 1 / N := by
    rw [div_div, ← pow_two, hasq]
    field_simp [hp.ne', hN.ne']
  have he : (edge / ns - p * nt) / a - v * m =
      (edge - p * ns * nt * (1 + m / a)) / (ns * a) + (nt / N - v) * m := by
    calc
      _ = (edge - p * ns * nt * (1 + m / a)) / (ns * a) +
          (p / a / a * nt - v) * m := by field_simp [hns.ne', ha.ne']; ring
      _ = _ := by rw [hpa]; ring
  have herr : |(edge - p * ns * nt * (1 + m / a)) / (ns * a)| ≤
      (nt / N) * (L / a) := by
    rw [abs_div, abs_of_pos (mul_pos hns ha)]
    apply (div_le_iff₀ (mul_pos hns ha)).mpr
    have hc : p * ns * nt * (L / (p * N)) = ((nt / N) * (L / a)) * (ns * a) := by
      field_simp [hp.ne', hN.ne', ha.ne']
    exact hedge.trans_eq hc
  have hu : nt / N ≤ 2 * v := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  rw [he]
  calc
    _ ≤ |(edge - p * ns * nt * (1 + m / a)) / (ns * a)| + |(nt / N - v) * m| := abs_add_le _ _
    _ ≤ (nt / N) * (L / a) + (L / a) * |m| :=
      add_le_add herr (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hsize (abs_nonneg _))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hu (div_nonneg hL ha.le)]

/-- The target in the binomial mean equation is close to the universal cone point. -/
theorem LevelEstimates.normalized_target {N ell : ℕ} {p : Probability} {x : State n}
    (h : LevelEstimates N p ell x) (hN : 0 < N) (hlog : 0 ≤ Real.log (N : ℝ))
    (hs : ∀ t, 0 < x.sizes t) (hu : ∀ t, (x.sizes t : ℝ) ≤ 2 * N * ν n t)
    (s t : History (n + 1)) :
    |(x.edges s t / x.sizes s - (p : ℝ) * x.sizes t) / scale N p - ν n t * μ n s t| ≤
      (2 * ν n t + |μ n s t|) * (Real.log N ^ ell / scale N p) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  exact normalized_target_scalar hn p.property.1
    (Real.sqrt_pos.mpr (mul_pos p.property.1 hn))
    (Real.sq_sqrt (mul_nonneg p.property.1.le hn.le))
    (by exact_mod_cast hs s) (Nat.cast_nonneg _) (pow_nonneg hlog _)
    (h.relative_sizes hN t) (hu t) (h.edges s t)

end MajorityDynamics.Idealized.Process
