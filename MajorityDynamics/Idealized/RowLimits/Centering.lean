import MajorityDynamics.Idealized.RowLimits.GeometryLocal

/-! The diagonal-trial centering correction in E.3 and enlargement of bounds. -/
noncomputable section
open MajorityDynamics.Universal
namespace MajorityDynamics.Idealized.RowLimits
variable {n : ℕ}

theorem centering_error (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s t : History (n + 1)) (ht : 0 < sizes t) (x : ℝ) :
    |(x - (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N) -
      (x - (p : ℝ) * Local.trials sizes s t) / Real.sqrt ((p : ℝ) * N)| ≤
        (p : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  rw [trials_cast sizes s t ht]
  split_ifs
  · have he : (x - (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N) -
        (x - (p : ℝ) * ((sizes t : ℝ) - 1)) / Real.sqrt ((p : ℝ) * N) =
          -((p : ℝ) / Real.sqrt ((p : ℝ) * N)) := by ring
    rw [he, abs_neg, abs_of_nonneg (div_nonneg p.property.1.le (Real.sqrt_nonneg _))]
  · simp only [sub_zero, sub_self, abs_zero]
    exact div_nonneg p.property.1.le (Real.sqrt_nonneg _)

theorem recenter_estimate (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s t : History (n + 1)) (ht : 0 < sizes t)
    (x y C ε : ℝ)
    (h : |(x - (p : ℝ) * Local.trials sizes s t) / Real.sqrt ((p : ℝ) * N) - y| ≤ C * ε)
    (herr : (p : ℝ) / Real.sqrt ((p : ℝ) * N) ≤ ε) :
    |(x - (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N) - y| ≤ (C + 1) * ε := by
  have hc := centering_error N p sizes s t ht x
  have hh := abs_add_le
    ((x - (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N) -
      (x - (p : ℝ) * Local.trials sizes s t) / Real.sqrt ((p : ℝ) * N))
    ((x - (p : ℝ) * Local.trials sizes s t) / Real.sqrt ((p : ℝ) * N) - y)
  rw [sub_add_sub_cancel] at hh
  nlinarith

theorem Estimates.mono {N : ℕ} {p : Binomial.Probability} {sizes : Local.Sizes n}
    {s : History (n + 1)} {σ : Row (n + 1)} {u C C' ε : ℝ}
    (h : Estimates N p sizes s σ u C ε) (hC : C ≤ C') (hε : 0 ≤ ε) :
    Estimates N p sizes s σ u C' ε := by
  have hm := mul_le_mul_of_nonneg_right hC hε
  exact ⟨h.history_probability.trans hm, fun b => (h.split_probability b).trans hm,
    fun t => (h.history_mean t).trans hm, fun b t => (h.child_mean b t).trans hm,
    fun t t' => (h.covariance t t').trans hm⟩

theorem le_error (L N : ℕ) (p : Binomial.Probability) (ξ : ℝ)
    (hN : 1 ≤ N) : ξ ≤ error L N p ξ := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := pow_nonneg (Real.log_nonneg hn) L
  exact le_add_of_nonneg_left (div_nonneg hp (Real.sqrt_nonneg _))

theorem gaussianMass_abs_le_one (σ : Row (n + 1)) (A : Set (Row (n + 1))) :
    |gaussianMass σ A| ≤ 1 := by
  unfold gaussianMass
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact MeasureTheory.measureReal_le_one

end MajorityDynamics.Idealized.RowLimits
