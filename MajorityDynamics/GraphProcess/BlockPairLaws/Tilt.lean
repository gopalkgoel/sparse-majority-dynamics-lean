import MajorityDynamics.GraphProcess.BlockPairLaws.Atoms
import MajorityDynamics.Binomial.TiltUniqueness

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Regroup the sufficient statistics by their actual source block. -/
theorem weighted_totals (π : V → History (n+1)) (d : RowArray.Ambient π)
    (a : History (n+1) → History (n+1) → ℝ) :
    (∑ v, ∑ t, (RowArray.values d v t : ℝ) * a (π v) t) =
      ∑ s, ∑ t, (RowArray.totals d s t : ℝ) * a s t := by
  rw [← Finset.sum_fiberwise Finset.univ π]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [RowArray.totals, History.edgeTotals, History.block, Int.cast_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr
  · ext v
    simp
  · intro v hv
    have hvs : π v = s := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hv
    rw [hvs]

def tiltConstant (π : V → History (n+1)) (q r : Local.Tilt n)
    (m : History (n+1) → History (n+1) → ℤ) : ℝ :=
  (∑ v, ∑ t, (Local.trials (Local.partSizes π) (π v) t : ℝ) *
    (Real.log (1 - (q (π v) t : ℝ)) - Real.log (1 - (r (π v) t : ℝ)))) +
  ∑ s, ∑ t, (m s t : ℝ) * (Binomial.logOdds (q s t) - Binomial.logOdds (r s t))

theorem log_mass_difference (π : V → History (n+1)) (q r : Local.Tilt n)
    (d : RowArray.Ambient π) :
    Real.log (mass π q d) - Real.log (mass π r d) =
      tiltConstant π q r (RowArray.totals d) := by
  rw [mass, mass, Real.log_prod (fun v _ => (Binomial.mass_pos _ _ (d v)).ne'),
    Real.log_prod (fun v _ => (Binomial.mass_pos _ _ (d v)).ne')]
  simp_rw [Binomial.log_mass]
  have h := weighted_totals π d
    (fun s t => Binomial.logOdds (q s t) - Binomial.logOdds (r s t))
  unfold tiltConstant
  rw [← h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub,
    Binomial.vector, RowArray.values, Int.cast_natCast]
  ring

/-- On the literal count event, the complete likelihood ratio is constant. -/
theorem mass_ratio (π : V → History (n+1)) (q r : Local.Tilt n)
    (m : History (n+1) → History (n+1) → ℤ) (d : RowArray.Ambient π)
    (hd : RowArray.totals d = m) :
    mass π q d = Real.exp (tiltConstant π q r m) * mass π r d := by
  have h := log_mass_difference π q r d
  rw [hd] at h
  have he := congrArg Real.exp h
  rw [Real.exp_sub, Real.exp_log (mass_pos π q d), Real.exp_log (mass_pos π r d)] at he
  exact (div_eq_iff (mass_pos π r d).ne').mp he

/-- Restricting the original laws to exact totals leaves only a scalar tilt factor. -/
theorem restrict_tilt (π : V → History (n+1)) (q r : Local.Tilt n)
    (m : History (n+1) → History (n+1) → ℤ) :
    (RowArray.law π q).restrict (RowArray.exactTotals π m) =
      ENNReal.ofReal (Real.exp (tiltConstant π q r m)) •
        (RowArray.law π r).restrict (RowArray.exactTotals π m) := by
  apply Measure.ext_of_singleton
  intro d
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton _),
    Measure.restrict_apply (measurableSet_singleton _)]
  by_cases hd : d ∈ RowArray.exactTotals π m
  · rw [Set.singleton_inter_of_mem hd, law_singleton, law_singleton,
      mass_ratio π q r m d hd, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl
  · rw [Set.singleton_inter_of_notMem hd]
    simp

/-- All open-interval tilt arrays give exactly the same count-conditioned law. -/
theorem tilt_independent (y : Local.CoarseData V n) (q r : Local.Tilt n) :
    cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge) =
      cond (RowArray.law y.part r) (RowArray.exactTotals y.part y.edge) := by
  let c := ENNReal.ofReal (Real.exp (tiltConstant y.part q r y.edge))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hres := restrict_tilt y.part q r y.edge
  have htot := congrArg (fun μ : Measure (RowArray.Ambient y.part) => μ Set.univ) hres
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.smul_apply, smul_eq_mul] at htot
  unfold ProbabilityTheory.cond
  rw [htot, hres, smul_smul, ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  change (c⁻¹ * (RowArray.law y.part r (RowArray.exactTotals y.part y.edge))⁻¹ * c) • _ = _
  rw [mul_right_comm, ENNReal.inv_mul_cancel hc hct, one_mul]

/-- The reference success probability used in the paper's binomial comparisons. -/
def halfProbability : Binomial.Probability := ⟨1/2, by norm_num⟩

def halfTilt (n : ℕ) : Local.Tilt n := fun _ _ => halfProbability

theorem tilt_half (y : Local.CoarseData V n) (q : Local.Tilt n) :
    cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge) =
      cond (RowArray.law y.part (halfTilt n)) (RowArray.exactTotals y.part y.edge) :=
  tilt_independent y q (halfTilt n)

end MajorityDynamics.GraphProcess.BlockPairLaws
