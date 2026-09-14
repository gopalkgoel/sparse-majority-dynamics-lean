import MajorityDynamics.Literature.BinomialChernoff
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The truncated exponential-square moment of a binomial variable

For `Y ∼ Bin(r,p)` with `r p ≤ B`, `B > 0`, and `λ = 1/(20 B)`, the manuscript's proof of
Lemma A.10 shows

  `E[exp(λ (Y - r p)²) 1_{|Y - r p| ≤ 2B}] ≤ 7/5 ≤ e^{1/2}`.

The only external input is the accepted scalar Chernoff statement
`MajorityDynamics.Literature.binomial_chernoff`; its two one-sided bounds give the
two-sided tail `P[|Y - rp| > u] ≤ 2 exp(-3u²/(10B))` for `0 < u ≤ 2B`
(`binomial_two_sided_tail`). The layer-cake identity
`E[g(min(|Ȳ|,2B))] = g(0) + ∫₀^{2B} g'(u) P[|Ȳ| > u] du` is Mathlib's
`lintegral_comp_eq_lintegral_meas_lt_mul`; the remaining integral is computed by
the fundamental theorem of calculus. The degenerate case `r p = 0` is a Dirac mass.
-/

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval Set
open scoped ENNReal

namespace MajorityDynamics.Probability.DegreeConcentration

/-! ### The two-sided tail from the scalar Chernoff input -/

theorem binomial_eq_dirac_of_mul_eq_zero (r : ℕ) (p : I) (h : (r : ℝ) * p = 0) :
    binomial r p = Measure.dirac 0 := by
  rcases mul_eq_zero.mp h with hr | hp
  · have : r = 0 := by exact_mod_cast hr
    subst this
    exact binomial_zero
  · have : p = 0 := Subtype.ext hp
    subst this
    simp [binomial]

/-- `P[|Y - rp| > u] ≤ 2 exp(-3u²/(10B))` for `Y ∼ Bin(r,p)`, `rp ≤ B` and `0 < u ≤ 2B`. -/
theorem binomial_two_sided_tail (r : ℕ) (p : I) (B u : ℝ) (hB : 0 < B)
    (hrp : (r : ℝ) * p ≤ B) (hu : 0 < u) (hu2 : u ≤ 2 * B) :
    (binomial r p).real {k : ℕ | u < |(k : ℝ) - r * p|} ≤
      2 * Real.exp (-(3 * u ^ 2) / (10 * B)) := by
  rcases (mul_nonneg (Nat.cast_nonneg r) p.2.1).lt_or_eq with hpos | hzero
  · obtain ⟨hup, hlow⟩ := Literature.binomial_chernoff r p hpos u hu.le
    have hsub : {k : ℕ | u < |(k : ℝ) - r * p|} ⊆
        {k : ℕ | (r : ℝ) * p + u ≤ (k : ℝ)} ∪ {k : ℕ | (k : ℝ) ≤ (r : ℝ) * p - u} := by
      intro k hk
      simp only [mem_ofPred_eq, mem_union] at hk ⊢
      rcases lt_abs.mp hk with h | h
      · left; linarith
      · right; linarith
    have hden : (10 * B) / 3 = 10 * B / 3 := rfl
    have hexp_up : Real.exp (-(u ^ 2) / (2 * ((r : ℝ) * p) + 2 * u / 3)) ≤
        Real.exp (-(3 * u ^ 2) / (10 * B)) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(3 * u ^ 2) / (10 * B) = -(u ^ 2 / (10 * B / 3)) := by
        field_simp
      rw [h1, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by linarith)
    have hexp_low : Real.exp (-(u ^ 2) / (2 * ((r : ℝ) * p))) ≤
        Real.exp (-(3 * u ^ 2) / (10 * B)) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(3 * u ^ 2) / (10 * B) = -(u ^ 2 / (10 * B / 3)) := by
        field_simp
      rw [h1, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by linarith)
    calc (binomial r p).real {k : ℕ | u < |(k : ℝ) - r * p|}
        ≤ (binomial r p).real
            ({k : ℕ | (r : ℝ) * p + u ≤ (k : ℝ)} ∪ {k : ℕ | (k : ℝ) ≤ (r : ℝ) * p - u}) :=
          measureReal_mono hsub
      _ ≤ (binomial r p).real {k : ℕ | (r : ℝ) * p + u ≤ (k : ℝ)} +
            (binomial r p).real {k : ℕ | (k : ℝ) ≤ (r : ℝ) * p - u} := measureReal_union_le _ _
      _ ≤ Real.exp (-(3 * u ^ 2) / (10 * B)) + Real.exp (-(3 * u ^ 2) / (10 * B)) :=
          add_le_add (hup.trans hexp_up) (hlow.trans hexp_low)
      _ = 2 * Real.exp (-(3 * u ^ 2) / (10 * B)) := by ring
  · rw [binomial_eq_dirac_of_mul_eq_zero r p hzero.symm, measureReal_def,
      Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
    have h0 : (0 : ℕ) ∉ {k : ℕ | u < |(k : ℝ) - r * p|} := by
      simp only [mem_ofPred_eq, Nat.cast_zero, zero_sub, abs_neg, not_lt]
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg r) p.2.1), ← hzero]
      exact hu.le
    rw [indicator_of_notMem h0]
    simp only [ENNReal.toReal_zero]
    positivity

/-! ### The truncated exponential-square weight -/

/-- `exp((k - rp)²/(20B))` on `|k - rp| ≤ 2B`, and `0` outside. -/
def truncWeight (r : ℕ) (p : I) (B : ℝ) (k : ℕ) : ℝ :=
  if |(k : ℝ) - r * p| ≤ 2 * B then Real.exp (((k : ℝ) - r * p) ^ 2 / (20 * B)) else 0

theorem truncWeight_nonneg (r : ℕ) (p : I) (B : ℝ) (k : ℕ) : 0 ≤ truncWeight r p B k := by
  unfold truncWeight
  split_ifs <;> positivity

theorem truncWeight_of_le (r : ℕ) (p : I) (B : ℝ) (k : ℕ) (h : |(k : ℝ) - r * p| ≤ 2 * B) :
    truncWeight r p B k = Real.exp (((k : ℝ) - r * p) ^ 2 / (20 * B)) := by
  simp [truncWeight, h]

/-- The antiderivative identity `∫₀ˣ 2λt e^{λt²} dt = e^{λx²} - 1`. -/
theorem integral_deriv_exp_mul_sq (l x : ℝ) :
    ∫ t in (0)..x, 2 * l * t * Real.exp (l * t ^ 2) = Real.exp (l * x ^ 2) - 1 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t ↦ Real.exp (l * t ^ 2))
      (2 * l * t * Real.exp (l * t ^ 2)) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul l).exp
    refine this.congr_deriv ?_
    simp
    ring
  have hcont : Continuous fun t : ℝ ↦ 2 * l * t * Real.exp (l * t ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable _ _)]
  simp

/-- `∫₀^{2B} 4λt e^{-t²/(4B)} dt = 8λB (1 - e^{-B}) ≤ 8λB`, with `λ = 1/(20B)`. -/
theorem integral_tail_kernel_le (B : ℝ) (hB : 0 < B) :
    ∫ t in (0)..(2 * B), 4 * (1 / (20 * B)) * t * Real.exp (-(t ^ 2) / (4 * B)) ≤ 2 / 5 := by
  have hB' : B ≠ 0 := hB.ne'
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t ↦ -(8 * (1 / (20 * B)) * B) * Real.exp (-(t ^ 2) / (4 * B)))
      (4 * (1 / (20 * B)) * t * Real.exp (-(t ^ 2) / (4 * B))) t := by
    intro t
    have := (((hasDerivAt_pow 2 t).neg).div_const (4 * B)).exp.const_mul (-(8 * (1 / (20 * B)) * B))
    refine this.congr_deriv ?_
    simp
    field_simp
    ring
  have hcont : Continuous fun t : ℝ ↦ 4 * (1 / (20 * B)) * t * Real.exp (-(t ^ 2) / (4 * B)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable _ _)]
  have hval : -(8 * (1 / (20 * B)) * B) = -(2 / 5) := by field_simp; ring
  rw [hval]
  have hexp_pos : 0 < Real.exp (-((2 * B) ^ 2) / (4 * B)) := Real.exp_pos _
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
    Real.exp_zero, mul_one]
  linarith

/-- The manuscript's single-variable bound: for `Y ∼ Bin(r,p)` with `rp ≤ B` and `B > 0`,
`E[exp((Y - rp)²/(20B)) 1_{|Y - rp| ≤ 2B}] ≤ 7/5 ≤ e^{1/2}`. -/
theorem truncated_exp_moment (r : ℕ) (p : I) (B : ℝ) (hB : 0 < B) (hrp : (r : ℝ) * p ≤ B) :
    ∫⁻ k, ENNReal.ofReal (truncWeight r p B k) ∂(binomial r p) ≤
      ENNReal.ofReal (Real.exp (1 / 2)) := by
  set μ := binomial r p with hμ
  set l : ℝ := 1 / (20 * B) with hl
  have hlpos : 0 < l := by positivity
  let f : ℕ → ℝ := fun k ↦ min |(k : ℝ) - r * p| (2 * B)
  let g : ℝ → ℝ := fun t ↦ 2 * l * t * Real.exp (l * t ^ 2)
  have hf_nn : ∀ k, 0 ≤ f k := fun k ↦ le_min (abs_nonneg _) (by positivity)
  have hf_le : ∀ k, f k ≤ 2 * B := fun k ↦ min_le_right _ _
  have hg_cont : Continuous g := by fun_prop
  have hg_nn : ∀ t, 0 ≤ t → 0 ≤ g t := fun t ht ↦ by
    simp only [g]; positivity
  -- pointwise domination by `exp(λ f(k)²)`
  have hpt : ∀ k, truncWeight r p B k ≤ Real.exp (l * (f k) ^ 2) := by
    intro k
    unfold truncWeight
    split_ifs with h
    · have : f k = |(k : ℝ) - r * p| := min_eq_left h
      rw [this, sq_abs, hl]
      apply le_of_eq
      congr 1
      field_simp
    · positivity
  -- layer cake
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ (ae_of_all _ hf_nn)
    (Measurable.of_discrete (f := f)).aemeasurable (fun t _ ↦ hg_cont.intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ hg_nn t (le_of_lt ht)))
  have hFTC : ∀ k, ∫ t in (0)..f k, g t = Real.exp (l * (f k) ^ 2) - 1 := fun k ↦
    integral_deriv_exp_mul_sq l (f k)
  -- the right-hand side of the layer cake is at most `2/5`
  have hrhs : ∫⁻ t in Ioi (0 : ℝ), μ {a : ℕ | t < f a} * ENNReal.ofReal (g t) ≤
      ENNReal.ofReal (2 / 5) := by
    let h : ℝ → ℝ := fun t ↦ 4 * (1 / (20 * B)) * t * Real.exp (-(t ^ 2) / (4 * B))
    have hpt' : ∀ t ∈ Ioi (0 : ℝ), μ {a : ℕ | t < f a} * ENNReal.ofReal (g t) ≤
        (Ioo (0 : ℝ) (2 * B)).indicator (fun t ↦ ENNReal.ofReal (h t)) t := by
      intro t ht
      have ht0 : 0 < t := ht
      by_cases ht2 : t < 2 * B
      · rw [Set.indicator_of_mem (mem_Ioo.mpr ⟨ht0, ht2⟩)]
        have hset : {a : ℕ | t < f a} = {a : ℕ | t < |(a : ℝ) - r * p|} := by
          ext a
          simp only [mem_ofPred_eq, f, lt_min_iff, ht2, and_true]
        rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top μ _), ← measureReal_def,
          ← ENNReal.ofReal_mul (measureReal_nonneg)]
        apply ENNReal.ofReal_le_ofReal
        have htail := binomial_two_sided_tail r p B t hB hrp ht0 ht2.le
        have hg : 0 ≤ g t := hg_nn t ht0.le
        calc μ.real {a : ℕ | t < |(a : ℝ) - r * p|} * g t
            ≤ 2 * Real.exp (-(3 * t ^ 2) / (10 * B)) * g t :=
              mul_le_mul_of_nonneg_right htail hg
          _ = h t := by
              simp only [g, h]
              rw [show 2 * Real.exp (-(3 * t ^ 2) / (10 * B)) * (2 * l * t * Real.exp (l * t ^ 2)) =
                  4 * l * t * (Real.exp (-(3 * t ^ 2) / (10 * B)) * Real.exp (l * t ^ 2)) by ring,
                ← Real.exp_add, hl]
              congr 1
              congr 1
              field_simp
              ring
      · have hset : {a : ℕ | t < f a} = ∅ := by
          ext a
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
          exact (hf_le a).trans (not_lt.mp ht2)
        rw [hset, measure_empty, zero_mul]
        exact zero_le
    calc ∫⁻ t in Ioi (0 : ℝ), μ {a : ℕ | t < f a} * ENNReal.ofReal (g t)
        ≤ ∫⁻ t in Ioi (0 : ℝ), (Ioo (0 : ℝ) (2 * B)).indicator (fun t ↦ ENNReal.ofReal (h t)) t :=
          setLIntegral_mono' measurableSet_Ioi hpt'
      _ = ∫⁻ t in Ioo (0 : ℝ) (2 * B), ENNReal.ofReal (h t) := by
          rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
            inter_eq_left.mpr Ioo_subset_Ioi_self]
      _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) (2 * B), h t) := by
          have hcont : Continuous h := by fun_prop
          rw [ofReal_integral_eq_lintegral_ofReal
            ((hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
            ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht ↦ by
              simp only [h]; have := ht.1; positivity))]
      _ ≤ ENNReal.ofReal (2 / 5) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity)]
          exact integral_tail_kernel_le B hB
  -- assemble
  calc ∫⁻ k, ENNReal.ofReal (truncWeight r p B k) ∂μ
      ≤ ∫⁻ k, ENNReal.ofReal (Real.exp (l * (f k) ^ 2)) ∂μ :=
        lintegral_mono fun k ↦ ENNReal.ofReal_le_ofReal (hpt k)
    _ = ∫⁻ k, (ENNReal.ofReal (∫ t in (0)..f k, g t) + 1) ∂μ := by
        apply lintegral_congr
        intro k
        rw [hFTC k, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by
            linarith [Real.add_one_le_exp (l * (f k) ^ 2), mul_nonneg hlpos.le (sq_nonneg (f k))])
            zero_le_one,
          sub_add_cancel]
    _ = (∫⁻ t in Ioi (0 : ℝ), μ {a : ℕ | t < f a} * ENNReal.ofReal (g t)) + 1 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, hlayer]
    _ ≤ ENNReal.ofReal (2 / 5) + 1 := add_le_add hrhs le_rfl
    _ = ENNReal.ofReal (7 / 5) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) zero_le_one]
        norm_num
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have := Real.add_one_le_exp (1 / 2 : ℝ)
        linarith

end MajorityDynamics.Probability.DegreeConcentration
