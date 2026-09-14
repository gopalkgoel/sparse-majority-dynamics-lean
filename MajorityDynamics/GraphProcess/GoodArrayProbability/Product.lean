import MajorityDynamics.GraphProcess.BlockPairLaws.Atoms
import MajorityDynamics.GraphProcess.GoodArrays.Counting
import MajorityDynamics.Binomial.ApproximationStatements

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.GoodArrayProbability
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Every factor is the actual singleton of the original binomial coordinate law. -/
theorem row_atom_product (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) :
    (RowArray.law y.part q).real {d} =
      ∏ v, ∏ t, Binomial.Approximation.pointMass
        (Local.trials y.sizes (y.part v) t) (RowArray.naturalRows d v t) (q (y.part v) t) := by
  rw [BlockPairLaws.law_singleton_real]
  simp only [BlockPairLaws.mass, Binomial.mass, Binomial.Approximation.pointMass,
    ProbabilityTheory.binomial_real_singleton, Binomial.closedProbability]
  rfl

/-- A probability measure increases the mass of every subevent when conditioned on a
positive containing event. The positive denominator is retained explicitly. -/
theorem real_le_cond_real {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {S E : Set α} (hE : MeasurableSet E)
    (hSE : S ⊆ E) (hpos : 0 < μ E) : μ.real S ≤ (cond μ E).real S := by
  rw [measureReal_def, measureReal_def, cond_apply hE, Set.inter_eq_right.mpr hSE,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hreal : 0 < (μ E).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hle : (μ E).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using (measure_mono (Set.subset_univ E) : μ E ≤ μ Set.univ))
  have hinv : 1 ≤ (μ E).toReal⁻¹ := (one_le_inv₀ hreal).2 hle
  simpa using mul_le_mul_of_nonneg_right hinv (ENNReal.toReal_nonneg : 0 ≤ (μ S).toReal)

theorem row_atom_le_conditioned (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) (hd : RowArray.totals d = y.edge) :
    (RowArray.law y.part q).real {d} ≤
      (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d} := by
  apply real_le_cond_real _ (Set.toFinite _).measurableSet _ (BlockPairLaws.exactTotals_pos y q)
  exact Set.singleton_subset_iff.mpr hd

theorem E0_le_conditioned (y : Local.CoarseData V n) (q : Local.Tilt n) (T p : ℝ) :
    (RowArray.law y.part q).real (GoodArrays.E0 y T p) ≤
      (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real
        (GoodArrays.E0 y T p) := by
  apply real_le_cond_real _ (Set.toFinite _).measurableSet _ (BlockPairLaws.exactTotals_pos y q)
  intro d hd
  exact ((GoodArrays.mem_E0 y T p d).mp hd).1

/-- A uniform coordinate bound gives precisely `h*N` factors. -/
theorem row_atom_of_coordinate_bound (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) {b : ℝ} (hb : 0 ≤ b)
    (hpoint : ∀ v t, b ≤ Binomial.Approximation.pointMass
      (Local.trials y.sizes (y.part v) t) (RowArray.naturalRows d v t) (q (y.part v) t)) :
    b^(2^(n+1)*Fintype.card V) ≤ (RowArray.law y.part q).real {d} := by
  rw [row_atom_product]
  have h := Finset.prod_le_prod (s := Finset.univ)
    (f := fun _v : V => ∏ _t : History (n+1), b)
    (g := fun v : V => ∏ t : History (n+1), Binomial.Approximation.pointMass
      (Local.trials y.sizes (y.part v) t) (RowArray.naturalRows d v t) (q (y.part v) t))
    (fun _ _ => Finset.prod_nonneg fun _ _ => hb)
    (fun v _ => Finset.prod_le_prod (fun _ _ => hb) (fun t _ => hpoint v t))
  simpa only [Finset.prod_const, Finset.card_univ, history_card, ← pow_mul] using h

/-- A fixed positive coordinate constant is absorbed into an exponential in N. -/
theorem coordinate_power_bound (n N : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Real.exp (-((|Real.log c|+1)*(2^(n+1) : ℕ))*N) *
      x^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) ≤ (c/Real.sqrt x)^(2^(n+1)*N) := by
  let m := 2^(n+1)*N
  have hc' : Real.exp (-(|Real.log c|+1)) ≤ c := by
    calc
      _ ≤ Real.exp (Real.log c) := Real.exp_le_exp.mpr (by linarith [neg_abs_le (Real.log c)])
      _ = c := Real.exp_log hc
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hc' m
  have hs : 0 < (Real.sqrt x)^m := pow_pos (Real.sqrt_pos.2 hx) _
  have hp := div_le_div_of_nonneg_right hpow hs.le
  have hid : Real.exp (-((|Real.log c|+1)*(2^(n+1) : ℕ))*N) *
      x^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) =
        Real.exp (-(|Real.log c|+1))^m / (Real.sqrt x)^m := by
    rw [GoodArrays.sqrt_pow_eq_rpow x hx.le m, ← Real.exp_nat_mul,
      Real.rpow_neg hx.le]
    simp only [div_eq_mul_inv]
    congr 2
    simp only [m, Nat.cast_mul]
    ring
  rw [hid, div_pow]
  exact hp

/-- Finite summation over the entire good set. -/
theorem card_mul_point_le_event (y : Local.CoarseData V n) (q : Local.Tilt n)
    (T p b : ℝ) (hpoint : ∀ d ∈ GoodArrays.E0 y T p,
      b ≤ (RowArray.law y.part q).real {d}) :
    ((GoodArrays.E0 y T p).card : ℝ)*b ≤
      (RowArray.law y.part q).real (GoodArrays.E0 y T p) := by
  rw [← sum_measureReal_singleton]
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    Finset.sum_le_sum (s := GoodArrays.E0 y T p) hpoint

/-- The opposite powers in the counting and point estimates cancel exactly. -/
theorem count_point_cancellation {a b x : ℝ} (hx : 0 < x) (N m : ℕ) :
    (Real.exp (-a*N)*x^((m:ℝ)/2)) *
      (Real.exp (-b*N)*x^(-((m:ℝ)/2))) = Real.exp (-(a+b)*N) := by
  calc
    _ = (Real.exp (-a*N)*Real.exp (-b*N)) *
        (x^((m:ℝ)/2)*x^(-((m:ℝ)/2))) := by ring
    _ = Real.exp (-(a+b)*N) := by
      rw [← Real.exp_add, ← Real.rpow_add hx]
      simp only [add_neg_cancel, Real.rpow_zero, mul_one]
      congr 1
      ring

end MajorityDynamics.GraphProcess.GoodArrayProbability
