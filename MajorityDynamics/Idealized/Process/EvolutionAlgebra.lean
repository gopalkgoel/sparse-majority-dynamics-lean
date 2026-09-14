import MajorityDynamics.Idealized.Process.Basic
import MajorityDynamics.Idealized.RowLimits.ContractBridges

/-! Exact local-template identities and the scalar error estimates in Step 7
of Theorem 5.2. No asymptotic expansion is assumed in these lemmas. -/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process
open Universal Local
variable {n : ℕ}

def childMean (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) : ℝ :=
  Binomial.conditionalMean (Local.trials sizes s) (q s) (Local.childSupport sizes s b) t

theorem childMean_eq_binomialMean (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (σ : History (n + 1) → Row (n + 1))
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    childMean sizes (fun s => RowLimits.rowTilt N p (σ s)) s b t =
      RowLimits.binomialMean N p sizes s (childSupport sizes s b) t (σ s) :=
  (RowLimits.binomialMean_eq_conditionalMean N p sizes s _ t (σ s)).symm

theorem splitProbability_nonneg (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s : History (n + 1)) (b : Bool) : 0 ≤ splitProbability sizes q s b := by
  unfold splitProbability Binomial.eventMass
  exact div_nonneg (Finset.sum_nonneg fun a _ => (Binomial.mass_pos _ _ a).le)
    (Finset.sum_nonneg fun a _ => (Binomial.mass_pos _ _ a).le)

theorem templateSizes_nonneg (sizes : Local.Sizes n) (q : Local.Tilt n)
    (u : History (n + 2)) : 0 ≤ templateSizes sizes q u :=
  mul_nonneg (Nat.cast_nonneg _) (splitProbability_nonneg sizes q (parent u) (last u))

theorem splitMoment_eq_probability_mul_childMean (sizes : Local.Sizes n)
    (q : Local.Tilt n) (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    splitMoment sizes q s b t = splitProbability sizes q s b * childMean sizes q s b t := by
  classical
  by_cases hS : (childSupport sizes s b).Nonempty
  · have hm := (Binomial.eventMass_pos (trials sizes s) (q s) hS).ne'
    have hh := (Binomial.eventMass_pos (trials sizes s) (q s)
      (hS.mono (childSupport_subset sizes s b))).ne'
    simp only [splitMoment, splitProbability, childMean, Binomial.conditionalMean,
      Binomial.expectation, Binomial.conditionalWeight, div_mul_eq_mul_div, ← Finset.sum_div]
    field_simp
  · have hS' := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [splitMoment, splitProbability, childMean, Binomial.conditionalMean,
      Binomial.expectation, Binomial.conditionalWeight, Binomial.eventMass, hS']

theorem templateHalfEdges_eq_size_mul_childMean (sizes : Local.Sizes n) (q : Local.Tilt n)
    (u : History (n + 2)) (t : History (n + 1)) :
    templateHalfEdges sizes q u t =
      templateSizes sizes q u * childMean sizes q (parent u) (last u) t := by
  simp only [templateHalfEdges, templateSizes, splitMoment_eq_probability_mul_childMean, mul_assoc]

/-- Converting an absolute size error into the reciprocal error needed in
the conditional-mean normalization. -/
theorem reciprocal_size_error {N z v ρ : ℝ} (hN : 0 < N) (hv : 0 < v)
    (hz : N * v / 2 ≤ z) (hclose : |z - N * v| ≤ N * ρ) :
    0 < z ∧ N / z ≤ 2 / v ∧ |N / z - 1 / v| ≤ 2 * ρ / v ^ 2 := by
  have hz0 : 0 < z := (by positivity : 0 < N * v / 2).trans_le hz
  have hρ : 0 ≤ ρ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hclose) hN
  refine ⟨hz0, ?_, ?_⟩
  · apply (div_le_div_iff₀ hz0 hv).mpr
    nlinarith
  · have heq : N / z - 1 / v = -(z - N * v) / (z * v) := by field_simp; ring
    rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos hz0 hv)]
    apply (div_le_iff₀ (mul_pos hz0 hv)).mpr
    refine hclose.trans ?_
    have hm := mul_le_mul_of_nonneg_right hz (show 0 ≤ 2 * ρ / v by positivity)
    convert hm using 1 <;> field_simp

/-- The first-order coefficient of a conditional mean is its Gaussian mean
divided by the universal part size. The remainder is one order smaller. -/
theorem conditional_mean_relative_error {N p a z v m b ρ K B : ℝ}
    (hN : 0 < N) (_hp : 0 < p) (ha : 0 < a) (ha2 : a ^ 2 = p * N)
    (hv : 0 < v) (hz : N * v / 2 ≤ z) (hclose : |z - N * v| ≤ N * ρ)
    (_hK : 0 ≤ K) (hB : |b| ≤ B)
    (hmean : |(m - p * z) / a - b| ≤ K * ρ) :
    |m / (p * z) - (1 + (b / v) / a)| ≤
      (2 * K / v + 2 * B / v ^ 2) * ρ / a := by
  obtain ⟨hz0, hrec, herr⟩ := reciprocal_size_error hN hv hz hclose
  have hρ : 0 ≤ ρ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hclose) hN
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have heq : m / (p * z) - (1 + (b / v) / a) =
      (N / z * ((m - p * z) / a - b) + (N / z - 1 / v) * b) / a := by
    have hp' : p = a ^ 2 / N := (eq_div_iff hN.ne').mpr ha2.symm
    rw [hp']
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos ha]
  calc
    _ ≤ (|N / z| * |(m - p * z) / a - b| + |N / z - 1 / v| * |b|) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      simpa only [abs_mul] using abs_add_le (N / z * ((m - p * z) / a - b))
        ((N / z - 1 / v) * b)
    _ ≤ ((2 / v) * (K * ρ) + (2 * ρ / v ^ 2) * B) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      apply add_le_add
      · apply mul_le_mul _ hmean (abs_nonneg _) (by positivity)
        simpa only [abs_of_pos (div_pos hN hz0)] using hrec
      · exact mul_le_mul herr hB (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- A split-probability error propagates directly to the unrounded size. -/
theorem split_size_error {N z v r q ρ K : ℝ} (hN : 0 ≤ N)
    (hz : 0 ≤ z) (hzN : z ≤ 2 * N) (hρ : 0 ≤ ρ) (_hK : 0 ≤ K)
    (hr : |r| ≤ 1) (hsize : |z - N * v| ≤ N * ρ)
    (hprob : |q - r| ≤ K * ρ) :
    |z * q - N * (v * r)| ≤ (2 * K + 1) * N * ρ := by
  calc
    _ = |z * (q - r) + (z - N * v) * r| := by congr 1; ring
    _ ≤ |z| * |q - r| + |z - N * v| * |r| := by
      simpa only [abs_mul] using abs_add_le (z * (q - r)) ((z - N * v) * r)
    _ ≤ (2 * N) * (K * ρ) + (N * ρ) * 1 := by
      apply add_le_add
      · apply mul_le_mul _ hprob (abs_nonneg _) (by positivity)
        simpa only [abs_of_nonneg hz] using hzN
      · exact mul_le_mul hsize hr (abs_nonneg _) (mul_nonneg hN hρ)
    _ = _ := by ring

theorem templateEdges_relative_identity (sizes : Local.Sizes n) (m : Local.EdgeCounts n)
    (q : Local.Tilt n) (p : ℝ) (hp : p ≠ 0)
    (u v : History (n + 2)) (hu : (sizes (parent u) : ℝ) ≠ 0)
    (hv : (sizes (parent v) : ℝ) ≠ 0) (hm : m (parent u) (parent v) ≠ 0) :
    templateEdges sizes m q u v = p * templateSizes sizes q u * templateSizes sizes q v *
      ((childMean sizes q (parent u) (last u) (parent v) / (p * sizes (parent v))) *
        (childMean sizes q (parent v) (last v) (parent u) / (p * sizes (parent u))) /
        (m (parent u) (parent v) / (p * sizes (parent u) * sizes (parent v)))) := by
  rw [templateEdges, templateHalfEdges_eq_size_mul_childMean,
    templateHalfEdges_eq_size_mul_childMean]
  field_simp

/-- Rounding changes a nonnegative real size by less than one. -/
theorem floor_size_error {z t e : ℝ} (hz : 0 ≤ z) (he : |z - t| ≤ e) :
    |(⌊z⌋₊ : ℝ) - t| ≤ e + 1 := by
  have hlo := Nat.floor_le hz
  have hhi := Nat.lt_floor_add_one z
  have hf : |(⌊z⌋₊ : ℝ) - z| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  exact (abs_sub_le _ _ _).trans ((add_le_add hf he).trans_eq (by ring))

/-- Quantitative effect of replacing two local template sizes by their floors.
The lower bound is imposed on the already rounded sizes. -/
theorem rounded_product_ratio {N c u v U V : ℝ} (hN : 1 ≤ N) (hc : 0 < c)
    (hu : c * N ≤ u) (hv : c * N ≤ v)
    (hU : 0 ≤ U - u ∧ U - u ≤ 1) (hV : 0 ≤ V - v ∧ V - v ≤ 1) :
    0 ≤ U * V / (u * v) ∧ U * V / (u * v) ≤ (1 + 1 / c) ^ 2 ∧
      |U * V / (u * v) - 1| ≤ (2 / c + 1 / c ^ 2) / N := by
  have hN0 : 0 < N := by linarith
  have hu0 : 0 < u := (mul_pos hc hN0).trans_le hu
  have hv0 : 0 < v := (mul_pos hc hN0).trans_le hv
  have hU0 : 0 ≤ U := by linarith [hU.1]
  have hV0 : 0 ≤ V := by linarith [hV.1]
  have huc : c ≤ u := (le_mul_of_one_le_right hc.le hN).trans hu
  have hvc : c ≤ v := (le_mul_of_one_le_right hc.le hN).trans hv
  have hiu : 1 / u ≤ 1 / c := one_div_le_one_div_of_le hc huc
  have hiv : 1 / v ≤ 1 / c := one_div_le_one_div_of_le hc hvc
  have hru : U / u ≤ 1 + 1 / c := by
    have hh := div_le_div_of_nonneg_right hU.2 hu0.le
    have hid : (U - u) / u = U / u - 1 := by field_simp
    rw [hid] at hh
    linarith
  have hrv : V / v ≤ 1 + 1 / c := by
    have hh := div_le_div_of_nonneg_right hV.2 hv0.le
    have hid : (V - v) / v = V / v - 1 := by field_simp
    rw [hid] at hh
    linarith
  have hid : U * V / (u * v) = (U / u) * (V / v) := by ring
  refine ⟨div_nonneg (mul_nonneg hU0 hV0) (mul_pos hu0 hv0).le, ?_, ?_⟩
  · rw [hid, pow_two]
    exact mul_le_mul hru hrv (div_nonneg hV0 hv0.le) (by positivity)
  · have hdiff : U * V / (u * v) - 1 =
        (U - u) / u + (V - v) / v + ((U - u) / u) * ((V - v) / v) := by
      field_simp
      ring
    have hdu : 0 ≤ (U - u) / u := div_nonneg hU.1 hu0.le
    have hdv : 0 ≤ (V - v) / v := div_nonneg hV.1 hv0.le
    have hdu' : (U - u) / u ≤ 1 / (c * N) :=
      div_le_div₀ (by norm_num) hU.2 (mul_pos hc hN0) hu
    have hdv' : (V - v) / v ≤ 1 / (c * N) :=
      div_le_div₀ (by norm_num) hV.2 (mul_pos hc hN0) hv
    rw [hdiff, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 1 / (c * N) + 1 / (c * N) + (1 / (c * N)) * (1 / (c * N)) := by
        exact add_le_add (add_le_add hdu' hdv') (mul_le_mul hdu' hdv' hdv (by positivity))
      _ ≤ (2 / c + 1 / c ^ 2) / N := by
        have hiN : 1 / N ≤ 1 := (div_le_one hN0).mpr hN
        have hprod := mul_le_mul_of_nonneg_left hiN (show 0 ≤ 1 / (c ^ 2 * N) by positivity)
        calc
          _ = 2 / (c * N) + 1 / (c ^ 2 * N) * (1 / N) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
          _ ≤ 2 / (c * N) + 1 / (c ^ 2 * N) * 1 := add_le_add le_rfl hprod
          _ = _ := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring

/-- A first-order edge estimate survives the deterministic floor operation. -/
theorem rounded_edge_error {R z w δ K B F H : ℝ}
    (hR : 0 ≤ R) (hR' : R ≤ H) (hz : |z - w| ≤ K * δ)
    (hw : |w| ≤ B) (hround : |R - 1| ≤ F * δ)
    (hδ : 0 ≤ δ) (_hK : 0 ≤ K) (_hB : 0 ≤ B) (hF : 0 ≤ F) :
    |R * z - w| ≤ (H * K + F * B) * δ := by
  calc
    _ = |R * (z - w) + (R - 1) * w| := by congr 1; ring
    _ ≤ |R| * |z - w| + |R - 1| * |w| := by
      simpa only [abs_mul] using abs_add_le (R * (z - w)) ((R - 1) * w)
    _ ≤ H * (K * δ) + (F * δ) * B := by
      exact add_le_add
        (mul_le_mul (by simpa only [abs_of_nonneg hR] using hR') hz (abs_nonneg _)
          (hR.trans hR'))
        (mul_le_mul hround hw (abs_nonneg _) (mul_nonneg hF hδ))
    _ = _ := by ring

end MajorityDynamics.Idealized.Process
