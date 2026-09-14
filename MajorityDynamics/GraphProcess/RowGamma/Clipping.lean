import MajorityDynamics.GraphProcess.RowGamma.Empirical
import MajorityDynamics.GraphProcess.RowConcentration.Expectations
import MajorityDynamics.GraphProcess.RowConcentration.Bounded

/-! Independent clipped squares under the actual history-conditioned row law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal RowConcentration
variable {V : Type*} [Fintype V] {n : ℕ}

def clippedSquare (p : ℝ) (π : V → History (n + 1)) (v : V)
    (t : History (n + 1)) (d : RowArray.Ambient π) : ℝ :=
  min (normalizedSquare p π v t d) ((Real.log (Fintype.card V))^2)

def clippedBlockVariable (p : ℝ) (π : V → History (n + 1))
    (s t : History (n + 1)) (v : V) (d : RowArray.Ambient π) : ℝ :=
  if π v = s then clippedSquare p π v t d else 0

theorem clippedSquare_bounds {p : ℝ} (hp : 0 ≤ p)
    (π : V → History (n + 1)) (v : V) (t : History (n + 1))
    (d : RowArray.Ambient π) :
    0 ≤ clippedSquare p π v t d ∧
      clippedSquare p π v t d ≤ (Real.log (Fintype.card V))^2 :=
  ⟨le_min (normalizedSquare_nonneg hp π v t d) (sq_nonneg _), min_le_right _ _⟩

theorem clippedBlockVariable_bounds {p : ℝ} (hp : 0 ≤ p)
    (π : V → History (n + 1)) (s t : History (n + 1))
    (v : V) (d : RowArray.Ambient π) :
    clippedBlockVariable p π s t v d ∈ Set.Icc 0 ((Real.log (Fintype.card V))^2) := by
  unfold clippedBlockVariable
  split_ifs
  · exact clippedSquare_bounds hp π v t d
  · exact ⟨le_rfl, sq_nonneg _⟩

theorem sum_clippedBlockVariable (p : ℝ) (π : V → History (n + 1))
    (s t : History (n + 1)) (d : RowArray.Ambient π) :
    ∑ v, clippedBlockVariable p π s t v d =
      ∑ v ∈ History.block π s, clippedSquare p π v t d := by
  simp only [clippedBlockVariable, History.block, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> rfl

theorem independent_clippedBlockVariable (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) (p : ℝ)
    (s t : History (n + 1)) :
    iIndepFun (clippedBlockVariable p y.part s t) (conditionedLaw y q) := by
  have h := (RowArray.conditioned_independent_rows y.part q (row_history_pos y q hφ hc)).comp
    (fun v a => if y.part v = s then
      min (((a t : ℝ) - p * Local.partSizes y.part t)^2 /
        (p * Fintype.card V)) ((Real.log (Fintype.card V))^2) else 0)
    (fun _ => measurable_of_countable _)
  convert h using 1 <;> try rfl

theorem clippedBlockVariable_integrable (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ p : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) (hp : 0 ≤ p)
    (s t : History (n + 1)) (v : V) :
    Integrable (clippedBlockVariable p y.part s t v) (conditionedLaw y q) := by
  let := conditioned_probability y q hφ hc
  exact Integrable.of_mem_Icc 0 ((Real.log (Fintype.card V))^2)
    (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall (clippedBlockVariable_bounds hp y.part s t v))

theorem expected_clipped_sum_le (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ p C0 : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) (hp : 0 ≤ p)
    (hC0 : 0 ≤ C0)
    (hint : ∀ v t, Integrable (normalizedSquare p y.part v t) (conditionedLaw y q))
    (hexp : ∀ v t, ∫ d, normalizedSquare p y.part v t d ∂conditionedLaw y q ≤ C0)
    (s t : History (n + 1)) :
    ∫ d, ∑ v, clippedBlockVariable p y.part s t v d ∂conditionedLaw y q ≤
      C0 * Fintype.card V := by
  let := conditioned_probability y q hφ hc
  rw [integral_finsetSum _ (fun v _ => clippedBlockVariable_integrable y q hφ hc hp s t v)]
  calc
    _ ≤ ∑ _v : V, C0 := Finset.sum_le_sum fun v _ => by
      by_cases hv : y.part v = s
      · refine (integral_mono (clippedBlockVariable_integrable y q hφ hc hp s t v)
          (hint v t) ?_).trans (hexp v t)
        intro d
        simp only [clippedBlockVariable, hv, if_true, clippedSquare]
        exact min_le_left _ _
      · simpa [clippedBlockVariable, hv] using hC0
    _ = _ := by simp [mul_comm]

theorem clipped_block_tail (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ p C0 : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) (hp : 0 ≤ p)
    (hC0 : 0 ≤ C0) (hN : 0 < Fintype.card V)
    (hint : ∀ v t, Integrable (normalizedSquare p y.part v t) (conditionedLaw y q))
    (hexp : ∀ v t, ∫ d, normalizedSquare p y.part v t d ∂conditionedLaw y q ≤ C0)
    (s t : History (n + 1)) :
    (conditionedLaw y q).real {d | (C0 + 1) * Fintype.card V <
      ∑ v ∈ History.block y.part s, clippedSquare p y.part v t d} ≤
      2 * Real.exp (-2 * Fintype.card V / (Real.log (Fintype.card V))^4) := by
  let := conditioned_probability y q hφ hc
  have hh := Bounded.sum_integral_tail (independent_clippedBlockVariable y q hφ hc p s t)
    (fun _ => (measurable_of_countable _).aemeasurable) (sq_nonneg (Real.log (Fintype.card V)))
    (fun v => Filter.Eventually.of_forall (clippedBlockVariable_bounds hp y.part s t v))
    Finset.univ (Nat.cast_nonneg (Fintype.card V))
  have he := expected_clipped_sum_le y q hφ hc hp hC0 hint hexp s t
  have hNr : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hr : -2 * (Fintype.card V : ℝ)^2 /
      ((Fintype.card V : ℝ) * ((Real.log (Fintype.card V))^2)^2) =
      -2 * Fintype.card V / (Real.log (Fintype.card V))^4 := by
    rw [← pow_mul]
    norm_num
    field_simp
  rw [Finset.card_univ, hr] at hh
  refine le_trans (measureReal_mono ?_ (by finiteness)) hh
  intro d hd
  have hd' : (C0 + 1) * Fintype.card V < ∑ v, clippedBlockVariable p y.part s t v d := by
    simpa only [sum_clippedBlockVariable] using (show (C0 + 1) * Fintype.card V <
      ∑ v ∈ History.block y.part s, clippedSquare p y.part v t d from hd)
  exact (by nlinarith : (Fintype.card V : ℝ) ≤
    (∑ v, clippedBlockVariable p y.part s t v d) -
      ∫ d, ∑ v, clippedBlockVariable p y.part s t v d ∂conditionedLaw y q).trans (le_abs_self _)

theorem clippedSquare_eq_on_R1 (y : Local.CoarseData V n) {p : ℝ}
    (hp : 0 < p) (hN : 0 < Fintype.card V)
    (hlog : 1 ≤ Real.log (Fintype.card V))
    (d : RowArray.Ambient y.part) (hd : R1 y p d) (v : V) (t : History (n + 1)) :
    clippedSquare p y.part v t d = normalizedSquare p y.part v t d := by
  have hNr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (Fintype.card V) := by linarith
  have hpow : (Real.log (Fintype.card V))^(2/3 : ℝ) ≤ Real.log (Fintype.card V) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (2/3 : ℝ) ≤ 1)
  have habs := (hd v t).trans (mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _))
  have hs := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hlog0) |>.mpr habs
  rw [sq_abs, mul_pow, Real.sq_sqrt (mul_pos hp hNr).le] at hs
  apply min_eq_left
  exact (div_le_iff₀ (mul_pos hp hNr)).mpr (by simpa [mul_comm, Local.CoarseData.sizes] using hs)

theorem gamma_failure (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ p C0 : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) (hp : 0 < p)
    (hC0 : 0 ≤ C0) (hN : 0 < Fintype.card V)
    (hlog : 1 ≤ Real.log (Fintype.card V))
    (hint : ∀ v t, Integrable (normalizedSquare p y.part v t) (conditionedLaw y q))
    (hexp : ∀ v t, ∫ d, normalizedSquare p y.part v t d ∂conditionedLaw y q ≤ C0) :
    (conditionedLaw y q).real {d | ¬ RowArray.Gamma y.part (RowArray.totals d) (C0+1) p d} ≤
      (conditionedLaw y q).real {d | ¬ R1 y p d} +
      (Fintype.card (History (n+1)) : ℝ)^2 *
        (2 * Real.exp (-2 * Fintype.card V / (Real.log (Fintype.card V))^4)) := by
  let := conditioned_probability y q hφ hc
  let bad := fun i : History (n+1) × History (n+1) =>
    {d : RowArray.Ambient y.part | (C0+1) * Fintype.card V <
      ∑ v ∈ History.block y.part i.1, clippedSquare p y.part v i.2 d}
  have hsub : {d | ¬ RowArray.Gamma y.part (RowArray.totals d) (C0+1) p d} ⊆
      {d | ¬ R1 y p d} ∪ ⋃ i, bad i := by
    intro d hd
    by_cases hr : R1 y p d
    · apply Or.inr
      by_contra hbad
      have hb : ∀ s t, ∑ v ∈ History.block y.part s,
          clippedSquare p y.part v t d ≤ (C0+1) * Fintype.card V := by
        intro s t
        by_contra hh
        apply hbad
        exact Set.mem_iUnion.mpr ⟨(s,t), not_le.mp hh⟩
      apply hd
      apply gamma_of_normalized_sums y.part d hp hN
      intro s t
      simpa only [clippedSquare_eq_on_R1 y hp hN hlog d hr] using hb s t
    · exact Or.inl hr
  calc
    _ ≤ (conditionedLaw y q).real ({d | ¬ R1 y p d} ∪ ⋃ i, bad i) :=
      measureReal_mono hsub (by finiteness)
    _ ≤ (conditionedLaw y q).real {d | ¬ R1 y p d} +
        (conditionedLaw y q).real (⋃ i, bad i) := measureReal_union_le _ _
    _ ≤ (conditionedLaw y q).real {d | ¬ R1 y p d} +
        ∑ i, (conditionedLaw y q).real (bad i) :=
      add_le_add le_rfl (measureReal_iUnion_fintype_le _)
    _ ≤ (conditionedLaw y q).real {d | ¬ R1 y p d} +
        ∑ _i : History (n+1) × History (n+1),
          (2 * Real.exp (-2 * Fintype.card V / (Real.log (Fintype.card V))^4)) := by
      apply add_le_add le_rfl
      exact Finset.sum_le_sum fun i _ => clipped_block_tail y q hφ hc hp.le hC0 hN hint hexp i.1 i.2
    _ = _ := by simp [sq, mul_assoc]

end MajorityDynamics.GraphProcess.RowGamma

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.independent_clippedBlockVariable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowGamma.independent_clippedBlockVariable

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.expected_clipped_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowGamma.expected_clipped_sum_le

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.clipped_block_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowGamma.clipped_block_tail

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.clippedSquare_eq_on_R1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowGamma.clippedSquare_eq_on_R1

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.gamma_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowGamma.gamma_failure
