import MajorityDynamics.Probability.FixedSizeExponential.Basic

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The finite law bridges for prescribed-size subsets

This file proves that the uniform prescribed-size law is the conditional law of
independent Bernoulli bits, for every success probability in `(0,1)`.  It also
proves the exact inclusion and mean identities, the nonnegative conditional
expectation comparison, and the independent-product MGF formula used by the
main estimate.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.FixedSizeExponential

/-- The bit-vector/subset equivalence. -/
def bitFinsetEquiv (n : ℕ) : Bit n ≃ Finset (Fin n) where
  toFun := bitSet
  invFun := fun S i => if i ∈ S then true else false
  left_inv := by
    intro ξ
    funext i
    cases h : ξ i <;> simp [bitSet, h]
  right_inv := by
    intro S
    ext i
    by_cases h : i ∈ S <;> simp [bitSet, h]

/-- Restriction of the bit/subset equivalence to prescribed cardinality. -/
def fixedSizeBitFinsetEquiv (n s : ℕ) :
    {ξ : Bit n // bitCount ξ = s} ≃ {S : Finset (Fin n) // S.card = s} where
  toFun := fun ξ => ⟨bitSet ξ.1, ξ.2⟩
  invFun := fun S =>
    ⟨(bitFinsetEquiv n).symm S.1, by
      change ((bitFinsetEquiv n) ((bitFinsetEquiv n).symm S.1)).card = s
      rw [(bitFinsetEquiv n).apply_symm_apply]
      exact S.2⟩
  left_inv := by
    intro ξ
    apply Subtype.ext
    exact (bitFinsetEquiv n).symm_apply_apply ξ.1
  right_inv := by
    intro S
    apply Subtype.ext
    exact (bitFinsetEquiv n).apply_symm_apply S.1

/-- Exactly `n.choose s` bit vectors select `s` coordinates. -/
theorem fixedSizeEvent_card (n s : ℕ) :
    (fixedSizeEvent n s).card = n.choose s := by
  classical
  calc
    (fixedSizeEvent n s).card =
        Fintype.card {ξ : Bit n // bitCount ξ = s} := by
      symm
      apply Fintype.card_of_subtype (fixedSizeEvent n s)
      intro ξ
      simp [fixedSizeEvent]
    _ = Fintype.card {S : Finset (Fin n) // S.card = s} :=
      Fintype.card_congr (fixedSizeBitFinsetEquiv n s)
    _ = Nat.choose (Fintype.card (Fin n)) s :=
      Fintype.card_finset_len (α := Fin n) s
    _ = n.choose s := by simp

/-- The prescribed-size event is nonempty whenever its size is at most `n`. -/
theorem fixedSizeEvent_nonempty {n s : ℕ} (hs : s ≤ n) :
    (fixedSizeEvent n s).Nonempty := by
  have hcard : 0 < (fixedSizeEvent n s).card := by
    rw [fixedSizeEvent_card]
    exact Nat.choose_pos hs
  exact Finset.card_pos.mp hcard

/-- The uniform law is a genuine probability measure in the allowed size range. -/
theorem fixedSizeMeasure_isProbability {n s : ℕ} (hs : s ≤ n) :
    IsProbabilityMeasure (fixedSizeMeasure n s) := by
  unfold fixedSizeMeasure fixedSizeEventSet
  apply ProbabilityTheory.isProbabilityMeasure_uniformOn
  · exact (fixedSizeEvent n s).finite_toSet
  · rcases fixedSizeEvent_nonempty hs with ⟨ξ, hξ⟩
    exact ⟨ξ, hξ⟩

/-- Singleton masses of the uniform prescribed-size law. -/
theorem fixedSizeMeasure_singleton {n s : ℕ} (_hs : s ≤ n) (ξ : Bit n) :
    (fixedSizeMeasure n s).real {ξ} =
      if ξ ∈ fixedSizeEvent n s then (n.choose s : ℝ)⁻¹ else 0 := by
  classical
  unfold fixedSizeMeasure fixedSizeEventSet
  rw [measureReal_def, ← Finset.coe_singleton, ProbabilityTheory.uniformOn_apply_finset]
  by_cases hξ : ξ ∈ fixedSizeEvent n s
  · simp [hξ, fixedSizeEvent_card]
  · simp [hξ]

/-- The finite average and the actual measure integral are identical. -/
theorem fixedSizeExpectation_eq_average {n s : ℕ} (hs : s ≤ n)
    (f : Bit n → ℝ) :
    fixedSizeExpectation n s f = fixedSizeAverage n s f := by
  classical
  let : IsProbabilityMeasure (fixedSizeMeasure n s) :=
    fixedSizeMeasure_isProbability hs
  rw [fixedSizeExpectation, integral_fintype (Integrable.of_finite)]
  simp_rw [fixedSizeMeasure_singleton hs, smul_eq_mul]
  calc
    (∑ x, (if x ∈ fixedSizeEvent n s then (n.choose s : ℝ)⁻¹ else 0) * f x) =
        (n.choose s : ℝ)⁻¹ * ∑ x, if x ∈ fixedSizeEvent n s then f x else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          split_ifs <;> ring
    _ = (n.choose s : ℝ)⁻¹ * ∑ x ∈ fixedSizeEvent n s, f x := by
          rw [Finset.sum_ite_mem_eq]
    _ = fixedSizeAverage n s f := by rfl

/-- The independent Bernoulli product measure has the real atom formula. -/
theorem bitProductMeasure_singleton_real {n : ℕ} (q : SuccessProbability) (ξ : Bit n) :
    (bitProductMeasure n q).real {ξ} =
      ∏ i, if ξ i = true then (q : ℝ) else 1 - (q : ℝ) := by
  classical
  rw [measureReal_def, bitProductMeasure, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  change (bernoulliMeasure true false (closedProbability q)).real {ξ i} = _
  cases h : ξ i <;>
    simp [closedProbability]

/-- Every atom on the prescribed-size event has the same real mass. -/
theorem bitProductMeasure_singleton_of_mem {n s : ℕ} (q : SuccessProbability)
    {ξ : Bit n} (hξ : ξ ∈ fixedSizeEvent n s) :
    (bitProductMeasure n q).real {ξ} =
      (q : ℝ) ^ s * (1 - (q : ℝ)) ^ (n - s) := by
  classical
  have hc : bitCount ξ = s := (Finset.mem_filter.mp hξ).2
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => ξ i = true)
  have hnot : (Finset.univ.filter (fun i => ¬ξ i = true)).card = n - s := by
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    change bitCount ξ + _ = n at hcard
    omega
  rw [bitProductMeasure_singleton_real, Finset.prod_ite]
  simp only [Finset.prod_const]
  change (q : ℝ) ^ bitCount ξ * _ = _
  rw [hc, hnot]

/-- Exact probability of the conditioning event. -/
theorem bitProductMeasure_event_real {n s : ℕ} (q : SuccessProbability) (_hs : s ≤ n) :
    (bitProductMeasure n q).real (fixedSizeEventSet n s) =
      (n.choose s : ℝ) * (q : ℝ) ^ s * (1 - (q : ℝ)) ^ (n - s) := by
  classical
  unfold fixedSizeEventSet
  rw [← MeasureTheory.sum_measureReal_singleton]
  calc
    _ = ∑ ξ ∈ fixedSizeEvent n s,
          (q : ℝ) ^ s * (1 - (q : ℝ)) ^ (n - s) := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      exact bitProductMeasure_singleton_of_mem q hξ
    _ = _ := by simp [fixedSizeEvent_card, mul_assoc]

/-- The conditioning event has strictly positive probability, including sizes zero and n. -/
theorem conditioning_event_pos {n s : ℕ} (q : SuccessProbability) (hs : s ≤ n) :
    0 < (bitProductMeasure n q).real (fixedSizeEventSet n s) := by
  rw [bitProductMeasure_event_real q hs]
  have hc : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hs
  exact mul_pos (mul_pos hc (pow_pos q.property.1 _))
    (pow_pos (sub_pos.mpr q.property.2) _)

/-- Conditioning independent Bernoulli(q) bits on their size gives the uniform law. -/
theorem conditional_bernoulli_uniform {n s : ℕ} (q : SuccessProbability) (hs : s ≤ n) :
    ProbabilityTheory.cond (bitProductMeasure n q) (fixedSizeEventSet n s) =
      fixedSizeMeasure n s := by
  classical
  let : IsProbabilityMeasure (fixedSizeMeasure n s) := fixedSizeMeasure_isProbability hs
  apply Measure.ext_of_measureReal_singleton
  intro ξ
  rw [measureReal_def, ProbabilityTheory.cond_apply' (measurableSet_singleton ξ),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((bitProductMeasure n q).real (fixedSizeEventSet n s))⁻¹ *
    (bitProductMeasure n q).real (fixedSizeEventSet n s ∩ {ξ}) = _
  rw [fixedSizeMeasure_singleton hs, bitProductMeasure_event_real q hs]
  by_cases hξ : ξ ∈ fixedSizeEvent n s
  · have hinter : fixedSizeEventSet n s ∩ {ξ} = {ξ} := by
      exact Set.inter_singleton_of_mem hξ
    rw [hinter, bitProductMeasure_singleton_of_mem q hξ, if_pos hξ]
    have hc : (n.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
    have hq : (q : ℝ) ≠ 0 := q.property.1.ne'
    have hq' : 1 - (q : ℝ) ≠ 0 := (sub_pos.mpr q.property.2).ne'
    field_simp
  · have hinter : fixedSizeEventSet n s ∩ {ξ} = ∅ :=
      Set.inter_singleton_of_notMem hξ
    simp [hinter, hξ]

/-- Explicit integral bridge from the conditioned bit law to the finite average. -/
theorem conditional_expectation_eq_average {n s : ℕ} (q : SuccessProbability)
    (hs : s ≤ n) (f : Bit n → ℝ) :
    (∫ ξ, f ξ ∂ProbabilityTheory.cond (bitProductMeasure n q) (fixedSizeEventSet n s)) =
      fixedSizeAverage n s f := by
  rw [conditional_bernoulli_uniform q hs]
  exact fixedSizeExpectation_eq_average hs f

/-- Conditional expectation under the product law is bounded by the
unconditioned expectation after multiplying by the conditioning atom.  The
proof is a direct finite-sum comparison; the preceding theorem identifies the
left-hand finite law with the actual conditional measure. -/
theorem conditional_expectation_mul_le {n s : ℕ} (q : SuccessProbability) (hs : s ≤ n)
    (f : Bit n → ℝ) (hf : ∀ ξ, 0 ≤ f ξ) :
    (bitProductMeasure n q).real (fixedSizeEventSet n s) *
        fixedSizeExpectation n s f ≤
      ∫ ξ, f ξ ∂bitProductMeasure n q := by
  classical
  let : IsProbabilityMeasure (bitProductMeasure n q) := by
    unfold bitProductMeasure
    infer_instance
  have hfinite : Integrable f (bitProductMeasure n q) := Integrable.of_finite
  rw [bitProductMeasure_event_real q hs, fixedSizeExpectation_eq_average hs,
    integral_fintype hfinite]
  simp only [smul_eq_mul]
  let w : ℝ := (q : ℝ) ^ s * (1 - (q : ℝ)) ^ (n - s)
  have hchoose : 0 < (n.choose s : ℝ) := by
    exact_mod_cast Nat.choose_pos hs
  have hterm (ξ : Bit n) :
      (if ξ ∈ fixedSizeEvent n s then w * f ξ else 0) ≤
        (bitProductMeasure n q).real {ξ} * f ξ := by
    by_cases hξ : ξ ∈ fixedSizeEvent n s
    · have hatom : (bitProductMeasure n q).real {ξ} = w := by
        exact bitProductMeasure_singleton_of_mem q hξ
      simp [hξ, hatom]
    · simp [hξ]
      exact mul_nonneg ENNReal.toReal_nonneg (hf ξ)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ξ _ => hterm ξ)
  rw [mul_assoc (n.choose s : ℝ)]
  calc
    (n.choose s : ℝ) * w *
        ((n.choose s : ℝ)⁻¹ * ∑ ξ ∈ fixedSizeEvent n s, f ξ) =
        w * ∑ ξ ∈ fixedSizeEvent n s, f ξ := by
          field_simp [hchoose.ne']
    _ = ∑ ξ, if ξ ∈ fixedSizeEvent n s then w * f ξ else 0 := by
          rw [Finset.sum_ite_mem_eq, Finset.mul_sum]
    _ ≤ ∑ ξ, (bitProductMeasure n q).real {ξ} * f ξ := hsum

/-- Exact inclusion probability under the uniform prescribed-size law. -/
theorem fixedSize_inclusion_probability {n s : ℕ} (hs0 : 0 < s) (hsn : s ≤ n)
    (i : Fin n) :
    fixedSizeExpectation n s (fun ξ => if ξ i = true then 1 else 0) =
      (s : ℝ) / n := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hs0 hsn
  have hcard : (fixedSizeEvent n s).card = n.choose s := fixedSizeEvent_card n s
  have hmap :
      ((fixedSizeEvent n s).filter (fun ξ => ξ i = true)).image (bitFinsetEquiv n) =
        ((Finset.univ : Finset (Fin n)).powersetCard s).filter (fun S => i ∈ S) := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_image.mp hS with ⟨ξ, hξ, rfl⟩
      have hξE := (Finset.mem_filter.mp hξ).1
      have hξi := (Finset.mem_filter.mp hξ).2
      have hcardξ := (Finset.mem_filter.mp hξE).2
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcardξ⟩
      · simpa [bitFinsetEquiv, bitSet] using hξi
    · intro hS
      have hS' := Finset.mem_filter.mp hS
      let ξ : Bit n := (bitFinsetEquiv n).symm S
      have hξE : ξ ∈ fixedSizeEvent n s := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · change ((bitFinsetEquiv n) ((bitFinsetEquiv n).symm S)).card = s
          rw [(bitFinsetEquiv n).apply_symm_apply]
          exact (Finset.mem_powersetCard.mp hS'.1).2
      refine Finset.mem_image.mpr ⟨ξ, Finset.mem_filter.mpr ⟨hξE, ?_⟩, ?_⟩
      · simp [ξ, bitFinsetEquiv, hS'.2]
      · exact (bitFinsetEquiv n).apply_symm_apply S
  have hcontains :
      ((fixedSizeEvent n s).filter (fun ξ => ξ i = true)).card = (n - 1).choose (s - 1) := by
    rw [← Finset.card_image_of_injective _ (bitFinsetEquiv n).injective, hmap]
    simpa using
      (Finset.card_filter_powersetCard_subset ({i} : Finset (Fin n)) Finset.univ s
        (by simp) (by simpa only [Finset.card_singleton] using Nat.succ_le_iff.mpr hs0))
  rw [fixedSizeExpectation_eq_average hsn]
  simp only [fixedSizeAverage]
  have hsum :
      ∑ ξ ∈ fixedSizeEvent n s, (if ξ i = true then (1 : ℝ) else 0) =
        ((fixedSizeEvent n s).filter (fun ξ => ξ i = true)).card := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum, hcontains]
  have hn : 0 < n := lt_of_lt_of_le hs0 hsn
  have hchoose : 0 < (n.choose s : ℝ) := by
    exact_mod_cast Nat.choose_pos hsn
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpred : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
  have hspred : (s - 1 : ℕ) + 1 = s := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hs0)
  have hchoose_id := Nat.add_one_mul_choose_eq (n - 1) (s - 1)
  have hchoose_id' : (n : ℝ) * (n - 1).choose (s - 1) =
      (n.choose s : ℝ) * s := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) hchoose_id
    simpa [hpred, hspred, Nat.cast_mul, Nat.cast_add] using h
  field_simp [hchoose.ne', hnreal]
  nlinarith [hchoose_id']

/-- Exact expectation of the signed linear statistic. -/
theorem fixedSize_mean {n s : ℕ} (hs0 : 0 < s) (hsn : s ≤ n)
    (a : Fin n → ℝ) :
    fixedSizeExpectation n s (bitLinear a) = (s : ℝ) / n * ∑ i, a i := by
  classical
  rw [fixedSizeExpectation_eq_average hsn]
  unfold fixedSizeAverage bitLinear
  have hinc (i : Fin n) :
      (n.choose s : ℝ)⁻¹ *
          ∑ ξ ∈ fixedSizeEvent n s, (if ξ i = true then (1 : ℝ) else 0) =
        (s : ℝ) / n := by
    have hh := fixedSize_inclusion_probability hs0 hsn i
    rw [fixedSizeExpectation_eq_average hsn] at hh
    simpa [fixedSizeAverage] using hh
  calc
    (n.choose s : ℝ)⁻¹ *
        ∑ ξ ∈ fixedSizeEvent n s, ∑ i, (if ξ i = true then a i else 0) =
        ∑ i, ((n.choose s : ℝ)⁻¹ *
          ∑ ξ ∈ fixedSizeEvent n s, (if ξ i = true then (1 : ℝ) else 0)) * a i := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro ξ hξ
      by_cases h : ξ i = true <;> simp [h]
    _ = ∑ i, ((s : ℝ) / n) * a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hinc]
    _ = (s : ℝ) / n * ∑ i, a i := by
      rw [Finset.mul_sum]

/-- The mean identity also covers the empty subset, including an empty ambient set. -/
theorem fixedSize_mean_all {n s : ℕ} (hsn : s ≤ n) (a : Fin n → ℝ) :
    fixedSizeExpectation n s (bitLinear a) = (s : ℝ) / n * ∑ i, a i := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · rw [fixedSizeExpectation_eq_average hsn]
    have hzero : ∀ ξ ∈ fixedSizeEvent n 0, bitLinear a ξ = 0 := by
      intro ξ hξ
      have hc : (bitSet ξ).card = 0 := (Finset.mem_filter.mp hξ).2
      have he : bitSet ξ = ∅ := Finset.card_eq_zero.mp hc
      unfold bitLinear
      apply Finset.sum_eq_zero
      intro i hi
      have hnot : ξ i ≠ true := by
        intro h
        have hm : i ∈ bitSet ξ := by simp [bitSet, h]
        rw [he] at hm
        exact Finset.notMem_empty i hm
      simp [hnot]
    simp only [fixedSizeAverage, Nat.cast_zero, zero_div, zero_mul]
    rw [Finset.sum_eq_zero hzero, mul_zero]
  · exact fixedSize_mean hs0 hsn a

/-- Product-formula MGF for the independent Bernoulli bits. -/
theorem bitProduct_mgf (n : ℕ) (q : SuccessProbability) (a : Fin n → ℝ) :
    (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) =
      ∏ i, ((q : ℝ) * Real.exp (a i) + (1 - (q : ℝ))) := by
  classical
  unfold bitProductMeasure bitLinear
  rw [show (fun ξ : Bit n => Real.exp (∑ i, if ξ i = true then a i else 0)) =
      (fun ξ => ∏ i, if ξ i = true then Real.exp (a i) else 1) by
        funext ξ
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases h : ξ i = true <;> simp [h]]
  rw [integral_fintype_prod_eq_prod (fun (i : Fin n) (b : Bool) =>
    if b = true then Real.exp (a i) else 1)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  simp [closedProbability]

/-- A signed small-weight upper bound for the independent MGF. -/
theorem bitProduct_mgf_bound {n : ℕ} (q : SuccessProbability) (a : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ 1) :
    (∫ ξ, Real.exp (bitLinear a ξ) ∂bitProductMeasure n q) ≤
      Real.exp ((q : ℝ) * ∑ i, a i + (q : ℝ) * ∑ i, (a i) ^ 2) := by
  classical
  rw [bitProduct_mgf]
  have hfac (i : Fin n) :
      0 ≤ 1 + (q : ℝ) * (Real.exp (a i) - 1) := by
    have hq := q.property.1.le
    have hq' := q.property.2.le
    have he : 0 < Real.exp (a i) := Real.exp_pos _
    nlinarith [mul_nonneg hq he.le]
  have hterm (i : Fin n) :
      1 + (q : ℝ) * (Real.exp (a i) - 1) ≤
        Real.exp ((q : ℝ) * (a i + (a i) ^ 2)) := by
    have hq : 0 ≤ (q : ℝ) := q.property.1.le
    have ht := Real.abs_exp_sub_one_sub_id_le (ha i)
    have ht' : Real.exp (a i) - 1 ≤ a i + (a i) ^ 2 := by
      have := le_abs_self (Real.exp (a i) - 1 - a i)
      linarith
    calc
      1 + (q : ℝ) * (Real.exp (a i) - 1) ≤
          Real.exp ((q : ℝ) * (Real.exp (a i) - 1)) := by
            convert Real.add_one_le_exp ((q : ℝ) * (Real.exp (a i) - 1)) using 1
            ring
      _ ≤ Real.exp ((q : ℝ) * (a i + (a i) ^ 2)) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left ht' hq
  calc
    ∏ i, ((q : ℝ) * Real.exp (a i) + (1 - (q : ℝ))) =
        ∏ i, (1 + (q : ℝ) * (Real.exp (a i) - 1)) := by
          apply Finset.prod_congr rfl
          intro i hi
          ring
    _ ≤ ∏ i, Real.exp ((q : ℝ) * (a i + (a i) ^ 2)) := by
          apply Finset.prod_le_prod
          · intro i hi
            exact hfac i
          · intro i hi
            exact hterm i
    _ = Real.exp ((q : ℝ) * ∑ i, a i + (q : ℝ) * ∑ i, (a i) ^ 2) := by
          rw [← Real.exp_sum]
          congr 1
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

end MajorityDynamics.Probability.FixedSizeExponential

