import MajorityDynamics.Literature.DegreeEnumeration.BinomialAtoms
import Mathlib.Probability.Independence.Basic

/-! Both conditioned-binomial atom formulas and their normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Literature.DegreeEnumeration
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

instance : IsProbabilityMeasure (bipartiteIndependentLaw L R) := by
  unfold bipartiteIndependentLaw
  infer_instance

theorem independentBinomials_coordinates (k : ℕ) :
    iIndepFun (fun i (a : V → ℕ) => a i) (independentBinomials V k) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem independentBinomials_coordinate_law (k : ℕ) (i : V) :
    (independentBinomials V k).map (fun a => a i) = binomial k halfProbability := by
  exact (measurePreserving_eval (fun _ : V => binomial k halfProbability) i).map_eq

theorem bipartiteIndependentLaw_independent :
    IndepFun Prod.fst Prod.snd (bipartiteIndependentLaw L R) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem bipartiteIndependentLaw_atom (a : L → ℕ) (b : R → ℕ) :
    (bipartiteIndependentLaw L R).real {(a, b)} =
      (independentBinomials L (Fintype.card R)).real {a} *
      (independentBinomials R (Fintype.card L)).real {b} := by
  rw [measureReal_def, ← Set.singleton_prod_singleton, bipartiteIndependentLaw,
    Measure.prod_prod, ENNReal.toReal_mul]
  rfl

theorem bipartiteIndependentLaw_totals (m : ℕ) :
    (bipartiteIndependentLaw L R).real {d | (∑ i, d.1 i) = m ∧ (∑ j, d.2 j) = m} =
      (independentBinomials L (Fintype.card R)).real {a | ∑ i, a i = m} *
      (independentBinomials R (Fintype.card L)).real {b | ∑ j, b j = m} := by
  change (((independentBinomials L (Fintype.card R)).prod
    (independentBinomials R (Fintype.card L)))
      ({a | ∑ i, a i = m} ×ˢ {b | ∑ j, b j = m})).toReal = _
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rfl

theorem bipartiteIndependentLaw_totals_pos (m : ℕ)
    (hm : m ≤ Fintype.card L * Fintype.card R) :
    0 < (bipartiteIndependentLaw L R).real
      {d | (∑ i, d.1 i) = m ∧ (∑ j, d.2 j) = m} := by
  rw [bipartiteIndependentLaw_totals]
  exact mul_pos (independentBinomials_total_pos _ _ hm)
    (independentBinomials_total_pos _ _ (by simpa [Nat.mul_comm] using hm))

theorem graphBinomialLaw_normalized (m : ℕ)
    (hm : 2 * m ≤ Fintype.card V * (Fintype.card V - 1)) :
    IsProbabilityMeasure (graphBinomialLaw V m) := by
  apply cond_isProbabilityMeasure
  have h := independentBinomials_total_pos (V := V) _ _ hm
  exact ENNReal.toReal_pos_iff.mp h |>.1.ne'

theorem bipartiteBinomialLaw_normalized (m : ℕ)
    (hm : m ≤ Fintype.card L * Fintype.card R) :
    IsProbabilityMeasure (bipartiteBinomialLaw L R m) := by
  apply cond_isProbabilityMeasure
  have h := bipartiteIndependentLaw_totals_pos m hm
  exact ENNReal.toReal_pos_iff.mp h |>.1.ne'

theorem bipartiteBinomialLaw_atom (m : ℕ) (a : L → ℕ) (b : R → ℕ)
    (hm : m ≤ Fintype.card L * Fintype.card R)
    (ha : ∑ i, a i = m) (hb : ∑ j, b j = m) :
    (bipartiteBinomialLaw L R m).real {(a, b)} =
      (∏ i, ((Fintype.card R).choose (a i) : ℝ)) *
        (∏ j, ((Fintype.card L).choose (b j) : ℝ)) /
          (((Fintype.card L * Fintype.card R).choose m : ℝ) ^ 2) := by
  have hmem : (a, b) ∈ {d : (L → ℕ) × (R → ℕ) |
      (∑ i, d.1 i) = m ∧ (∑ j, d.2 j) = m} := ⟨ha, hb⟩
  rw [measureReal_def, bipartiteBinomialLaw, cond_apply' (measurableSet_singleton _),
    Set.inter_singleton_of_mem hmem, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((bipartiteIndependentLaw L R).real
    {d | (∑ i, d.1 i) = m ∧ (∑ j, d.2 j) = m})⁻¹ *
    (bipartiteIndependentLaw L R).real {(a, b)} = _
  rw [bipartiteIndependentLaw_totals, bipartiteIndependentLaw_atom]
  simp_rw [independentBinomials_total, independentBinomials_atom]
  rw [Nat.mul_comm (Fintype.card R) (Fintype.card L)]
  have hp : (2 : ℝ) ^ (Fintype.card L * Fintype.card R) ≠ 0 := by positivity
  have hc : (((Fintype.card L * Fintype.card R).choose m) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hm).ne'
  field_simp

end MajorityDynamics.Literature.DegreeEnumeration
