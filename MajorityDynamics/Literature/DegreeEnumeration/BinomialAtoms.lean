import MajorityDynamics.Literature.DegreeEnumeration.FixedEdges

/-! Counting the independent-binomial conditioning event through labeled row subsets. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V W : Type*} [Fintype V] [Fintype W]

def rowSet (E : Set (V × W)) (i : V) : Set W := {j | (i, j) ∈ E}

omit [Fintype V] in
theorem rowSet_ncard (E : Set (V × W)) (i : V) :
    (rowSet E i).ncard = leftDegree E i := by
  rw [Set.ncard_eq_toFinset_card']
  unfold leftDegree leftNeighbors
  congr 1
  ext j
  simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

def rowFiberEquiv (a : V → ℕ) :
    {E : Set (V × W) // ∀ i, leftDegree E i = a i} ≃
      ((i : V) → {s : Set W // s.ncard = a i}) where
  toFun E i := ⟨rowSet E i, by rw [rowSet_ncard]; exact E.2 i⟩
  invFun f := ⟨{e | e.2 ∈ (f e.1).1}, fun i => by
    rw [← rowSet_ncard]
    exact (f i).2⟩
  left_inv E := by
    apply Subtype.ext
    rfl
  right_inv f := by
    funext i
    apply Subtype.ext
    rfl

theorem subset_ncard_count (k : ℕ) :
    ({s : Set W | s.ncard = k} : Set (Set W)).ncard = (Fintype.card W).choose k := by
  simpa using Set.ncard_powerset_ncard (Set.toFinite (Set.univ : Set W)) k

theorem rowFiber_card (a : V → ℕ) :
    ({E : Set (V × W) | ∀ i, leftDegree E i = a i}).ncard =
      ∏ i, (Fintype.card W).choose (a i) := by
  change Nat.card {E : Set (V × W) // ∀ i, leftDegree E i = a i} = _
  rw [Nat.card_congr (rowFiberEquiv a), Nat.card_eq_fintype_card, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Nat.card_eq_fintype_card]
  exact subset_ncard_count (a i)

theorem binomial_half_atom (k d : ℕ) :
    (binomial k halfProbability).real {d} = (k.choose d : ℝ) / 2 ^ k := by
  rw [binomial_real_singleton]
  norm_num only [halfProbability, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  by_cases hd : d ≤ k
  · rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hd, div_pow]
    simp [div_eq_mul_inv]
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hd)]

theorem independentBinomials_atom (k : ℕ) (a : V → ℕ) :
    (independentBinomials V k).real {a} =
      (∏ i, (k.choose (a i) : ℝ)) / 2 ^ (Fintype.card V * k) := by
  rw [measureReal_def, independentBinomials, Measure.pi_singleton, ENNReal.toReal_prod]
  change (∏ i, (binomial k halfProbability).real {a i}) = _
  simp_rw [binomial_half_atom]
  rw [Finset.prod_div_distrib]
  simp [← pow_mul, Nat.mul_comm]

theorem independentBinomials_eq_row_law (k : ℕ) :
    independentBinomials V k =
      (uniformOn (Set.univ : Set (Set (V × Fin k)))).map
        (fun E => leftDegree E) := by
  apply Measure.ext_of_measureReal_singleton
  intro a
  rw [independentBinomials_atom, measureReal_def,
    Measure.map_apply .of_discrete (measurableSet_singleton _), uniform_apply]
  simp only [Set.univ_inter, ENNReal.toReal_div, ENNReal.toReal_natCast]
  have he : (fun E : Set (V × Fin k) => leftDegree E) ⁻¹' {a} =
      {E | ∀ i, leftDegree E i = a i} := by
    ext E
    simp [funext_iff]
  rw [he, rowFiber_card]
  simp

theorem independentBinomials_total (k m : ℕ) :
    (independentBinomials V k).real {a | ∑ i, a i = m} =
      ((Fintype.card V * k).choose m : ℝ) / 2 ^ (Fintype.card V * k) := by
  rw [independentBinomials_eq_row_law, measureReal_def,
    Measure.map_apply .of_discrete (by measurability), uniform_apply]
  simp only [Set.univ_inter, ENNReal.toReal_div, ENNReal.toReal_natCast]
  have he : (fun E : Set (V × Fin k) => leftDegree E) ⁻¹' {a | ∑ i, a i = m} =
      crossEdgeFamily V (Fin k) m := by
    ext E
    simp [crossEdgeFamily, sum_leftDegree]
  rw [he, crossEdgeFamily_card]
  simp

theorem independentBinomials_total_pos (k m : ℕ) (hm : m ≤ Fintype.card V * k) :
    0 < (independentBinomials V k).real {a | ∑ i, a i = m} := by
  rw [independentBinomials_total]
  exact div_pos (by exact_mod_cast Nat.choose_pos hm) (by positivity)

theorem conditional_binomial_atom (k m : ℕ) (a : V → ℕ)
    (hm : m ≤ Fintype.card V * k) (ha : ∑ i, a i = m) :
    (cond (independentBinomials V k) {d | ∑ i, d i = m}).real {a} =
      (∏ i, (k.choose (a i) : ℝ)) / ((Fintype.card V * k).choose m : ℝ) := by
  rw [measureReal_def, cond_apply' (measurableSet_singleton _),
    Set.inter_singleton_of_mem (show a ∈ {d | ∑ i, d i = m} from ha), ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((independentBinomials V k).real {d | ∑ i, d i = m})⁻¹ *
    (independentBinomials V k).real {a} = _
  rw [independentBinomials_total, independentBinomials_atom]
  have hp : (2 : ℝ) ^ (Fintype.card V * k) ≠ 0 := by positivity
  have hc : (((Fintype.card V * k).choose m) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hm).ne'
  field_simp

theorem graphBinomialLaw_atom (m : ℕ) (d : V → ℕ)
    (hm : 2 * m ≤ Fintype.card V * (Fintype.card V - 1))
    (hd : ∑ i, d i = 2 * m) :
    (graphBinomialLaw V m).real {d} =
      (∏ i, ((Fintype.card V - 1).choose (d i) : ℝ)) /
        ((Fintype.card V * (Fintype.card V - 1)).choose (2 * m) : ℝ) :=
  conditional_binomial_atom _ _ d hm hd

end MajorityDynamics.Literature.DegreeEnumeration
