import MajorityDynamics.Probability.UnconditionedExactTotals.Basic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.UnconditionedExactTotals

open Classical
variable {ι : Type*} [Fintype ι]

@[fun_prop] theorem measurable_count : Measurable (@count ι _) := by
  classical
  exact .of_discrete

theorem count_eq_sum (x : ι → Bool) : count x = ∑ i, if x i = true then 1 else 0 := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]

def bitsFinsetEquiv : (ι → Bool) ≃ Finset ι where
  toFun := fun x => Finset.univ.filter (fun i => x i = true)
  invFun := fun s i => if i ∈ s then true else false
  left_inv := by intro x; funext i; cases h : x i <;> simp [h]
  right_inv := by intro s; ext i; simp

def countFiberEquiv (k : ℕ) :
    {x : ι → Bool // count x = k} ≃ {s : Finset ι // s.card = k} where
  toFun := fun x => ⟨bitsFinsetEquiv x.1, x.2⟩
  invFun := fun s => ⟨bitsFinsetEquiv.symm s.1, by
    change (bitsFinsetEquiv (bitsFinsetEquiv.symm s.1)).card = k
    simpa using s.2⟩
  left_inv := by intro x; apply Subtype.ext; exact bitsFinsetEquiv.symm_apply_apply x.1
  right_inv := by intro s; apply Subtype.ext; exact bitsFinsetEquiv.apply_symm_apply s.1

theorem countFiber_card (k : ℕ) :
    (Finset.univ.filter (fun x : ι → Bool => count x = k)).card = (Fintype.card ι).choose k := by
  classical
  calc
    _ = Fintype.card {x : ι → Bool // count x = k} := by
      symm
      apply Fintype.card_of_subtype
      intro x
      simp
    _ = Fintype.card {s : Finset ι // s.card = k} := Fintype.card_congr (countFiberEquiv k)
    _ = _ := Fintype.card_finset_len k

theorem bitsLaw_atom (q : unitInterval) (x : ι → Bool) :
    (bitsLaw ι q).real {x} = (q : ℝ) ^ count x * (1 - (q : ℝ)) ^ (Fintype.card ι - count x) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun i => x i = true)
  have hn : (Finset.univ.filter (fun i => ¬x i = true)).card = Fintype.card ι - count x := by
    simp only [Finset.card_univ] at hc
    change count x + _ = _ at hc
    omega
  rw [measureReal_def, bitsLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  have hatom (i : ι) : (bernoulliMeasure true false q).real {x i} =
      if x i = true then (q : ℝ) else 1 - (q : ℝ) := by cases x i <;> simp
  simp_rw [← measureReal_def, hatom]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  change (q : ℝ) ^ count x * _ = _
  rw [hn]

/-- Counting independent bits gives the actual Mathlib binomial measure. -/
theorem count_law (q : unitInterval) : (bitsLaw ι q).map count = binomial (Fintype.card ι) q := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton k), binomial_real_singleton]
  have he : count ⁻¹' ({k} : Set ℕ) =
      (Finset.univ.filter (fun x : ι → Bool => count x = k) : Set (ι → Bool)) := by ext x; simp
  rw [he, ← sum_measureReal_singleton]
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : ι → Bool => count x = k),
        (q : ℝ) ^ k * (1 - (q : ℝ)) ^ (Fintype.card ι - k) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [bitsLaw_atom, (Finset.mem_filter.mp hx).2]
    _ = _ := by simp [countFiber_card, mul_assoc]

end MajorityDynamics.Probability.UnconditionedExactTotals
