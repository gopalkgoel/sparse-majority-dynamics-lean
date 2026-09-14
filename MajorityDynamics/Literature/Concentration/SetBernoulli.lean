import Mathlib.Probability.Distributions.Binomial

/-!
# Restricting a Bernoulli product and counting its selected elements

These probability-law bridges support CKLT21, Lemma 2.1(ii),
https://arxiv.org/abs/2105.12709v1 . They use Mathlib's actual `setBernoulli`
product measure: intersecting the sampled set with a fixed subfamily applies
logical conjunction coordinate by coordinate. Mathlib's proved product-map and
binomial singleton formulas then identify the exact count distribution.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal

namespace MajorityDynamics.Literature.Concentration

/-- Intersecting a Bernoulli random subset with a fixed set restricts its product law. -/
lemma map_inter_setBernoulli {ι : Type*} [Fintype ι] (u s : Set ι) (p : unitInterval) :
    (setBernoulli u p).map (fun selected => s ∩ selected) =
      setBernoulli (s ∩ u) p := by
  rw [setBernoulli_eq_map, Measure.map_map (.of_discrete) (by fun_prop)]
  rw [setBernoulli_eq_map]
  change (Measure.infinitePi _).map
      ((fun x : ι → Prop => {i | x i}) ∘ (fun x i => i ∈ s ∧ x i)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_pi (f := fun i (x : Prop) => i ∈ s ∧ x) _ (fun i => .of_discrete)]
  congr 1
  congr 1
  funext i
  rw [Measure.map_add, Measure.map_smul, Measure.map_smul]
  · simp [Measure.map_dirac, Set.mem_inter_iff]
  · exact .of_discrete

/-- The cardinality of a finite Bernoulli random subset has the binomial law. -/
lemma map_ncard_setBernoulli_eq_binomial {ι : Type*} [Fintype ι]
    (s : Set ι) (p : unitInterval) :
    (setBernoulli s p).map Set.ncard = binomial s.ncard p := by
  apply Measure.ext_of_singleton
  intro k
  rw [map_ncard_setBernoulli_singleton (Set.toFinite s), binomial_singleton]

/-- Selecting outside a fixed subfamily does not alter the law of its selected count. -/
lemma map_inter_ncard_setBernoulli {ι : Type*} [Fintype ι]
    (u s : Set ι) (p : unitInterval) (hsu : s ⊆ u) :
    (setBernoulli u p).map (fun selected => (s ∩ selected).ncard) =
      binomial s.ncard p := by
  change (setBernoulli u p).map (Set.ncard ∘ (fun selected => s ∩ selected)) = _
  rw [← Measure.map_map (.of_discrete) (.of_discrete), map_inter_setBernoulli,
    Set.inter_eq_left.mpr hsu, map_ncard_setBernoulli_eq_binomial]

/-- Exact transport of a count event to the scalar binomial distribution. -/
lemma setBernoulli_inter_ncard_apply {ι : Type*} [Fintype ι]
    (u s : Set ι) (p : unitInterval) (hsu : s ⊆ u) (event : Set ℕ) :
    setBernoulli u p {selected | (s ∩ selected).ncard ∈ event} =
      binomial s.ncard p event := by
  rw [← map_inter_ncard_setBernoulli u s p hsu,
    Measure.map_apply (.of_discrete) (.of_discrete)]
  rfl

end MajorityDynamics.Literature.Concentration
