import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent Bernoulli sites: block counts are independent binomials

Both random graph laws of Lemma A.10 are pushforwards of a product of Bernoulli
measures indexed by the potential edges ("sites"). This module works with that
product directly:

* `siteLaw u p` is the product over all sites `i` of `Ber(i ∈ u, False, p)` on
  `ι → Prop`; Mathlib's `setBer(u, p)` is its pushforward under `setOf`, and
  `SimpleGraph.binomialRandom` is in turn the pushforward under `fromEdgeSet`.
* `blockCount A ω` counts the present sites in a finite block `A`.
* `siteLaw_map_blockCount`: a block inside `u` has `binomial |A| p` count.
* `blockCount_iIndepFun`: counts of pairwise disjoint blocks are independent.
  This is proved by regrouping the coordinates along the fibers of the block
  map (`iIndepFun_fiberRestrict`), which is the only place where independence
  is asserted; it is exactly the "disjoint edge sets" argument of the manuscript.
-/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.DegreeConcentration

/-! ### Two generic independence lemmas -/

/-- Independence of `F` under the pushforward `μ.map Φ` gives independence of the
compositions `F j ∘ Φ` under `μ`. -/
theorem iIndepFun_comp_of_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {J : Type*} {β : J → Type*} [∀ j, MeasurableSpace (β j)]
    (μ : Measure Ω) (Φ : Ω → Ω') (hΦ : Measurable Φ) (F : ∀ j, Ω' → β j)
    (hF : ∀ j, Measurable (F j)) (h : iIndepFun F (μ.map Φ)) :
    iIndepFun (fun j ω ↦ F j (Φ ω)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have hmeas : ∀ j ∈ S, MeasurableSet (F j ⁻¹' sets j) := fun j hj ↦ hF j (hsets j hj)
  have h1 : (⋂ j ∈ S, (fun ω ↦ F j (Φ ω)) ⁻¹' sets j) = Φ ⁻¹' (⋂ j ∈ S, F j ⁻¹' sets j) := by
    ext ω; simp
  rw [h1, ← Measure.map_apply hΦ (S.measurableSet_biInter hmeas), h S hsets]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Measure.map_apply hΦ (hmeas j hj)]
  rfl

/-- Block independence in a product measure: the restrictions of a product-distributed
configuration to the fibers of any map `g` are mutually independent. -/
theorem iIndepFun_fiberRestrict {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {J : Type*} (g : ι → J) :
    iIndepFun (fun (j : J) (ω : ∀ i, X i) (i : {i // g i = j}) ↦ ω i.1) (infinitePi μ) := by
  have hlaw : (infinitePi μ).map
      ((MeasurableEquiv.piCurry (fun j (i : {i // g i = j}) ↦ X (Equiv.sigmaFiberEquiv g ⟨j, i⟩))) ∘
        (MeasurableEquiv.piCongrLeft X (Equiv.sigmaFiberEquiv g)).symm) =
      infinitePi fun j ↦ infinitePi fun i : {i // g i = j} ↦ μ (Equiv.sigmaFiberEquiv g ⟨j, i⟩) := by
    rw [← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
    have h1 : (infinitePi μ).map (MeasurableEquiv.piCongrLeft X (Equiv.sigmaFiberEquiv g)).symm =
        infinitePi fun s ↦ μ (Equiv.sigmaFiberEquiv g s) := by
      rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, MeasurableEquiv.symm_symm]
      exact (infinitePi_map_piCongrLeft μ (Equiv.sigmaFiberEquiv g)).symm
    rw [h1]
    exact infinitePi_map_piCurry (fun j (i : {i // g i = j}) ↦ μ (Equiv.sigmaFiberEquiv g ⟨j, i⟩))
  have hind := iIndepFun_infinitePi (P := fun j ↦ infinitePi fun i : {i // g i = j} ↦
      μ (Equiv.sigmaFiberEquiv g ⟨j, i⟩)) (X := fun _ ω ↦ ω) (fun _ ↦ measurable_id)
  rw [← hlaw] at hind
  exact iIndepFun_comp_of_map _ _
    ((MeasurableEquiv.piCurry (fun j (i : {i // g i = j}) ↦
        X (Equiv.sigmaFiberEquiv g ⟨j, i⟩))).measurable.comp
      (MeasurableEquiv.piCongrLeft X (Equiv.sigmaFiberEquiv g)).symm.measurable) _
    (fun j ↦ measurable_pi_apply j) hind

/-! ### The site model -/

variable {ι : Type*}

/-- The product of independent Bernoulli sites: site `i ∈ u` is present with probability `p`,
sites outside `u` are never present. -/
def siteLaw (u : Set ι) (p : I) : Measure (ι → Prop) :=
  infinitePi fun i ↦ Ber(i ∈ u, False, p)

instance siteLaw_isProbabilityMeasure (u : Set ι) (p : I) : IsProbabilityMeasure (siteLaw u p) := by
  unfold siteLaw
  infer_instance

/-- Mathlib's `setBer(u, p)` is the pushforward of the site law under `ω ↦ {i | ω i}`. -/
theorem setBernoulli_eq_map_siteLaw (u : Set ι) (p : I) :
    setBer(u, p) = (siteLaw u p).map (fun ω ↦ {i | ω i}) :=
  setBernoulli_eq_map u p

/-- Mathlib's binomial random graph is the pushforward of the site law on the non-diagonal
pairs under `ω ↦ fromEdgeSet {e | ω e}`. -/
theorem binomialRandom_eq_map_siteLaw (V : Type*) [Fintype V] (p : I) :
    SimpleGraph.binomialRandom V p =
      (siteLaw (Sym2.diagSetᶜ : Set (Sym2 V)) p).map
        (fun ω ↦ SimpleGraph.fromEdgeSet {e | ω e}) := by
  rw [SimpleGraph.binomialRandom_eq_map, setBernoulli_eq_map_siteLaw,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The number of present sites in the block `A`. -/
def blockCount (A : Finset ι) (ω : ι → Prop) : ℕ := by
  classical
  exact ∑ i ∈ A, if ω i then 1 else 0

open Classical in
theorem blockCount_eq_card (A : Finset ι) (ω : ι → Prop) :
    blockCount A ω = (A.filter fun i ↦ ω i).card := by
  unfold blockCount
  rw [Finset.card_filter]

theorem blockCount_le_card (A : Finset ι) (ω : ι → Prop) : blockCount A ω ≤ A.card := by
  classical
  unfold blockCount
  calc (∑ i ∈ A, if ω i then 1 else 0) ≤ ∑ _i ∈ A, 1 :=
        Finset.sum_le_sum fun i _ ↦ by split_ifs <;> simp
    _ = A.card := by simp

theorem blockCount_mono {A B : Finset ι} (h : A ⊆ B) (ω : ι → Prop) :
    blockCount A ω ≤ blockCount B ω := by
  classical
  unfold blockCount
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ ↦ by split_ifs <;> simp

open Classical in
theorem blockCount_eq_ncard (A : Finset ι) (ω : ι → Prop) :
    blockCount A ω = ({i | ω i} ∩ (A : Set ι)).ncard := by
  have : ({i | ω i} ∩ (A : Set ι)) = ((A.filter fun i ↦ ω i : Finset ι) : Set ι) := by
    ext i; simp [and_comm]
  rw [this, Set.ncard_coe_finset, blockCount_eq_card]

/-! ### The law of one block count -/

/-- Restricting a Bernoulli random set to a sub-block `A ⊆ u` gives the Bernoulli random
set on `A`. -/
theorem setBernoulli_map_inter [Fintype ι] (u A : Set ι) (p : I) (hA : A ⊆ u) :
    setBer(u, p).map (fun E ↦ E ∩ A) = setBer(A, p) := by
  rw [setBernoulli_eq_map, setBernoulli_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : ((fun E : Set ι ↦ E ∩ A) ∘ fun (ω : ι → Prop) ↦ {i | ω i}) =
      (fun (ω : ι → Prop) ↦ {i | ω i}) ∘ (fun (ω : ι → Prop) i ↦ ω i ∧ i ∈ A) := by
    funext ω; ext i; simp
  have hg : Measurable (fun (ω : ι → Prop) i ↦ ω i ∧ i ∈ A) := measurable_of_countable _
  rw [hcomp, ← Measure.map_map (by fun_prop) hg]
  congr 1
  have hpi := infinitePi_map_pi (fun i ↦ Ber(i ∈ u, False, p)) (f := fun i (q : Prop) ↦ q ∧ i ∈ A)
    (fun i ↦ measurable_of_countable _)
  simp only [bernoulliMeasure_def] at hpi
  rw [hpi]
  congr 1
  funext i
  rw [← bernoulliMeasure_def, map_bernoulliMeasure, bernoulliMeasure_def]
  have h1 : ((i ∈ u) ∧ i ∈ A) = (i ∈ A) := propext ⟨And.right, fun h ↦ ⟨hA h, h⟩⟩
  simp [h1]

/-- The cardinality of a Bernoulli random subset of a finite block is binomial. -/
theorem setBernoulli_map_ncard_eq_binomial [Fintype ι] (A : Finset ι) (p : I) :
    setBer((A : Set ι), p).map Set.ncard = binomial A.card p := by
  refine Measure.ext_of_singleton fun k ↦ ?_
  rw [map_ncard_setBernoulli_singleton A.finite_toSet p k, binomial_singleton,
    Set.ncard_coe_finset]

/-- The count of a block `A ⊆ u` is `binomial |A| p` under the site law. -/
theorem siteLaw_map_blockCount [Fintype ι] (u : Set ι) (p : I) (A : Finset ι)
    (hA : (A : Set ι) ⊆ u) :
    (siteLaw u p).map (blockCount A) = binomial A.card p := by
  have hfun : blockCount A =
      Set.ncard ∘ (fun E : Set ι ↦ E ∩ (A : Set ι)) ∘ (fun ω : ι → Prop ↦ {i | ω i}) := by
    funext ω
    exact blockCount_eq_ncard A ω
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), ← setBernoulli_eq_map_siteLaw,
    setBernoulli_map_inter u A p hA, setBernoulli_map_ncard_eq_binomial]

/-! ### Independence of disjoint block counts -/

/-- Counts of pairwise disjoint blocks are mutually independent under the site law. -/
theorem blockCount_iIndepFun [Fintype ι] (u : Set ι) (p : I) {J : Type*} (A : J → Finset ι)
    (hA : Pairwise fun j j' ↦ Disjoint (A j) (A j')) :
    iIndepFun (fun j ↦ blockCount (A j)) (siteLaw u p) := by
  classical
  -- the block map: a site is sent to the (unique) block containing it
  let g : ι → Option J := fun i ↦ if h : ∃ j, i ∈ A j then some h.choose else none
  have hg : ∀ j, ∀ i ∈ A j, g i = some j := by
    intro j i hi
    have h : ∃ j, i ∈ A j := ⟨j, hi⟩
    simp only [g, dif_pos h, Option.some.injEq]
    by_contra hne
    exact Finset.disjoint_left.mp (hA hne) h.choose_spec hi
  have hres := iIndepFun_fiberRestrict (fun i ↦ Ber(i ∈ u, False, p)) g
  have hres' := hres.precomp (Option.some_injective J)
  let φ : ∀ j : J, ({i // g i = some j} → Prop) → ℕ := fun j ω' ↦
    ∑ i ∈ (A j).attach, if ω' ⟨i.1, hg j i.1 i.2⟩ then 1 else 0
  have hφ : ∀ j, Measurable (φ j) := fun j ↦ measurable_of_countable _
  have hcomp := hres'.comp φ hφ
  have hfun : (fun j ↦ φ j ∘ fun (ω : ι → Prop) (i : {i // g i = some j}) ↦ ω i.1) =
      fun j ↦ blockCount (A j) := by
    funext j ω
    simp only [Function.comp, φ, blockCount]
    exact Finset.sum_attach (A j) fun i ↦ if ω i then 1 else 0
  rw [hfun] at hcomp
  exact hcomp

end MajorityDynamics.Probability.DegreeConcentration
