import MajorityDynamics.Probability.HypergeometricTiltTail.MGF

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

/-- The literal average over all prescribed-size subsets; an empty family has average zero. -/
def subsetAverage {V : Type*} [DecidableEq V] (A : Finset V) (k : ℕ)
    (f : Finset V → ℝ) : ℝ :=
  (A.card.choose k : ℝ)⁻¹ * ∑ R ∈ A.powersetCard k, f R

theorem subsetAverage_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ↪ W) (A : Finset V) (k : ℕ) (f : Finset W → ℝ) :
    subsetAverage (A.map e) k f = subsetAverage A k (fun R => f (R.map e)) := by
  simp [subsetAverage, Finset.powersetCard_map]

theorem subsetAverage_fin_eq_expectation {n k : ℕ} (hk : k ≤ n)
    (f : Finset (Fin n) → ℝ) :
    subsetAverage Finset.univ k f =
      fixedSizeExpectation n k (fun ξ => f (bitSet ξ)) := by
  classical
  rw [fixedSizeExpectation_eq_average hk]
  unfold subsetAverage fixedSizeAverage
  simp only [Finset.card_univ, Fintype.card_fin]
  congr 1
  symm
  apply Finset.sum_equiv (bitFinsetEquiv n)
  · intro ξ
    change (ξ ∈ fixedSizeEvent n k) ↔ (bitSet ξ) ∈ Finset.univ.powersetCard k
    constructor
    · intro h
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp h).2⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_powersetCard.mp h).2⟩
  · intro ξ hξ
    rfl

/-- The concrete enumeration of a finite carrier used only to transport laws. -/
def carrierEmbedding {V : Type*} [DecidableEq V] (A : Finset V) : Fin A.card ↪ V :=
  A.equivFin.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

theorem carrierEmbedding_mem {V : Type*} [DecidableEq V] (A : Finset V)
    (i : Fin A.card) : carrierEmbedding A i ∈ A := (A.equivFin.symm i).property

theorem carrierEmbedding_univ {V : Type*} [DecidableEq V] (A : Finset V) :
    Finset.univ.map (carrierEmbedding A) = A := by
  classical
  ext v
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact carrierEmbedding_mem A i
  · intro hv
    exact ⟨A.equivFin ⟨v, hv⟩, by simp [carrierEmbedding]⟩

theorem subsetAverage_eq_expectation {V : Type*} [DecidableEq V]
    (A : Finset V) {k : ℕ} (hk : k ≤ A.card) (f : Finset V → ℝ) :
    subsetAverage A k f = fixedSizeExpectation A.card k
      (fun ξ => f ((bitSet ξ).map (carrierEmbedding A))) := by
  rw [← subsetAverage_fin_eq_expectation hk (fun R => f (R.map (carrierEmbedding A)))]
  rw [← subsetAverage_map, carrierEmbedding_univ]

theorem carrierEmbedding_sum {V : Type*} [DecidableEq V]
    (A : Finset V) (a : V → ℝ) :
    ∑ i : Fin A.card, a (carrierEmbedding A i) = ∑ v ∈ A, a v := by
  calc
    _ = ∑ v ∈ Finset.univ.map (carrierEmbedding A), a v := by rw [Finset.sum_map]
    _ = _ := by rw [carrierEmbedding_univ]

theorem bitLinear_map {V : Type*} [DecidableEq V] {n : ℕ}
    (e : Fin n ↪ V) (a : V → ℝ) (ξ : Bit n) :
    ∑ v ∈ (bitSet ξ).map e, a v = bitLinear (fun i => a (e i)) ξ := by
  classical
  simp [Finset.sum_map, bitSet, bitLinear, Finset.sum_filter]

theorem subset_average_mgf {V : Type*} [DecidableEq V]
    (A : Finset V) {k : ℕ} (hk : k < A.card) (a : V → ℝ)
    (ha : ∀ v ∈ A, |a v| ≤ 1) :
    subsetAverage A k (fun R => Real.exp (∑ v ∈ R, a v)) ≤
      mgfPrefactor k * Real.exp (((k : ℝ) / A.card) * ∑ v ∈ A, a v +
        ((k : ℝ) / A.card) * ∑ v ∈ A, (a v)^2) := by
  rw [subsetAverage_eq_expectation A hk.le]
  simp only [bitLinear_map]
  have h := fixedSize_mgf hk (fun i => a (carrierEmbedding A i))
    (fun i => ha _ (carrierEmbedding_mem A i))
  rw [carrierEmbedding_sum A a, carrierEmbedding_sum A (fun v => (a v)^2)] at h
  exact h

theorem subset_average_mean {V : Type*} [DecidableEq V]
    (A : Finset V) {k : ℕ} (hk : k ≤ A.card) (a : V → ℝ) :
    subsetAverage A k (fun R => ∑ v ∈ R, a v) =
      ((k : ℝ) / A.card) * ∑ v ∈ A, a v := by
  rw [subsetAverage_eq_expectation A hk]
  simp only [bitLinear_map, fixedSize_mean_all hk, carrierEmbedding_sum]

theorem subsetAverage_empty_family {V : Type*} [DecidableEq V]
    (A : Finset V) {k : ℕ} (hk : A.card < k) (f : Finset V → ℝ) :
    subsetAverage A k f = 0 := by
  simp [subsetAverage, Nat.choose_eq_zero_of_lt hk]

theorem subsetAverage_zero {V : Type*} [DecidableEq V]
    (A : Finset V) (f : Finset V → ℝ) : subsetAverage A 0 f = f ∅ := by
  simp [subsetAverage]

end MajorityDynamics.Probability.HypergeometricTiltTail
