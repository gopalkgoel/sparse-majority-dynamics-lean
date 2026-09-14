import MajorityDynamics.Probability.HypergeometricTiltTail.Algebra
import MajorityDynamics.Probability.HypergeometricTiltTail.MGFTransport
import MajorityDynamics.Probability.HypergeometricTiltTail.Hypergeom

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail

/-- Actual expectation under independent uniform subsets of a part and its complement. -/
def tiltExpectation {V : Type*} [DecidableEq V] (P S : Finset V)
    (k l : ℕ) (p L : ℝ) (β : V → ℝ) : ℝ :=
  subsetAverage S k (fun R => subsetAverage (P \ S) l
    (fun Q => Real.exp (tiltWeight P (R ∪ Q) p L β)))

/-- The literal hypergeometric mass multiplied by the literal two-subset expectation. -/
def weightedFactor {V : Type*} [DecidableEq V] (P S : Finset V)
    (d t : ℤ) (p L : ℝ) (β : V → ℝ) : ℝ :=
  hypergeomMass P.card S.card d.toNat t.toNat *
    tiltExpectation P S t.toNat (d - t).toNat p L β

theorem subsetAverage_nonneg {V : Type*} [DecidableEq V]
    (A : Finset V) (k : ℕ) (f : Finset V → ℝ) (hf : ∀ R, 0 ≤ f R) :
    0 ≤ subsetAverage A k f := by
  unfold subsetAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun R _ => hf R)

theorem subsetAverage_congr {V : Type*} [DecidableEq V]
    (A : Finset V) (k : ℕ) (f g : Finset V → ℝ)
    (h : ∀ R ∈ A.powersetCard k, f R = g R) :
    subsetAverage A k f = subsetAverage A k g := by
  unfold subsetAverage
  rw [Finset.sum_congr rfl h]

theorem subsetAverage_mul_const {V : Type*} [DecidableEq V]
    (A : Finset V) (k : ℕ) (f : Finset V → ℝ) (c : ℝ) :
    subsetAverage A k (fun R => f R * c) = subsetAverage A k f * c := by
  simp only [subsetAverage, ← Finset.sum_mul]
  ring

theorem subsetAverage_const_mul {V : Type*} [DecidableEq V]
    (A : Finset V) (k : ℕ) (f : Finset V → ℝ) (c : ℝ) :
    subsetAverage A k (fun R => c * f R) = c * subsetAverage A k f := by
  simp only [subsetAverage, ← Finset.mul_sum]
  ring

theorem tiltExpectation_nonneg {V : Type*} [DecidableEq V]
    (P S : Finset V) (k l : ℕ) (p L : ℝ) (β : V → ℝ) :
    0 ≤ tiltExpectation P S k l p L β := by
  apply subsetAverage_nonneg
  intro R
  exact subsetAverage_nonneg _ _ _ (fun Q => (Real.exp_pos _).le)

/-- Independence and exact weight linearization give a product of two actual MGFs. -/
theorem tiltExpectation_product {V : Type*} [DecidableEq V]
    {P S : Finset V} (hSP : S ⊆ P) (k l : ℕ)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (β : V → ℝ) :
    tiltExpectation P S k l p L β =
    Real.exp (-tiltConstant P p L β) *
      subsetAverage S k (fun R => Real.exp (∑ v ∈ R, tiltCoefficient p L β v)) *
      subsetAverage (P \ S) l
        (fun Q => Real.exp (∑ v ∈ Q, tiltCoefficient p L β v)) := by
  unfold tiltExpectation
  have he : ∀ R ∈ S.powersetCard k,
      subsetAverage (P \ S) l (fun Q => Real.exp (tiltWeight P (R ∪ Q) p L β)) =
      Real.exp (-tiltConstant P p L β) *
        Real.exp (∑ v ∈ R, tiltCoefficient p L β v) *
        subsetAverage (P \ S) l
          (fun Q => Real.exp (∑ v ∈ Q, tiltCoefficient p L β v)) := by
    intro R hR
    rw [← subsetAverage_const_mul]
    apply subsetAverage_congr
    intro Q hQ
    rw [tiltWeight_union hSP (Finset.mem_powersetCard.mp hR).1
      (Finset.mem_powersetCard.mp hQ).1 hp hL]
    rw [show (∑ v ∈ R, tiltCoefficient p L β v) +
        (∑ v ∈ Q, tiltCoefficient p L β v) - tiltConstant P p L β =
        -tiltConstant P p L β + (∑ v ∈ R, tiltCoefficient p L β v) +
          (∑ v ∈ Q, tiltCoefficient p L β v) by ring,
      Real.exp_add, Real.exp_add]
  rw [subsetAverage_congr S k _ _ he, subsetAverage_mul_const, subsetAverage_const_mul]

/-- If either subset family is empty, its actual expectation, and hence factor, vanishes. -/
theorem tiltExpectation_empty_left {V : Type*} [DecidableEq V]
    (P S : Finset V) {k : ℕ} (hk : S.card < k) (l : ℕ) (p L : ℝ) (β : V → ℝ) :
    tiltExpectation P S k l p L β = 0 := by
  exact subsetAverage_empty_family S hk _

theorem tiltExpectation_empty_right {V : Type*} [DecidableEq V]
    (P S : Finset V) (k : ℕ) {l : ℕ} (hl : (P \ S).card < l)
    (p L : ℝ) (β : V → ℝ) :
    tiltExpectation P S k l p L β = 0 := by
  unfold tiltExpectation
  simp only [subsetAverage_empty_family (P \ S) hl]
  simp [subsetAverage]

/-- Zero and full-draw target counts use the same law, with a deterministic empty piece. -/
theorem tiltExpectation_zero_left {V : Type*} [DecidableEq V]
    (P S : Finset V) (l : ℕ) (p L : ℝ) (β : V → ℝ) :
    tiltExpectation P S 0 l p L β = subsetAverage (P \ S) l
      (fun Q => Real.exp (tiltWeight P Q p L β)) := by
  simp [tiltExpectation, subsetAverage_zero]

theorem tiltExpectation_zero_right {V : Type*} [DecidableEq V]
    (P S : Finset V) (k : ℕ) (p L : ℝ) (β : V → ℝ) :
    tiltExpectation P S k 0 p L β = subsetAverage S k
      (fun R => Real.exp (tiltWeight P R p L β)) := by
  simp [tiltExpectation, subsetAverage_zero]

end MajorityDynamics.Probability.HypergeometricTiltTail
