import MajorityDynamics.Probability.HypergeometricTiltTail.Basic

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail

/-- A nonempty fixed-size subset law preserves constants, including draw size zero. -/
theorem subsetAverage_const {V : Type*} [DecidableEq V]
    (A : Finset V) {k : ℕ} (hk : k ≤ A.card) (c : ℝ) :
    subsetAverage A k (fun _ => c) = c := by
  have hc : (A.card.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  simp only [subsetAverage, Finset.sum_const, Finset.card_powersetCard,
    nsmul_eq_mul]
  field_simp

theorem subsetAverage_add {V : Type*} [DecidableEq V]
    (A : Finset V) (k : ℕ) (f g : Finset V → ℝ) :
    subsetAverage A k (fun R => f R + g R) =
      subsetAverage A k f + subsetAverage A k g := by
  simp only [subsetAverage, Finset.sum_add_distrib, mul_add]

theorem subsetAverage_sub {V : Type*} [DecidableEq V]
    (A : Finset V) (k : ℕ) (f g : Finset V → ℝ) :
    subsetAverage A k (fun R => f R - g R) =
      subsetAverage A k f - subsetAverage A k g := by
  simp only [subsetAverage, Finset.sum_sub_distrib, mul_sub]

/-- The mean of the actual pair of independent uniform subset laws is the
literal centered coefficient mean. Feasible zero-size strata are included. -/
theorem pair_tilt_actual_mean {V : Type*} [DecidableEq V]
    {P S : Finset V} (hSP : S ⊆ P) {k l : ℕ}
    (hk : k ≤ S.card) (hl : l ≤ (P \ S).card)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (β : V → ℝ) :
    subsetAverage S k (fun R => subsetAverage (P \ S) l
      (fun Q => tiltWeight P (R ∪ Q) p L β)) =
      ((1+p)*k/S.card-p)*(∑ v ∈ S, β v)/Real.sqrt (p*L) +
        ((1+p)*l/(P \ S).card-p)*(∑ v ∈ P \ S, β v)/Real.sqrt (p*L) := by
  have he : subsetAverage S k (fun R => subsetAverage (P \ S) l
      (fun Q => tiltWeight P (R ∪ Q) p L β)) =
      subsetAverage S k (fun R => subsetAverage (P \ S) l
        (fun Q => (∑ v ∈ R, tiltCoefficient p L β v) +
          (∑ v ∈ Q, tiltCoefficient p L β v) - tiltConstant P p L β)) := by
    apply subsetAverage_congr
    intro R hR
    apply subsetAverage_congr
    intro Q hQ
    exact tiltWeight_union hSP (Finset.mem_powersetCard.mp hR).1
      (Finset.mem_powersetCard.mp hQ).1 hp hL β
  rw [he]
  simp only [subsetAverage_sub, subsetAverage_add,
    subsetAverage_const _ hl, subset_average_mean _ hl,
    subsetAverage_const _ hk, subset_average_mean _ hk]
  exact pair_mean_eq hSP hp hL β k l

end MajorityDynamics.Probability.HypergeometricTiltTail
