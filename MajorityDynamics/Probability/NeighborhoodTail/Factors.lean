import MajorityDynamics.Probability.NeighborhoodTail.Basic
import MajorityDynamics.Probability.HypergeometricTiltTail.Adapters

/-! Exact finite bridges between the C.4 comparison expression and the proved
weighted hypergeometric factor. Empty subset families need no exceptions. -/
noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open NeighborhoodBulk HypergeometricTiltTail

theorem subsetExpectation_eq_nested {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) (k l : ℕ) (f : Finset V → ℝ) :
    subsetExpectation A B k l f =
      subsetAverage A k (fun R => subsetAverage B l (fun Q => f (R ∪ Q))) := by
  rw [subsetExpectation_eq_average]
  simp only [subsetAverage, ← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_assoc]
  congr!

theorem graphWeight_eq_tilt {n : ℕ} (p : ℝ) (d : Fin n → ℤ)
    (v : Fin n) (R : Finset (Fin n)) :
    graphWeight p d v R =
      tiltWeight (Finset.univ.erase v) R p n (fun i => standardizedDegree p n (d i)) := by
  rw [show (n : ℝ) = Fintype.card (Fin n) by simp, graph_tiltWeight_eq]
  simp only [Fintype.card_fin, graphWeight, ← Finset.sum_div,
    ← Finset.mul_sum]
  ring

theorem bipartiteWeight_eq_tilt {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ)
    (R : Finset (Fin n)) :
    bipartiteWeight p ell b R =
      tiltWeight Finset.univ R p ell (fun i => standardizedDegree p ell (b i)) := by
  simp only [bipartiteWeight, tiltWeight, ← Finset.sum_div,
    ← Finset.mul_sum]
  ring

theorem graphComparison_eq_factor {n : ℕ} (p : ℝ) (d : Fin n → ℤ)
    (v : Fin n) (S : Finset (Fin n)) {t : ℤ} (ht : 0 ≤ t) (htd : t ≤ d v) :
    graphComparison p d v S t =
      weightedFactor (Finset.univ.erase v) (S.erase v) (d v) t p n
        (fun i => standardizedDegree p n (d i)) := by
  have h := graphFactor_eq v S ht htd p (fun i => standardizedDegree p n (d i))
  simp only [graphFactor, Fintype.card_fin] at h
  rw [h, graphComparison, subsetExpectation_eq_nested]
  congr 1
  apply subsetAverage_congr
  intro R _
  apply subsetAverage_congr
  intro Q _
  congr 1
  rw [graphWeight_eq_tilt]
  simp only [tiltWeight, erased_population_sdiff]

theorem bipartiteComparison_eq_factor {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ)
    (dv : ℤ) (S : Finset (Fin n)) {t : ℤ} (ht : 0 ≤ t) (htd : t ≤ dv) :
    bipartiteComparison p ell b dv S t =
      weightedFactor Finset.univ S dv t p ell (fun i => standardizedDegree p ell (b i)) := by
  have h := bipartiteFactor_eq S ht htd p (ell : ℝ)
    (fun i => standardizedDegree p ell (b i))
  simp only [bipartiteFactor, Fintype.card_fin] at h
  rw [h, bipartiteComparison, subsetExpectation_eq_nested]
  congr 1
  apply subsetAverage_congr
  intro R _
  apply subsetAverage_congr
  intro Q _
  congr 1
  rw [bipartiteWeight_eq_tilt]
  rfl

theorem degreeWindow_of_standardized {p : ℝ} {n : ℕ} {d : ℤ}
    (hp : 0 < p) (hn : 0 < n) (hd : |standardizedDegree p n d| ≤ Real.log n) :
    |(d : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n := by
  have hs : 0 < Real.sqrt (p * n) := Real.sqrt_pos.2 (mul_pos hp (by exact_mod_cast hn))
  rw [standardizedDegree, abs_div, abs_of_pos hs] at hd
  have h := (div_le_iff₀ hs).mp hd
  simpa only [mul_comm] using h

end MajorityDynamics.Probability.NeighborhoodTail
