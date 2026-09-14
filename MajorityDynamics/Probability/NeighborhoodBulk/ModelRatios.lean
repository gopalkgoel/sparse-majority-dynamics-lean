import MajorityDynamics.Probability.NeighborhoodBulk.BinomialProducts

noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Combinatorics.DegreeRatios

theorem graph_model_ratio {n m : ℕ} (d : Fin n → ℕ) (v : Fin n) (R : Finset (Fin n))
    (hn : 2 ≤ n) (hR : v ∉ R) (hd : ∀ i, d i ≤ n - 1) (hpos : ∀ i ∈ R, 1 ≤ d i) :
    graphCountModel (m - d v) (graphResidualFin d v R) / graphCountModel m d =
      graphRatio n (m : ℤ) (d v : ℤ) *
        bernoulliProduct (Finset.univ.erase v) R (fun i => (d i : ℝ) / (n - 1 : ℕ)) /
          ((n - 1).choose (d v) : ℝ) := by
  have hpred : n - 1 - 1 = n - 2 := by omega
  have htwo : (2 * (m : ℤ) - 2 * (d v : ℤ)).toNat = 2 * (m - d v) := by omega
  have hsub : ((m : ℤ) - (d v : ℤ)).toNat = m - d v := by omega
  unfold graphCountModel
  rw [hpred]
  have hfactor : ∀ A B P Q : ℝ, (A * P) / (B * Q) = (A / B) * (P / Q) := by
    intros; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  rw [hfactor, graph_choose_product_ratio d v R hn hR hd hpos]
  have hratio :
      ((((n - 1).choose 2).choose (m - d v) : ℝ) /
        (((n - 1) * (n - 2)).choose (2 * (m - d v)) : ℝ)) /
      (((n.choose 2).choose m : ℝ) / ((n * (n - 1)).choose (2 * m) : ℝ)) =
        graphRatio n (m : ℤ) (d v : ℤ) := by
    unfold graphRatio edgeCapacity
    rw [Nat.choose_two_right, Nat.choose_two_right, hpred, htwo, hsub]
    norm_cast
  rw [hratio]
  ring

theorem bipartite_right_product_ratio {ell n : ℕ} (b : Fin n → ℕ) (R : Finset (Fin n))
    (hell : 1 ≤ ell) (hb : ∀ j, b j ≤ ell) (hpos : ∀ j ∈ R, 1 ≤ b j) :
    (∏ j, ((ell - 1).choose (residualRightDegree b R j) : ℝ)) /
      (∏ j, (ell.choose (b j) : ℝ)) =
        bernoulliProduct Finset.univ R (fun j => (b j : ℝ) / ell) := by
  have h := choose_delete_product Finset.univ R ell b hell (Finset.subset_univ R)
    (fun j _ => hb j) hpos
  exact h

theorem bipartite_model_ratio {ell n m : ℕ} (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (v : Fin ell) (R : Finset (Fin n)) (hell : 1 ≤ ell)
    (ha : ∀ i, a i ≤ n) (hb : ∀ j, b j ≤ ell) (hpos : ∀ j ∈ R, 1 ≤ b j) :
    bipartiteCountModel (m - a v) (leftResidualFin a v) (residualRightDegree b R) /
      bipartiteCountModel m a b =
        bipartiteRatio n (ell : ℤ) (m : ℤ) (a v : ℤ) *
          bernoulliProduct Finset.univ R (fun j => (b j : ℝ) / ell) /
            (n.choose (a v) : ℝ) := by
  have hleft : (∏ i, (n.choose (leftResidualFin a v i) : ℝ)) /
      (∏ i, (n.choose (a i) : ℝ)) = 1 / (n.choose (a v) : ℝ) := by
    rw [← leftResidualFin_choose_product a v]
    have hne : (∏ i, (n.choose (leftResidualFin a v i) : ℝ)) ≠ 0 := by
      apply ne_of_gt
      apply Finset.prod_pos
      intro i _
      exact_mod_cast Nat.choose_pos (ha ((remainingEquiv v).symm i))
    field_simp
  have hfactor : ∀ L R E L' R' E' : ℝ,
      (L' * R' / E') / (L * R / E) = (E / E') * (L' / L) * (R' / R) := by
    intros; simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  unfold bipartiteCountModel
  rw [hfactor, hleft, bipartite_right_product_ratio b R hell hb hpos]
  have he : (((ell : ℤ) - 1) * (n : ℤ)).toNat = (ell - 1) * n := by
    rw [Int.toNat_mul (by omega) (by omega), Int.toNat_natCast]
    congr 1
    omega
  have hsub : ((m : ℤ) - (a v : ℤ)).toNat = m - a v := by omega
  unfold bipartiteRatio
  rw [he, hsub]
  simp only [← Nat.cast_mul, Int.toNat_natCast]
  ring

end MajorityDynamics.Probability.NeighborhoodBulk
