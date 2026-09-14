import MajorityDynamics.Probability.NeighborhoodBulk.ResidualData
import MajorityDynamics.Probability.NeighborhoodBulk.BernoulliProfile
import MajorityDynamics.Literature.DegreeEnumeration.Counts

noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Combinatorics.DegreeRatios

theorem choose_delete_selected (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) (hdN : d ≤ N) :
    ((N - 1).choose (d - 1) : ℝ) / (N.choose d : ℝ) = (d : ℝ) / N := by
  have h := Nat.add_one_mul_choose_eq (N - 1) (d - 1)
  rw [Nat.sub_add_cancel hN, Nat.sub_add_cancel hd] at h
  have hr : (N : ℝ) * ((N - 1).choose (d - 1) : ℝ) = (N.choose d : ℝ) * d := by exact_mod_cast h
  have hc : (N.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdN).ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  apply (div_eq_div_iff hc hN0).mpr
  nlinarith only [hr]

theorem choose_delete_unselected (N d : ℕ) (hN : 1 ≤ N) (hdN : d ≤ N) :
    ((N - 1).choose d : ℝ) / (N.choose d : ℝ) = 1 - (d : ℝ) / N := by
  have h := Nat.choose_mul_succ_eq (N - 1) d
  rw [Nat.sub_add_cancel hN] at h
  have hr : ((N - 1).choose d : ℝ) * N = (N.choose d : ℝ) * ((N : ℝ) - d) := by
    exact_mod_cast h
  have hc : (N.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdN).ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have he : 1 - (d : ℝ) / N = ((N : ℝ) - d) / N := by field_simp
  rw [he]
  apply (div_eq_div_iff hc hN0).mpr
  nlinarith only [hr]

theorem choose_delete_product {V : Type*} (A R : Finset V) (N : ℕ) (d : V → ℕ)
    (hN : 1 ≤ N) (hR : R ⊆ A) (hd : ∀ i ∈ A, d i ≤ N) (hpos : ∀ i ∈ R, 1 ≤ d i) :
    (∏ i ∈ A, ((N - 1).choose (d i - if i ∈ R then 1 else 0) : ℝ)) /
      (∏ i ∈ A, (N.choose (d i) : ℝ)) = bernoulliProduct A R (fun i => (d i : ℝ) / N) := by
  rw [← Finset.prod_div_distrib]
  have he : (∏ i ∈ A, ((N - 1).choose (d i - if i ∈ R then 1 else 0) : ℝ) /
      (N.choose (d i) : ℝ)) =
      ∏ i ∈ A, if i ∈ R then (d i : ℝ) / N else 1 - (d i : ℝ) / N := by
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs with hmem
    · exact choose_delete_selected N (d i) hN (hpos i hmem) (hd i hi)
    · simpa only [Nat.sub_zero] using choose_delete_unselected N (d i) hN (hd i hi)
  rw [he, Finset.prod_ite]
  have hy : A.filter (fun i => i ∈ R) = R := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hR h, h⟩⟩
  have hn : A.filter (fun i => i ∉ R) = A \ R := by ext i; simp
  rw [hy, hn]
  rfl

theorem prod_remaining_mul {V M : Type*} [Fintype V] [CommMonoid M] (f : V → M) (v : V) :
    (∏ u : Remaining v, f u) * f v = ∏ u, f u := by
  rw [← Finset.prod_subtype (Finset.univ.erase v) (by simp)]
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ v)

theorem graphResidualFin_choose_product {n : ℕ} (d : Fin n → ℕ) (v : Fin n) (R : Finset (Fin n)) :
    (∏ i, ((n - 2).choose (graphResidualFin d v R i) : ℝ)) =
      ∏ i ∈ Finset.univ.erase v, ((n - 2).choose (d i - if i ∈ R then 1 else 0) : ℝ) := by
  unfold graphResidualFin
  rw [(remainingEquiv v).symm.prod_comp
    (fun u : Remaining v => ((n - 2).choose (residualDegree d v R u) : ℝ))]
  unfold residualDegree
  convert (Finset.prod_subtype (p := fun u : Fin n => u ≠ v) (Finset.univ.erase v) (by simp)
    (fun i => ((n - 2).choose (d i - if i ∈ R then 1 else 0) : ℝ))).symm using 1
  congr 1
  ext i
  split_ifs <;> rfl

theorem graph_choose_product_ratio {n : ℕ} (d : Fin n → ℕ) (v : Fin n) (R : Finset (Fin n))
    (hn : 2 ≤ n) (hR : v ∉ R) (hd : ∀ i, d i ≤ n - 1) (hpos : ∀ i ∈ R, 1 ≤ d i) :
    (∏ i, ((n - 2).choose (graphResidualFin d v R i) : ℝ)) /
      (∏ i, ((n - 1).choose (d i) : ℝ)) =
        bernoulliProduct (Finset.univ.erase v) R (fun i => (d i : ℝ) / (n - 1 : ℕ)) /
          ((n - 1).choose (d v) : ℝ) := by
  have hsub : R ⊆ Finset.univ.erase v := by
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    exact hR (he ▸ hi)
  have hh := choose_delete_product (Finset.univ.erase v) R (n - 1) d (by omega) hsub
    (fun i _ => hd i) hpos
  have hpred : n - 1 - 1 = n - 2 := by omega
  rw [hpred] at hh
  rw [graphResidualFin_choose_product, ← Finset.prod_erase_mul Finset.univ
    (fun i => ((n - 1).choose (d i) : ℝ)) (Finset.mem_univ v)]
  rw [← div_div]
  congr 1
  convert hh using 1
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> rfl

theorem leftResidualFin_choose_product {ell n : ℕ} (a : Fin ell → ℕ) (v : Fin ell) :
    (∏ i, (n.choose (leftResidualFin a v i) : ℝ)) * (n.choose (a v) : ℝ) =
      ∏ i, (n.choose (a i) : ℝ) := by
  unfold leftResidualFin
  rw [(remainingEquiv v).symm.prod_comp (fun u : Remaining v => (n.choose (a u) : ℝ))]
  convert prod_remaining_mul (fun i => (n.choose (a i) : ℝ)) v using 1
  congr 2
  ext i
  simp

end MajorityDynamics.Probability.NeighborhoodBulk
