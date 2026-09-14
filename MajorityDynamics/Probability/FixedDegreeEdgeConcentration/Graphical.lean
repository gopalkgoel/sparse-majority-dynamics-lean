import MajorityDynamics.GraphProcess.AutomaticGraphicality.Relabel
import MajorityDynamics.Probability.FixedDegreeSampling.Laws

/-! Normalization from the already accepted A.8/A.9 sufficient graphicality
criteria, and exact conversions of signed degree/count inputs. -/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling GraphProcess.AutomaticGraphicality

variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

theorem graphFamily_nonempty_of_degree_bound (d : V → ℕ) (m : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hd : ∀ v, (d v : ℝ) ≤ D) (hsum : ∑ v, d v = 2 * m)
    (hbound : D * (D + 1) ≤ 2 * (m : ℝ)) : (graphFamily d).Nonempty := by
  have hs : ∑ v, (d v : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hsum
  obtain ⟨G, hG⟩ := graphical_of_bound (fun v => (d v : ℤ)) D
    (fun v => Int.natCast_nonneg _) hD (by simpa using hd)
    (by rw [hs]; exact even_two_mul _) (by rw [hs]; exact_mod_cast hbound)
  refine ⟨G, fun v => ?_⟩
  exact_mod_cast hG v

theorem graphLaw_normalized_of_degree_bound (d : V → ℕ) (m : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hd : ∀ v, (d v : ℝ) ≤ D) (hsum : ∑ v, d v = 2 * m)
    (hbound : D * (D + 1) ≤ 2 * (m : ℝ)) : IsProbabilityMeasure (fixedDegreeLaw d) :=
  fixedDegreeLaw_normalized d (graphFamily_nonempty_of_degree_bound d m D hD hd hsum hbound)

theorem bipartiteFamily_nonempty_of_degree_bound (a : L → ℕ) (b : R → ℕ)
    (m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (ha : ∀ v, (a v : ℝ) ≤ D) (hb : ∀ w, (b w : ℝ) ≤ D)
    (hsA : ∑ v, a v = m) (hsB : ∑ w, b w = m) (hbound : D ^ 2 ≤ (m : ℝ)) :
    (bipartiteFamily a b).Nonempty := by
  have hsA' : ∑ v, (a v : ℤ) = (m : ℤ) := by exact_mod_cast hsA
  have hsB' : ∑ w, (b w : ℤ) = (m : ℤ) := by exact_mod_cast hsB
  obtain ⟨E, hE, hF⟩ := cross_of_bound (fun v => (a v : ℤ)) (fun w => (b w : ℤ)) D
    (fun v => Int.natCast_nonneg _) (fun w => Int.natCast_nonneg _) hD
    (by simpa using ha) (by simpa using hb) (hsA'.trans hsB'.symm)
    (by rw [hsA']; exact_mod_cast hbound)
  refine ⟨E, (fun v => ?_), (fun w => ?_)⟩
  · exact_mod_cast hE v
  · exact_mod_cast hF w

theorem bipartiteLaw_normalized_of_degree_bound (a : L → ℕ) (b : R → ℕ)
    (m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (ha : ∀ v, (a v : ℝ) ≤ D) (hb : ∀ w, (b w : ℝ) ≤ D)
    (hsA : ∑ v, a v = m) (hsB : ∑ w, b w = m) (hbound : D ^ 2 ≤ (m : ℝ)) :
    IsProbabilityMeasure (bipartiteFixedDegreeLaw a b) :=
  bipartiteFixedDegreeLaw_normalized a b
    (bipartiteFamily_nonempty_of_degree_bound a b m D hD ha hb hsA hsB hbound)

omit [Fintype V] in
/-- Exact natural degree conversion; neither a truncation error nor a new bound. -/
theorem signed_degree_cast (d : V → ℤ) (hd : ∀ v, 0 ≤ d v) (v : V) :
    ((d v).toNat : ℤ) = d v := Int.toNat_of_nonneg (hd v)

omit [Fintype V] in
theorem signed_degree_real (d : V → ℤ) (hd : ∀ v, 0 ≤ d v) (v : V) :
    ((d v).toNat : ℝ) = (d v : ℝ) := by
  exact_mod_cast signed_degree_cast d hd v

omit [Fintype V] in
theorem signed_subset_degree_sum (d : V → ℤ) (hd : ∀ v, 0 ≤ d v) (U : Finset V) :
    (∑ v ∈ U, ((d v).toNat : ℝ)) = ((∑ v ∈ U, d v : ℤ) : ℝ) := by
  simp only [signed_degree_real d hd, Int.cast_sum]

theorem signed_graph_total (d : V → ℤ) (m : ℤ) (hd : ∀ v, 0 ≤ d v)
    (hsum : ∑ v, d v = 2 * m) :
    0 ≤ m ∧ ∑ v, (d v).toNat = 2 * m.toNat ∧ (m.toNat : ℤ) = m := by
  have hnonneg : 0 ≤ ∑ v, d v := Finset.sum_nonneg (fun v _ => hd v)
  have hm : 0 ≤ m := by omega
  refine ⟨hm, ?_, Int.toNat_of_nonneg hm⟩
  have hh : ((∑ v, (d v).toNat : ℕ) : ℤ) = (2 * m.toNat : ℕ) := by
    push_cast
    simp only [Int.toNat_of_nonneg hm, signed_degree_cast d hd]
    exact hsum
  exact_mod_cast hh

theorem signed_bipartite_total (a : L → ℤ) (b : R → ℤ) (m : ℤ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ w, 0 ≤ b w)
    (hsA : ∑ v, a v = m) (hsB : ∑ w, b w = m) :
    0 ≤ m ∧ ∑ v, (a v).toNat = m.toNat ∧
      ∑ w, (b w).toNat = m.toNat ∧ (m.toNat : ℤ) = m := by
  have hm : 0 ≤ m := hsA ▸ Finset.sum_nonneg (fun v _ => ha v)
  refine ⟨hm, ?_, ?_, Int.toNat_of_nonneg hm⟩
  · have h : ((∑ v, (a v).toNat : ℕ) : ℤ) = m.toNat := by
      push_cast
      simp only [Int.toNat_of_nonneg hm, signed_degree_cast a ha]
      exact hsA
    exact_mod_cast h
  · have h : ((∑ w, (b w).toNat : ℕ) : ℤ) = m.toNat := by
      push_cast
      simp only [Int.toNat_of_nonneg hm, signed_degree_cast b hb]
      exact hsB
    exact_mod_cast h

omit [Fintype L] [Fintype R] in
theorem signed_card_conversion (ell : ℤ) (hell : (Fintype.card V : ℤ) = ell) :
    0 ≤ ell ∧ ell.toNat = Fintype.card V ∧ (ell.toNat : ℝ) = (ell : ℝ) := by
  subst ell
  simp

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
