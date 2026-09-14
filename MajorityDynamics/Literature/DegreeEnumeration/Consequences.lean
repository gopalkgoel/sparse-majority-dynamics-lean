import MajorityDynamics.Literature.DegreeEnumeration.Statements
import MajorityDynamics.Literature.DegreeEnumeration.FixedEdges

/-! Positivity consequences of the source comparison. These lemmas derive
nonempty graph fibers from a sufficiently accurate enumeration formula;
graphicality is not assumed. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Probability.FixedDegreeSampling

theorem RelativeApproximation.bounds {δ P Q : ℝ}
    (h : RelativeApproximation δ P Q) (hQ : 0 ≤ Q) :
    (1 - δ) * Q ≤ P ∧ P ≤ (1 + δ) * Q := by
  obtain ⟨ε, hε, rfl⟩ := h
  obtain ⟨hl, hu⟩ := abs_le.mp hε
  constructor <;> nlinarith

theorem RelativeApproximation.pos {δ P Q : ℝ}
    (h : RelativeApproximation δ P Q) (hδ : δ < 1) (hQ : 0 < Q) : 0 < P := by
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hδ) hQ) (h.bounds hQ.le).1

theorem RelativeApproximation.mono {δ δ' P Q : ℝ}
    (h : RelativeApproximation δ P Q) (hδ : δ ≤ δ') : RelativeApproximation δ' P Q := by
  obtain ⟨ε, hε, he⟩ := h
  exact ⟨ε, hε.trans hδ, he⟩

theorem graphDegreeLaw_real_atom {V : Type*} [Fintype V]
    (d : V → ℕ) (m : ℕ) (hs : ∑ i, d i = 2 * m) :
    (graphDegreeLaw V m).real {d} =
      (graphCount d : ℝ) / (((Fintype.card V).choose 2).choose m : ℝ) := by
  rw [measureReal_def, graphDegreeLaw_atom d m hs, ENNReal.toReal_div]
  simp

theorem bipartiteDegreeLaw_real_atom {L R : Type*} [Fintype L] [Fintype R]
    (a : L → ℕ) (b : R → ℕ) (m : ℕ) (hs : ∑ i, a i = m) :
    (bipartiteDegreeLaw L R m).real {(a, b)} =
      (bipartiteCount a b : ℝ) / ((Fintype.card L * Fintype.card R).choose m : ℝ) := by
  rw [measureReal_def, bipartiteDegreeLaw_atom a b m hs, ENNReal.toReal_div]
  simp

theorem graphBinomialLaw_atom_pos {n m : ℕ} (d : Fin n → ℕ)
    (hd : ∀ i, d i ≤ n - 1) (hs : ∑ i, d i = 2 * m) :
    0 < (graphBinomialLaw (Fin n) m).real {d} := by
  have hm : 2 * m ≤ n * (n - 1) := by
    calc
      _ = ∑ i, d i := hs.symm
      _ ≤ ∑ _ : Fin n, (n - 1) := Finset.sum_le_sum (fun i _ => hd i)
      _ = _ := by simp
  rw [graphBinomialLaw_atom m d (by simpa using hm) hs]
  apply div_pos
  · exact Finset.prod_pos fun i _ => by
      exact_mod_cast Nat.choose_pos (by simpa using hd i)
  · exact_mod_cast Nat.choose_pos (by simpa using hm)

theorem bipartiteBinomialLaw_atom_pos {ell n m : ℕ}
    (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, a i ≤ n) (hb : ∀ j, b j ≤ ell)
    (hsa : ∑ i, a i = m) (hsb : ∑ j, b j = m) :
    0 < (bipartiteBinomialLaw (Fin ell) (Fin n) m).real {(a, b)} := by
  have hm : m ≤ ell * n := by
    calc
      _ = ∑ i, a i := hsa.symm
      _ ≤ ∑ _ : Fin ell, n := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  rw [bipartiteBinomialLaw_atom m a b (by simpa using hm) hsa hsb]
  apply div_pos
  · apply mul_pos
    · exact Finset.prod_pos fun i _ => by
        exact_mod_cast Nat.choose_pos (by simpa using ha i)
    · exact Finset.prod_pos fun j _ => by
        exact_mod_cast Nat.choose_pos (by simpa using hb j)
  · exact sq_pos_of_pos (by exact_mod_cast Nat.choose_pos (by simpa using hm))

theorem graphFamily_nonempty_of_enumeration {n m : ℕ} {α δ : ℝ}
    (d : Fin n → ℕ) (hd : GraphSourceData α n m d) (hδ : δ < 1)
    (h : RelativeApproximation δ ((graphDegreeLaw (Fin n) m).real {d})
      ((graphBinomialLaw (Fin n) m).real {d} * graphCorrection m d)) :
    (graphFamily d).Nonempty := by
  have hpos := h.pos hδ (mul_pos (graphBinomialLaw_atom_pos d hd.1 hd.2.1)
    (Real.exp_pos _))
  rw [graphDegreeLaw_real_atom d m hd.2.1] at hpos
  have hc : 0 < (graphCount d : ℝ) := by
    have hden : 0 ≤ (((Fintype.card (Fin n)).choose 2).choose m : ℝ) := by positivity
    exact (div_pos_iff.mp hpos).resolve_right (fun h => not_lt_of_ge hden h.2) |>.1
  exact (Set.ncard_pos (Set.toFinite _)).mp (by exact_mod_cast hc)

theorem bipartiteFamily_nonempty_of_enumeration {ell n m : ℕ} {α δ : ℝ}
    (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (hd : BipartiteSourceData α ell n m a b) (hδ : δ < 1)
    (h : RelativeApproximation δ ((bipartiteDegreeLaw (Fin ell) (Fin n) m).real {(a, b)})
      ((bipartiteBinomialLaw (Fin ell) (Fin n) m).real {(a, b)} *
        bipartiteCorrection m a b)) : (bipartiteFamily a b).Nonempty := by
  have hpos := h.pos hδ (mul_pos
    (bipartiteBinomialLaw_atom_pos a b hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1)
    (Real.exp_pos _))
  rw [bipartiteDegreeLaw_real_atom a b m hd.2.2.1] at hpos
  have hc : 0 < (bipartiteCount a b : ℝ) := by
    have hden : 0 ≤ ((Fintype.card (Fin ell) * Fintype.card (Fin n)).choose m : ℝ) := by
      positivity
    exact (div_pos_iff.mp hpos).resolve_right (fun h => not_lt_of_ge hden h.2) |>.1
  exact (Set.ncard_pos (Set.toFinite _)).mp (by exact_mod_cast hc)

end MajorityDynamics.Literature.DegreeEnumeration
