import MajorityDynamics.Probability.HypergeometricTiltTail.Basic

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail

/-- The graph population omits the distinguished vertex, while its normalization
retains the original ambient size. -/
def graphFactor {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (S : Finset V) (d t : ℤ) (p : ℝ) (β : V → ℝ) : ℝ :=
  weightedFactor (Finset.univ.erase v) (S.erase v) d t p (Fintype.card V) β

/-- The bipartite population is the entire opposite side; `L` is the size of the
side containing the distinguished vertex. -/
def bipartiteFactor {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (d t : ℤ) (p L : ℝ) (β : V → ℝ) : ℝ :=
  weightedFactor Finset.univ S d t p L β

theorem erase_subset_population {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (S : Finset V) : S.erase v ⊆ Finset.univ.erase v := by
  intro x hx
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩

theorem erased_population_card {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) : (Finset.univ.erase v).card = Fintype.card V - 1 := by
  simp

theorem erased_part_card {V : Type*} [DecidableEq V]
    (v : V) (S : Finset V) : (S.erase v).card = S.card - if v ∈ S then 1 else 0 := by
  by_cases hv : v ∈ S
  · simp [hv, Finset.card_erase_of_mem hv]
  · simp [hv]

theorem erased_part_card_close {V : Type*} [DecidableEq V]
    (v : V) (S : Finset V) : |((S.erase v).card : ℝ) - S.card| ≤ 1 := by
  by_cases hv : v ∈ S
  · have h := Finset.card_erase_add_one hv
    have hr : ((S.erase v).card : ℝ) + 1 = S.card := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith : ((S.erase v).card : ℝ) - S.card ≤ 0)]
    linarith
  · simp [Finset.erase_eq_of_notMem hv]

theorem erased_population_card_close {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) : |((Finset.univ.erase v).card : ℝ) - Fintype.card V| ≤ 1 := by
  simpa using erased_part_card_close v Finset.univ

theorem erased_population_sdiff {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (S : Finset V) :
    Finset.univ.erase v \ S = Finset.univ \ insert v S := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_insert, true_and]
  tauto

theorem erased_part_complement {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (S : Finset V) :
    Finset.univ.erase v \ S.erase v = Finset.univ \ insert v S := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_insert, true_and]
  tauto

theorem erased_complement_card {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (S : Finset V) :
    (Finset.univ \ insert v S).card =
      Fintype.card V - S.card - if v ∉ S then 1 else 0 := by
  have he : Finset.univ \ insert v S = (Finset.univ \ S).erase v := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ,
      Finset.mem_insert, true_and]
    tauto
  rw [he, erased_part_card]
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ S)]

/-- Exact graph weight: the unselected sum excludes the distinguished vertex. -/
theorem graph_tiltWeight_eq {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (R : Finset V) (p : ℝ) (β : V → ℝ) :
    tiltWeight (Finset.univ.erase v) R p (Fintype.card V) β =
      (∑ x ∈ R, β x) / Real.sqrt (p * Fintype.card V) -
        (∑ x ∈ Finset.univ \ insert v R, β x) *
          Real.sqrt (p * Fintype.card V) / Fintype.card V := by
  simp only [tiltWeight, erased_population_sdiff]

/-- Exact bipartite weight, using the normalization on the distinguished side. -/
theorem bipartite_tiltWeight_eq {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (p L : ℝ) (β : V → ℝ) :
    tiltWeight Finset.univ R p L β =
      (∑ x ∈ R, β x) / Real.sqrt (p * L) -
        (∑ x ∈ Finset.univ \ R, β x) * Real.sqrt (p * L) / L := rfl

/-- The graph adapter has the literal deleted-vertex hypergeometric coefficients
and the actual two independent fixed-size subset averages. -/
theorem graphFactor_eq {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (S : Finset V) {d t : ℤ} (ht : 0 ≤ t) (_htd : t ≤ d)
    (p : ℝ) (β : V → ℝ) :
    graphFactor v S d t p β =
      (((S.card - if v ∈ S then 1 else 0).choose t.toNat : ℝ) *
        ((Fintype.card V - S.card - if v ∉ S then 1 else 0).choose (d-t).toNat : ℝ) /
        ((Fintype.card V - 1).choose d.toNat : ℝ)) *
      subsetAverage (S.erase v) t.toNat (fun R =>
        subsetAverage (Finset.univ \ insert v S) (d-t).toNat (fun Q =>
          Real.exp ((∑ x ∈ R ∪ Q, β x) / Real.sqrt (p * Fintype.card V) -
            (∑ x ∈ Finset.univ \ insert v (R ∪ Q), β x) *
              Real.sqrt (p * Fintype.card V) / Fintype.card V))) := by
  have hnat : d.toNat - t.toNat = (d-t).toNat := by omega
  unfold graphFactor weightedFactor hypergeomMass tiltExpectation
  rw [← Finset.card_sdiff_of_subset (erase_subset_population v S),
    erased_part_complement, erased_complement_card, erased_population_card,
    erased_part_card, hnat]
  simp only [graph_tiltWeight_eq]

/-- The bipartite adapter retains the ordinary two-side hypergeometric law and
the possibly different distinguished-side normalization. -/
theorem bipartiteFactor_eq {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {d t : ℤ} (ht : 0 ≤ t) (_htd : t ≤ d)
    (p L : ℝ) (β : V → ℝ) :
    bipartiteFactor S d t p L β =
      ((S.card.choose t.toNat : ℝ) *
        ((Fintype.card V - S.card).choose (d-t).toNat : ℝ) /
        ((Fintype.card V).choose d.toNat : ℝ)) *
      subsetAverage S t.toNat (fun R =>
        subsetAverage (Finset.univ \ S) (d-t).toNat (fun Q =>
          Real.exp ((∑ x ∈ R ∪ Q, β x) / Real.sqrt (p * L) -
            (∑ x ∈ Finset.univ \ (R ∪ Q), β x) * Real.sqrt (p * L) / L))) := by
  have hnat : d.toNat - t.toNat = (d-t).toNat := by omega
  simp only [bipartiteFactor, weightedFactor, hypergeomMass, tiltExpectation,
    Finset.card_univ, hnat, tiltWeight]

end MajorityDynamics.Probability.HypergeometricTiltTail
