import MajorityDynamics.Probability.DegreeConcentration.Sites
import MajorityDynamics.Probability.DegreeConcentration.Product
import MajorityDynamics.Probability.DegreeConcentration.Cut

/-!
# Lemma A.10(i) for every positive density

`graph_bound`: for every `n ≥ 1`, every `p ∈ (0,1]`, every `K` and every `C ≥ 160 (K+2)`,

  `P_{G(n,p)}[∑ᵢ (dᵢ - d̄)² ≥ C p n² ∧ ∀ i, |dᵢ - p n| ≤ p n] ≤ e^{-K n}`.

Route (the manuscript's): the empirical variance is at most `∑ᵢ (dᵢ - p(n-1))²`
(`sum_sq_mean_le`); the random-cut covering (`exists_cut_of_spread`) places the spread
event inside `⋃_S E_S` with `E_S = {∑_{v∉S} (deg_S v - p|S|)² ≥ C p n²/8}`; for a fixed `S`
the cut degrees `deg_S v`, `v ∉ S`, are the counts of the pairwise disjoint edge blocks
`{v} × S`, hence independent `Bin(|S|, p)` (`Sites.lean`); on the truncation event they
satisfy `|deg_S v - p|S|| ≤ 2 p n`, so `eq:trunc-mgf` with `B = p n`, `t = C p n²/8`,
`q ≤ n` gives `P[E_S ∩ 𝒦] ≤ exp(-C n/160 + n/2)`; a union bound over the `2^n` cuts finishes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval Set Finset
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.DegreeConcentration

/-- Simple graphs on a countable vertex type have measurable singletons (the measurable
structure is pulled back from the edge set). -/
instance simpleGraph_measurableSingletonClass (V : Type*) [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    have he : ({G} : Set (SimpleGraph V)) = SimpleGraph.edgeSet ⁻¹' {G.edgeSet} := by
      ext H
      simp [SimpleGraph.edgeSet_injective.eq_iff]
    rw [he]
    exact SimpleGraph.measurable_edgeSet (measurableSet_singleton _)

variable {n : ℕ}

/-- The graph read off a site configuration. -/
def graphOf (ω : Sym2 (Fin n) → Prop) : Graph n := SimpleGraph.fromEdgeSet {e | ω e}

theorem measurable_graphOf : Measurable (graphOf (n := n)) :=
  SimpleGraph.measurable_fromEdgeSet.comp (by fun_prop)

theorem graphLaw_eq_map (p : I) :
    graphLaw n p = (siteLaw (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) p).map graphOf :=
  binomialRandom_eq_map_siteLaw (Fin n) p

/-- The edge block `{v} × S` of a vertex `v`, as a finset of potential edges. -/
def edgeBlock (S : Finset (Fin n)) (v : Fin n) : Finset (Sym2 (Fin n)) :=
  S.map ⟨fun w ↦ s(v, w), fun _ _ h ↦ Sym2.congr_right.mp h⟩

theorem card_edgeBlock (S : Finset (Fin n)) (v : Fin n) : (edgeBlock S v).card = S.card :=
  Finset.card_map _

theorem mem_edgeBlock {S : Finset (Fin n)} {v : Fin n} {e : Sym2 (Fin n)} :
    e ∈ edgeBlock S v ↔ ∃ w ∈ S, s(v, w) = e := by
  unfold edgeBlock
  rw [Finset.mem_map]
  rfl

theorem edgeBlock_subset_compl_diagSet (S : Finset (Fin n)) (v : Fin n) (hv : v ∉ S) :
    (edgeBlock S v : Set (Sym2 (Fin n))) ⊆ Sym2.diagSetᶜ := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := mem_edgeBlock.mp (Finset.mem_coe.mp he)
  simp only [Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  rintro rfl
  exact hv hw

theorem edgeBlock_disjoint (S : Finset (Fin n)) {v v' : Fin n} (hv : v ∉ S) (hne : v ≠ v') :
    Disjoint (edgeBlock S v) (edgeBlock S v') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨w, hw, rfl⟩ := mem_edgeBlock.mp he
  obtain ⟨w', hw', h⟩ := mem_edgeBlock.mp he'
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hne h1.symm
  · subst h2
    exact hv hw'

open Classical in
/-- For `v ∉ S`, the cut degree of `v` into `S` is the count of the edge block `{v} × S`. -/
theorem cutDegree_graphOf (S : Finset (Fin n)) (v : Fin n) (hv : v ∉ S)
    (ω : Sym2 (Fin n) → Prop) : cutDegree (graphOf ω) S v = blockCount (edgeBlock S v) ω := by
  rw [blockCount_eq_card, edgeBlock, Finset.filter_map, Finset.card_map]
  unfold cutDegree
  congr 1
  refine Finset.filter_congr fun w hw ↦ ?_
  simp only [graphOf, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq, Function.comp]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun hvw ↦ hv (hvw ▸ hw)⟩

/-- `∑ᵢ (dᵢ - d̄)² ≤ ∑ᵢ (dᵢ - p(n-1))²`. -/
theorem graphSquareSum_le (G : Graph n) (p : ℝ) :
    graphSquareSum G ≤ ∑ i, (graphDegree G i - p * ((n : ℝ) - 1)) ^ 2 := by
  have := sum_sq_mean_le (graphDegree G) (p * ((n : ℝ) - 1))
  rw [Fintype.card_fin] at this
  exact this

open Classical in
theorem graphDegree_eq (G : Graph n) (i : Fin n) : graphDegree G i = (G.degree i : ℝ) := by
  unfold graphDegree
  congr 1

/-- The per-cut estimate: `P[E_S ∩ 𝒦] ≤ exp(-C n/160 + n/2)`. -/
theorem cut_bound (hn : 0 < n) (p : I) (hp : 0 < (p : ℝ)) (C : ℝ) (S : Finset (Fin n)) :
    (siteLaw (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) p)
      {ω | C * p * (n : ℝ) ^ 2 / 8 ≤
          ∑ v ∈ Sᶜ, ((cutDegree (graphOf ω) S v : ℝ) - p * (S.card : ℝ)) ^ 2 ∧
        ∀ v, |graphDegree (graphOf ω) v - p * n| ≤ p * n} ≤
      ENNReal.ofReal (Real.exp (-(C * n) / 160 + (n : ℝ) / 2)) := by
  classical
  set P := siteLaw (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) p with hP
  -- the independent family: cut degrees of the vertices outside `S`
  let J := {v : Fin n // v ∉ S}
  let X : J → (Sym2 (Fin n) → Prop) → ℕ := fun v ω ↦ blockCount (edgeBlock S v.1) ω
  let r : J → ℕ := fun _ ↦ S.card
  have hB : 0 < (p : ℝ) * n := mul_pos hp (by exact_mod_cast hn)
  have hScard : (S.card : ℝ) ≤ n := by
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hr : ∀ v : J, (r v : ℝ) * p ≤ (p : ℝ) * n := fun v ↦ by
    simp only [r]
    nlinarith
  have hX : ∀ v : J, Measurable (X v) := fun v ↦ measurable_of_countable _
  have hlaw : ∀ v : J, P.map (X v) = binomial (r v) p := fun v ↦ by
    simp only [X, r, hP]
    rw [siteLaw_map_blockCount _ p _ (edgeBlock_subset_compl_diagSet S v.1 v.2), card_edgeBlock]
  have hind : iIndepFun X P :=
    blockCount_iIndepFun _ p (fun v : J ↦ edgeBlock S v.1) fun v v' hne ↦
      edgeBlock_disjoint S v.2 fun h ↦ hne (Subtype.ext h)
  -- the event is contained in the truncated-spread event
  have hsub : {ω | C * p * (n : ℝ) ^ 2 / 8 ≤
          ∑ v ∈ Sᶜ, ((cutDegree (graphOf ω) S v : ℝ) - p * (S.card : ℝ)) ^ 2 ∧
        ∀ v, |graphDegree (graphOf ω) v - p * n| ≤ p * n} ⊆
      truncatedSpread X r p ((p : ℝ) * n) (C * p * (n : ℝ) ^ 2 / 8) := by
    intro ω ⟨hspread, htrunc⟩
    have hsum : ∑ v ∈ Sᶜ, ((cutDegree (graphOf ω) S v : ℝ) - p * (S.card : ℝ)) ^ 2 =
        ∑ v : J, ((X v ω : ℝ) - r v * p) ^ 2 := by
      rw [Finset.sum_subtype Sᶜ (p := fun v ↦ v ∉ S) (fun v ↦ Finset.mem_compl)]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [X, r]
      rw [cutDegree_graphOf S v.1 v.2 ω, mul_comm (S.card : ℝ)]
    refine ⟨hsum ▸ hspread, fun v ↦ ?_⟩
    simp only [X, r]
    rw [← cutDegree_graphOf S v.1 v.2 ω]
    have hdeg := htrunc v.1
    rw [graphDegree_eq] at hdeg
    have hcut : (cutDegree (graphOf ω) S v.1 : ℝ) ≤ ((graphOf ω).degree v.1 : ℝ) := by
      exact_mod_cast cutDegree_le_degree (graphOf ω) S v.1
    have hcut0 : (0 : ℝ) ≤ cutDegree (graphOf ω) S v.1 := Nat.cast_nonneg _
    have hpS : 0 ≤ (S.card : ℝ) * p := by positivity
    have hpS' : (S.card : ℝ) * p ≤ p * n := by nlinarith
    rw [abs_le] at hdeg ⊢
    constructor <;> nlinarith
  calc P _ ≤ P (truncatedSpread X r p ((p : ℝ) * n) (C * p * (n : ℝ) ^ 2 / 8)) :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(C * p * (n : ℝ) ^ 2 / 8) / (20 * ((p : ℝ) * n)) +
          (Fintype.card J : ℝ) / 2)) :=
        truncated_square_bound P X r p ((p : ℝ) * n) _ hB hr hX hlaw hind
    _ ≤ ENNReal.ofReal (Real.exp (-(C * n) / 160 + (n : ℝ) / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hcard : (Fintype.card J : ℝ) ≤ n := by
          have := Fintype.card_subtype_le fun v : Fin n ↦ v ∉ S
          rw [Fintype.card_fin] at this
          exact_mod_cast this
        have hexp : -(C * p * (n : ℝ) ^ 2 / 8) / (20 * ((p : ℝ) * n)) = -(C * n) / 160 := by
          field_simp
          ring
        rw [hexp]
        linarith

/-- Lemma A.10(i) for every `n ≥ 1`, `p ∈ (0,1]`, and `C ≥ 160 (K + 2)`. -/
theorem graph_bound (hn : 0 < n) (p : I) (hp : 0 < (p : ℝ)) (C K : ℝ)
    (hC : 160 * (K + 2) ≤ C) :
    graphLaw n p (graphBad n C p) ≤ failureBound K n := by
  classical
  set P := siteLaw (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) p with hP
  rw [graphLaw_eq_map, Measure.map_apply measurable_graphOf (Set.to_countable _).measurableSet]
  -- covering by the cut events
  have hcover : graphOf ⁻¹' graphBad n C p ⊆
      ⋃ S : Finset (Fin n), {ω : Sym2 (Fin n) → Prop | C * p * (n : ℝ) ^ 2 / 8 ≤
          ∑ v ∈ Sᶜ, ((cutDegree (graphOf ω) S v : ℝ) - p * (S.card : ℝ)) ^ 2 ∧
        ∀ v, |graphDegree (graphOf ω) v - p * n| ≤ p * n} := by
    intro ω hω
    obtain ⟨hspread, htrunc⟩ := hω
    have hspread' : C * p * (n : ℝ) ^ 2 ≤ graphSquareSum (graphOf ω) := hspread
    have h1 : 8 * (C * p * (n : ℝ) ^ 2 / 8) ≤
        ∑ v, (((graphOf ω).degree v : ℝ) - p * ((n : ℝ) - 1)) ^ 2 := by
      have := (graphSquareSum_le (graphOf ω) p)
      simp only [graphDegree_eq] at this
      linarith
    obtain ⟨S, hS⟩ := exists_cut_of_spread (graphOf ω) p _ h1
    exact Set.mem_iUnion.mpr ⟨S, hS, htrunc⟩
  have hcount : (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n := by
    rw [Fintype.card_finset, Fintype.card_fin]
    push_cast
    rfl
  calc P (graphOf ⁻¹' graphBad n C p)
      ≤ P (⋃ S : Finset (Fin n), {ω : Sym2 (Fin n) → Prop | C * p * (n : ℝ) ^ 2 / 8 ≤
          ∑ v ∈ Sᶜ, ((cutDegree (graphOf ω) S v : ℝ) - p * (S.card : ℝ)) ^ 2 ∧
        ∀ v, |graphDegree (graphOf ω) v - p * n| ≤ p * n}) := measure_mono hcover
    _ ≤ ∑' S : Finset (Fin n), P {ω : Sym2 (Fin n) → Prop | C * p * (n : ℝ) ^ 2 / 8 ≤
          ∑ v ∈ Sᶜ, ((cutDegree (graphOf ω) S v : ℝ) - p * (S.card : ℝ)) ^ 2 ∧
        ∀ v, |graphDegree (graphOf ω) v - p * n| ≤ p * n} := measure_iUnion_le _
    _ ≤ ∑' _S : Finset (Fin n), ENNReal.ofReal (Real.exp (-(C * n) / 160 + (n : ℝ) / 2)) :=
        ENNReal.tsum_le_tsum fun S ↦ cut_bound hn p hp C S
    _ = ENNReal.ofReal ((Fintype.card (Finset (Fin n)) : ℝ) *
          Real.exp (-(C * n) / 160 + (n : ℝ) / 2)) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ failureBound K n := by
        unfold failureBound
        apply ENNReal.ofReal_le_ofReal
        rw [hcount]
        have h2 : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log two_pos]
        rw [h2, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hlog : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
          linarith
        have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith

end MajorityDynamics.Probability.DegreeConcentration
