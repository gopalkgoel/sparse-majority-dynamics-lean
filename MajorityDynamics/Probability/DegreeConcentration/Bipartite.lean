import MajorityDynamics.Probability.DegreeConcentration.Sites
import MajorityDynamics.Probability.DegreeConcentration.Product
import MajorityDynamics.Probability.DegreeConcentration.Cut
import MajorityDynamics.Probability.DegreeConcentration.Graph

/-!
# Lemma A.10(ii) for every positive density, and the simple-graph interpretation

`bipartite_bound`: for `n ≥ 2`, `p ∈ (0,1]`, `T > 1`, an integer `ℓ ∈ [T⁻¹ n, T n]`,
and `C ≥ 20 T² (K + T)`,

  `P_{G(ℓ,n,p)}[(∑ᵢ (sᵢ - s̄)² ≥ C p ℓ n ∨ ∑ⱼ (tⱼ - t̄)² ≥ C p ℓ n) ∧ 𝒦_{ℓ,n}] ≤ e^{-K n}`.

The left degrees are the counts of the pairwise disjoint row blocks `{i} × [n]`, hence
independent `Bin(n,p)`; the right degrees are the counts of the disjoint column blocks,
hence independent `Bin(ℓ,p)`. The two side families are *not* jointly independent and are
not claimed to be: the two side failures are combined by a union bound. `eq:trunc-mgf` is
applied with `B = T p n`, which dominates both `n p` and `ℓ p`.

The second half of the file identifies the cross-edge model with a simple bipartite graph
on `Fin ℓ ⊕ Fin n`: `bipartiteGraph` is injective, has no same-side edges, and its vertex
degrees are exactly the side degrees, so the same probability bound holds for the graph law
`bipartiteGraphLaw` and the event written with `SimpleGraph.degree`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval Set Finset
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.DegreeConcentration

variable {ℓ n : ℕ}

/-- The cross-edge set read off a site configuration. -/
def edgesOf (ω : Fin ℓ × Fin n → Prop) : CrossEdges ℓ n := {x | ω x}

theorem measurable_edgesOf : Measurable (edgesOf (ℓ := ℓ) (n := n)) := by
  unfold edgesOf
  fun_prop

theorem bipartiteLaw_eq_map (p : I) :
    bipartiteLaw ℓ n p = (siteLaw (Set.univ : Set (Fin ℓ × Fin n)) p).map edgesOf :=
  setBernoulli_eq_map_siteLaw _ p

/-- The row block `{i} × [n]`. -/
def rowBlock (n : ℕ) (i : Fin ℓ) : Finset (Fin ℓ × Fin n) :=
  Finset.univ.map ⟨fun j ↦ (i, j), fun _ _ h ↦ (Prod.mk.inj h).2⟩

/-- The column block `[ℓ] × {j}`. -/
def colBlock (ℓ : ℕ) (j : Fin n) : Finset (Fin ℓ × Fin n) :=
  Finset.univ.map ⟨fun i ↦ (i, j), fun _ _ h ↦ (Prod.mk.inj h).1⟩

theorem card_rowBlock (i : Fin ℓ) : (rowBlock n i).card = n := by
  simp [rowBlock]

theorem card_colBlock (j : Fin n) : (colBlock ℓ j).card = ℓ := by
  simp [colBlock]

theorem mem_rowBlock {i : Fin ℓ} {x : Fin ℓ × Fin n} : x ∈ rowBlock n i ↔ x.1 = i := by
  unfold rowBlock
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, _, rfl⟩; rfl
  · intro h
    refine ⟨x.2, Finset.mem_univ _, ?_⟩
    show (i, x.2) = x
    exact Prod.ext h.symm rfl

theorem mem_colBlock {j : Fin n} {x : Fin ℓ × Fin n} : x ∈ colBlock ℓ j ↔ x.2 = j := by
  unfold colBlock
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i, _, rfl⟩; rfl
  · intro h
    refine ⟨x.1, Finset.mem_univ _, ?_⟩
    show (x.1, j) = x
    exact Prod.ext rfl h.symm

theorem rowBlock_disjoint {i i' : Fin ℓ} (h : i ≠ i') :
    Disjoint (rowBlock n i) (rowBlock n i') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_rowBlock] at hx hx'
  exact h (hx.symm.trans hx')

theorem colBlock_disjoint {j j' : Fin n} (h : j ≠ j') :
    Disjoint (colBlock ℓ j) (colBlock ℓ j') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_colBlock] at hx hx'
  exact h (hx.symm.trans hx')

open Classical in
theorem leftDegree_edgesOf (ω : Fin ℓ × Fin n → Prop) (i : Fin ℓ) :
    leftDegree (edgesOf ω) i = (blockCount (rowBlock n i) ω : ℝ) := by
  rw [blockCount_eq_card, rowBlock, Finset.filter_map, Finset.card_map]
  unfold leftDegree
  congr 2

open Classical in
theorem rightDegree_edgesOf (ω : Fin ℓ × Fin n → Prop) (j : Fin n) :
    rightDegree (edgesOf ω) j = (blockCount (colBlock ℓ j) ω : ℝ) := by
  rw [blockCount_eq_card, colBlock, Finset.filter_map, Finset.card_map]
  unfold rightDegree
  congr 2

/-- `∑ᵢ (sᵢ - s̄)² ≤ ∑ᵢ (sᵢ - a)²`. -/
theorem leftSquareSum_le (E : CrossEdges ℓ n) (a : ℝ) :
    leftSquareSum E ≤ ∑ i, (leftDegree E i - a) ^ 2 := by
  have := sum_sq_mean_le (leftDegree E) a
  rw [Fintype.card_fin] at this
  exact this

/-- `∑ⱼ (tⱼ - t̄)² ≤ ∑ⱼ (tⱼ - a)²`. -/
theorem rightSquareSum_le (E : CrossEdges ℓ n) (a : ℝ) :
    rightSquareSum E ≤ ∑ j, (rightDegree E j - a) ^ 2 := by
  have := sum_sq_mean_le (rightDegree E) a
  rw [Fintype.card_fin] at this
  exact this

/-- The left-side estimate: `P[∑ᵢ (sᵢ - s̄)² ≥ C p ℓ n ∧ 𝒦] ≤ exp(-C ℓ/(20T) + ℓ/2)`. -/
theorem left_bound (hn : 0 < n) (p : I) (hp : 0 < (p : ℝ)) (T : ℝ) (hT : 1 ≤ T) (C : ℝ) :
    (siteLaw (Set.univ : Set (Fin ℓ × Fin n)) p)
      {ω | C * p * ℓ * n ≤ leftSquareSum (edgesOf ω) ∧ edgesOf ω ∈ bipartiteTruncation ℓ n p} ≤
      ENNReal.ofReal (Real.exp (-(C * ℓ) / (20 * T) + (ℓ : ℝ) / 2)) := by
  classical
  set P := siteLaw (Set.univ : Set (Fin ℓ × Fin n)) p with hP
  let X : Fin ℓ → (Fin ℓ × Fin n → Prop) → ℕ := fun i ω ↦ blockCount (rowBlock n i) ω
  let r : Fin ℓ → ℕ := fun _ ↦ n
  have hpn : 0 < (p : ℝ) * n := mul_pos hp (by exact_mod_cast hn)
  have hB : 0 < T * ((p : ℝ) * n) := mul_pos (by linarith) hpn
  have hr : ∀ i, (r i : ℝ) * p ≤ T * ((p : ℝ) * n) := fun i ↦ by
    simp only [r]
    nlinarith
  have hX : ∀ i, Measurable (X i) := fun i ↦ measurable_of_countable _
  have hlaw : ∀ i, P.map (X i) = binomial (r i) p := fun i ↦ by
    simp only [X, r, hP]
    rw [siteLaw_map_blockCount _ p _ (Set.subset_univ _), card_rowBlock]
  have hind : iIndepFun X P :=
    blockCount_iIndepFun _ p (fun i ↦ rowBlock n i) fun _ _ hne ↦ rowBlock_disjoint hne
  have hsub : {ω | C * p * ℓ * n ≤ leftSquareSum (edgesOf ω) ∧
        edgesOf ω ∈ bipartiteTruncation ℓ n p} ⊆
      truncatedSpread X r p (T * ((p : ℝ) * n)) (C * p * ℓ * n) := by
    intro ω ⟨hspread, htrunc⟩
    obtain ⟨hleft, _⟩ := htrunc
    have hsum : ∑ i, (leftDegree (edgesOf ω) i - p * n) ^ 2 =
        ∑ i, ((X i ω : ℝ) - r i * p) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [X, r]
      rw [leftDegree_edgesOf, mul_comm (n : ℝ)]
    refine ⟨hsum ▸ hspread.trans (leftSquareSum_le _ _), fun i ↦ ?_⟩
    simp only [X, r]
    rw [← leftDegree_edgesOf, mul_comm (n : ℝ)]
    refine (hleft i).trans ?_
    nlinarith
  calc P _ ≤ P (truncatedSpread X r p (T * ((p : ℝ) * n)) (C * p * ℓ * n)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(C * p * ℓ * n) / (20 * (T * ((p : ℝ) * n))) +
          (Fintype.card (Fin ℓ) : ℝ) / 2)) :=
        truncated_square_bound P X r p _ _ hB hr hX hlaw hind
    _ = ENNReal.ofReal (Real.exp (-(C * ℓ) / (20 * T) + (ℓ : ℝ) / 2)) := by
        rw [Fintype.card_fin]
        congr 3
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring

/-- The right-side estimate: `P[∑ⱼ (tⱼ - t̄)² ≥ C p ℓ n ∧ 𝒦] ≤ exp(-C ℓ/(20T) + n/2)`. -/
theorem right_bound (hn : 0 < n) (p : I) (hp : 0 < (p : ℝ)) (T : ℝ) (hT : 1 ≤ T)
    (hℓ : (ℓ : ℝ) ≤ T * n) (C : ℝ) :
    (siteLaw (Set.univ : Set (Fin ℓ × Fin n)) p)
      {ω | C * p * ℓ * n ≤ rightSquareSum (edgesOf ω) ∧ edgesOf ω ∈ bipartiteTruncation ℓ n p} ≤
      ENNReal.ofReal (Real.exp (-(C * ℓ) / (20 * T) + (n : ℝ) / 2)) := by
  classical
  set P := siteLaw (Set.univ : Set (Fin ℓ × Fin n)) p with hP
  let X : Fin n → (Fin ℓ × Fin n → Prop) → ℕ := fun j ω ↦ blockCount (colBlock ℓ j) ω
  let r : Fin n → ℕ := fun _ ↦ ℓ
  have hpn : 0 < (p : ℝ) * n := mul_pos hp (by exact_mod_cast hn)
  have hB : 0 < T * ((p : ℝ) * n) := mul_pos (by linarith) hpn
  have hr : ∀ j, (r j : ℝ) * p ≤ T * ((p : ℝ) * n) := fun j ↦ by
    simp only [r]
    nlinarith
  have hX : ∀ j, Measurable (X j) := fun j ↦ measurable_of_countable _
  have hlaw : ∀ j, P.map (X j) = binomial (r j) p := fun j ↦ by
    simp only [X, r, hP]
    rw [siteLaw_map_blockCount _ p _ (Set.subset_univ _), card_colBlock]
  have hind : iIndepFun X P :=
    blockCount_iIndepFun _ p (fun j ↦ colBlock ℓ j) fun _ _ hne ↦ colBlock_disjoint hne
  have hsub : {ω | C * p * ℓ * n ≤ rightSquareSum (edgesOf ω) ∧
        edgesOf ω ∈ bipartiteTruncation ℓ n p} ⊆
      truncatedSpread X r p (T * ((p : ℝ) * n)) (C * p * ℓ * n) := by
    intro ω ⟨hspread, htrunc⟩
    obtain ⟨_, hright⟩ := htrunc
    have hsum : ∑ j, (rightDegree (edgesOf ω) j - p * ℓ) ^ 2 =
        ∑ j, ((X j ω : ℝ) - r j * p) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [X, r]
      rw [rightDegree_edgesOf, mul_comm (ℓ : ℝ)]
    refine ⟨hsum ▸ hspread.trans (rightSquareSum_le _ _), fun j ↦ ?_⟩
    simp only [X, r]
    rw [← rightDegree_edgesOf, mul_comm (ℓ : ℝ)]
    refine (hright j).trans ?_
    nlinarith
  calc P _ ≤ P (truncatedSpread X r p (T * ((p : ℝ) * n)) (C * p * ℓ * n)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(C * p * ℓ * n) / (20 * (T * ((p : ℝ) * n))) +
          (Fintype.card (Fin n) : ℝ) / 2)) :=
        truncated_square_bound P X r p _ _ hB hr hX hlaw hind
    _ = ENNReal.ofReal (Real.exp (-(C * ℓ) / (20 * T) + (n : ℝ) / 2)) := by
        rw [Fintype.card_fin]
        congr 3
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring

/-- Lemma A.10(ii) for every `n ≥ 2`, `p ∈ (0,1]`, `T > 1`, integer `ℓ ∈ [T⁻¹ n, T n]`,
and `C ≥ 20 T² (K + T)`. -/
theorem bipartite_bound (hn : 2 ≤ n) (p : I) (hp : 0 < (p : ℝ)) (T : ℝ) (hT : 1 < T)
    (hℓ : sizeRange T n ℓ) (C K : ℝ) (hK : 0 ≤ K) (hC : 20 * T ^ 2 * (K + T) ≤ C) :
    bipartiteLaw ℓ n p (bipartiteBad ℓ n C p) ≤ failureBound K n := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨hℓ1, hℓ2⟩ := hℓ
  have hT0 : 0 < T := by linarith
  have hTn : (n : ℝ) ≤ T * ℓ := by
    have := mul_le_mul_of_nonneg_left hℓ1 hT0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hT0.ne', one_mul] at this
  have hC0 : 0 ≤ C := by
    have : 0 ≤ 20 * T ^ 2 * (K + T) := by positivity
    linarith
  set P := siteLaw (Set.univ : Set (Fin ℓ × Fin n)) p with hP
  rw [bipartiteLaw_eq_map, Measure.map_apply measurable_edgesOf (Set.to_countable _).measurableSet]
  have hcover : edgesOf ⁻¹' bipartiteBad ℓ n C p ⊆
      {ω | C * p * ℓ * n ≤ leftSquareSum (edgesOf ω) ∧ edgesOf ω ∈ bipartiteTruncation ℓ n p} ∪
      {ω | C * p * ℓ * n ≤ rightSquareSum (edgesOf ω) ∧ edgesOf ω ∈ bipartiteTruncation ℓ n p} := by
    intro ω ⟨hspread, htrunc⟩
    rcases hspread with h | h
    · exact Or.inl ⟨h, htrunc⟩
    · exact Or.inr ⟨h, htrunc⟩
  -- the common exponent
  have hexp1 : -(C * ℓ) / (20 * T) + (ℓ : ℝ) / 2 ≤ -(C * n) / (20 * T ^ 2) + T * n / 2 := by
    have h1 : C * n / (20 * T ^ 2) ≤ C * ℓ / (20 * T) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hTn hC0, mul_nonneg hC0 (by positivity : (0:ℝ) ≤ T * ℓ)]
    have h2 : (ℓ : ℝ) / 2 ≤ T * n / 2 := by linarith
    rw [neg_div, neg_div]
    linarith
  have hexp2 : -(C * ℓ) / (20 * T) + (n : ℝ) / 2 ≤ -(C * n) / (20 * T ^ 2) + T * n / 2 := by
    have h1 : C * n / (20 * T ^ 2) ≤ C * ℓ / (20 * T) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hTn hC0, mul_nonneg hC0 (by positivity : (0:ℝ) ≤ T * ℓ)]
    have h2 : (n : ℝ) / 2 ≤ T * n / 2 := by nlinarith
    rw [neg_div, neg_div]
    linarith
  have hfinal : 2 * Real.exp (-(C * n) / (20 * T ^ 2) + T * n / 2) ≤ Real.exp (-K * n) := by
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
      linarith
    rw [show (2 : ℝ) * Real.exp (-(C * n) / (20 * T ^ 2) + T * n / 2) =
        Real.exp (Real.log 2 + (-(C * n) / (20 * T ^ 2) + T * n / 2)) by
      rw [Real.exp_add (Real.log 2), Real.exp_log two_pos]]
    apply Real.exp_le_exp.mpr
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hCT : K + T ≤ C / (20 * T ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hkey : (C * n) / (20 * T ^ 2) = n * (C / (20 * T ^ 2)) := by ring
    rw [neg_div, hkey]
    nlinarith [mul_le_mul_of_nonneg_left hCT (Nat.cast_nonneg n),
      mul_le_mul_of_nonneg_right hT.le (Nat.cast_nonneg n)]
  calc P (edgesOf ⁻¹' bipartiteBad ℓ n C p)
      ≤ P ({ω | C * p * ℓ * n ≤ leftSquareSum (edgesOf ω) ∧
            edgesOf ω ∈ bipartiteTruncation ℓ n p} ∪
          {ω | C * p * ℓ * n ≤ rightSquareSum (edgesOf ω) ∧
            edgesOf ω ∈ bipartiteTruncation ℓ n p}) := measure_mono hcover
    _ ≤ P {ω | C * p * ℓ * n ≤ leftSquareSum (edgesOf ω) ∧
            edgesOf ω ∈ bipartiteTruncation ℓ n p} +
          P {ω | C * p * ℓ * n ≤ rightSquareSum (edgesOf ω) ∧
            edgesOf ω ∈ bipartiteTruncation ℓ n p} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(C * ℓ) / (20 * T) + (ℓ : ℝ) / 2)) +
          ENNReal.ofReal (Real.exp (-(C * ℓ) / (20 * T) + (n : ℝ) / 2)) :=
        add_le_add (left_bound hn0 p hp T hT.le C) (right_bound hn0 p hp T hT.le hℓ2 C)
    _ = ENNReal.ofReal (Real.exp (-(C * ℓ) / (20 * T) + (ℓ : ℝ) / 2) +
          Real.exp (-(C * ℓ) / (20 * T) + (n : ℝ) / 2)) :=
        (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
    _ ≤ failureBound K n := by
        unfold failureBound
        apply ENNReal.ofReal_le_ofReal
        have e1 := Real.exp_le_exp.mpr hexp1
        have e2 := Real.exp_le_exp.mpr hexp2
        linarith

/-! ### The simple-graph interpretation of `G(ℓ,n,p)` -/

theorem bipartiteGraph_adj_inl_inr (E : CrossEdges ℓ n) (i : Fin ℓ) (j : Fin n) :
    (bipartiteGraph E).Adj (Sum.inl i) (Sum.inr j) ↔ (i, j) ∈ E := by
  simp only [bipartiteGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Sym2.eq_iff,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false, or_false,
    ne_eq, not_false_eq_true, and_true]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl, rfl⟩
    exact hab
  · intro h
    exact ⟨(i, j), h, rfl, rfl⟩

theorem bipartiteGraph_not_adj_inl_inl (E : CrossEdges ℓ n) (i i' : Fin ℓ) :
    ¬ (bipartiteGraph E).Adj (Sum.inl i) (Sum.inl i') := by
  simp [bipartiteGraph, SimpleGraph.fromEdgeSet_adj]

theorem bipartiteGraph_not_adj_inr_inr (E : CrossEdges ℓ n) (j j' : Fin n) :
    ¬ (bipartiteGraph E).Adj (Sum.inr j) (Sum.inr j') := by
  simp [bipartiteGraph, SimpleGraph.fromEdgeSet_adj]

/-- Every cross-edge set is determined by its graph. -/
theorem bipartiteGraph_injective : Function.Injective (bipartiteGraph (ℓ := ℓ) (n := n)) := by
  intro E E' h
  ext ⟨i, j⟩
  rw [← bipartiteGraph_adj_inl_inr, ← bipartiteGraph_adj_inl_inr, h]

theorem measurable_bipartiteGraph : Measurable (bipartiteGraph (ℓ := ℓ) (n := n)) :=
  measurable_of_countable _

open Classical in
/-- The degree of a left vertex in the bipartite graph is its left degree. -/
theorem degree_inl (E : CrossEdges ℓ n) (i : Fin ℓ) :
    ((bipartiteGraph E).degree (Sum.inl i) : ℝ) = leftDegree E i := by
  unfold leftDegree
  congr 1
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (bipartiteGraph E).neighborFinset (Sum.inl i) =
      (Finset.univ.filter fun j : Fin n ↦ (i, j) ∈ E).map Function.Embedding.inr := by
    ext y
    rcases y with i' | j
    · simp [bipartiteGraph_not_adj_inl_inl]
    · simp [bipartiteGraph_adj_inl_inr]
  rw [this, Finset.card_map]

open Classical in
/-- The degree of a right vertex in the bipartite graph is its right degree. -/
theorem degree_inr (E : CrossEdges ℓ n) (j : Fin n) :
    ((bipartiteGraph E).degree (Sum.inr j) : ℝ) = rightDegree E j := by
  unfold rightDegree
  congr 1
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (bipartiteGraph E).neighborFinset (Sum.inr j) =
      (Finset.univ.filter fun i : Fin ℓ ↦ (i, j) ∈ E).map Function.Embedding.inl := by
    ext y
    rcases y with i | j'
    · simp [(bipartiteGraph E).adj_comm, bipartiteGraph_adj_inl_inr]
    · simp [bipartiteGraph_not_adj_inr_inr]
  rw [this, Finset.card_map]

theorem preimage_bipartiteGraphBad (C p : ℝ) :
    bipartiteGraph ⁻¹' bipartiteGraphBad ℓ n C p = bipartiteBad ℓ n C p := by
  ext E
  simp only [Set.mem_preimage, bipartiteGraphBad, bipartiteBad, bipartiteSpread,
    bipartiteTruncation, Set.mem_inter_iff, Set.mem_ofPred_eq, leftSquareSum, rightSquareSum,
    leftDegreeMean, rightDegreeMean, degree_inl, degree_inr]

/-- The probability of the event of Lemma A.10(ii) is the same for the cross-edge model and for
the simple bipartite graph law on `Fin ℓ ⊕ Fin n`. -/
theorem bipartiteGraphLaw_bad (p : I) (C : ℝ) :
    bipartiteGraphLaw ℓ n p (bipartiteGraphBad ℓ n C p) = bipartiteLaw ℓ n p (bipartiteBad ℓ n C p) := by
  rw [bipartiteGraphLaw, Measure.map_apply measurable_bipartiteGraph
    (Set.to_countable _).measurableSet, preimage_bipartiteGraphBad]

end MajorityDynamics.Probability.DegreeConcentration
