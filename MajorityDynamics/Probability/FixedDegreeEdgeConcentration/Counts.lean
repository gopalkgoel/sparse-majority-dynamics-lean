import MajorityDynamics.Probability.FixedDegreeSampling.Conditioning
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Moments

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

/-- Each unordered pair of distinct vertices occurs exactly once. -/
def internalCandidates (U : Finset V) : Finset (Sym2 V) :=
  U.sym2.filter (fun e => ¬ e.IsDiag)

/-- Symmetric product, well-defined on genuine unordered pairs. -/
def degreeProduct (d : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => d a * d b, fun a b => mul_comm (d a) (d b)⟩

omit [Fintype V] in
@[simp] theorem degreeProduct_mk (d : V → ℝ) (a b : V) :
    degreeProduct d s(a,b) = d a * d b := rfl

omit [Fintype V] in
/-- The exact finite identity includes the missing diagonal. -/
theorem internal_product_sum (d : V → ℝ) (U : Finset V) :
    2 * (∑ e ∈ internalCandidates U, degreeProduct d e) =
      (∑ v ∈ U, d v)^2 - ∑ v ∈ U, (d v)^2 := by
  induction U using Finset.cons_induction with
  | empty => simp [internalCandidates]
  | cons a U ha ih =>
    have hadd : ∑ e ∈ internalCandidates (U.cons a ha), degreeProduct d e =
        d a * (∑ v ∈ U, d v) + ∑ e ∈ internalCandidates U, degreeProduct d e := by
      simp only [internalCandidates, Finset.sum_filter, Finset.sym2_cons,
        Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons,
        Sym2.mkEmbedding_apply, Sym2.mk_isDiag_iff, not_true_eq_false,
        if_false, zero_add, degreeProduct_mk]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [if_pos (ne_of_mem_of_not_mem hv ha).symm]
    rw [hadd, Finset.sum_cons, Finset.sum_cons]
    nlinarith

/-- Literal number of undirected edges in the induced graph. -/
def internalCount (U : Finset V) (G : SimpleGraph V) : ℕ :=
  (G.induce (U : Set V)).edgeFinset.card

theorem internalCount_eq_filter (U : Finset V) (G : SimpleGraph V) :
    internalCount U G = ((internalCandidates U).filter (fun e => e ∈ G.edgeSet)).card := by
  rw [internalCount, ← G.card_filter_edgeFinset_toFinset_subset U]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      internalCandidates, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
      Finset.subset_iff, Sym2.mem_toFinset, Sym2.mem_iff]
    constructor
    · intro h
      exact ⟨⟨⟨h.2 (Or.inl rfl), h.2 (Or.inr rfl)⟩, h.1.ne⟩, h.1⟩
    · rintro ⟨⟨⟨ha, hb⟩, _⟩, hab⟩
      exact ⟨hab, fun v hv => hv.elim (fun h => h ▸ ha) (fun h => h ▸ hb)⟩

/-- The cut is represented by its unique endpoint in U and endpoint outside U. -/
def cutCandidates (U : Finset V) : Finset (V × V) := U ×ˢ (Finset.univ \ U)

def cutCount (U : Finset V) (G : SimpleGraph V) : ℕ :=
  ((cutCandidates U).filter (fun e => G.Adj e.1 e.2)).card

/-- Literal number of present cross-edge pairs in the prescribed rectangle. -/
def rectangleCount (U : Finset L) (W : Finset R) (E : CrossEdges L R) : ℕ :=
  ((U ×ˢ W).filter (fun e => e ∈ E)).card

omit [Fintype L] [Fintype R] in
theorem rectangle_product_sum (a : L → ℝ) (b : R → ℝ) (U : Finset L) (W : Finset R) :
    ∑ e ∈ U ×ˢ W, a e.1 * b e.2 = (∑ i ∈ U, a i) * (∑ j ∈ W, b j) := by
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.mul_sum W (fun j => b j) (a i)).symm

theorem cut_product_sum (d : V → ℝ) (U : Finset V) :
    ∑ e ∈ cutCandidates U, d e.1 * d e.2 =
      (∑ i ∈ U, d i) * (∑ j ∈ Finset.univ \ U, d j) :=
  rectangle_product_sum d d U (Finset.univ \ U)

/-- Graph-pair weights use the exact total number of oriented edges. -/
def graphWeight (d : V → ℕ) (m : ℕ) (e : Sym2 V) : ℝ :=
  degreeProduct (fun v => (d v : ℝ)) e / (2*m)

def bipartiteWeight (a : L → ℕ) (b : R → ℕ) (m : ℕ) (e : L × R) : ℝ :=
  (a e.1 : ℝ) * b e.2 / m

omit [Fintype V] in
theorem internal_weight_sum (d : V → ℕ) (m : ℕ) (U : Finset V) :
    ∑ e ∈ internalCandidates U, graphWeight d m e =
      ((∑ v ∈ U, (d v : ℝ))^2 - ∑ v ∈ U, (d v : ℝ)^2)/(4*m) := by
  simp only [graphWeight, ← Finset.sum_div]
  have h := internal_product_sum (fun v => (d v : ℝ)) U
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
    nlinarith

omit [Fintype L] [Fintype R] in
theorem rectangle_weight_sum (a : L → ℕ) (b : R → ℕ) (m : ℕ)
    (U : Finset L) (W : Finset R) :
    ∑ e ∈ U ×ˢ W, bipartiteWeight a b m e =
      (∑ i ∈ U, (a i : ℝ))*(∑ j ∈ W, (b j : ℝ))/m := by
  simp only [bipartiteWeight, ← Finset.sum_div]
  rw [rectangle_product_sum (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) U W]

omit [Fintype V] in
theorem graphWeight_nonneg (d : V → ℕ) (m : ℕ) (e : Sym2 V) :
    0 ≤ graphWeight d m e := by
  induction e using Sym2.ind with
  | _ a b => simp only [graphWeight, degreeProduct_mk]; positivity

omit [Fintype L] [Fintype R] in
theorem bipartiteWeight_nonneg (a : L → ℕ) (b : R → ℕ) (m : ℕ) (e : L × R) :
    0 ≤ bipartiteWeight a b m e := by unfold bipartiteWeight; positivity

/-- The two orientations of a cut edge cannot both occur in the chosen carrier. -/
theorem cut_sym2_injective (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1,e.2)) (cutCandidates U : Set (V × V)) := by
  intro x hx y hy he
  have hx' := Finset.mem_product.mp hx
  have hy' := Finset.mem_product.mp hy
  rcases Sym2.eq_iff.mp he with h | h
  · exact Prod.ext h.1 h.2
  · have hn := (Finset.mem_sdiff.mp hy'.2).2
    exact False.elim (hn (h.1 ▸ hx'.1))

omit [Fintype V] in
theorem indicatorCount_finset (S : Finset V) (A : V → Prop) :
    indicatorCount (fun v : S => fun _ : Unit => A v) () =
      ((S.filter A).card : ℝ) := by
  simp only [indicatorCount, eventIndicator]
  change (∑ i ∈ S.attach, if A i.val then (1 : ℝ) else 0) = _
  rw [Finset.sum_attach S (fun v => if A v then (1 : ℝ) else 0)]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The moment carrier gives exactly the actual induced edge count. -/
theorem internal_indicator_count (U : Finset V) (G : SimpleGraph V) :
    indicatorCount (fun e : internalCandidates U => fun H : SimpleGraph V => e.val ∈ H.edgeSet) G =
      (internalCount U G : ℝ) := by
  rw [internalCount_eq_filter]
  calc
    _ = indicatorCount (fun e : internalCandidates U => fun _ : Unit => e.val ∈ G.edgeSet) () := by
      unfold indicatorCount
      apply Finset.sum_congr rfl
      intro e _
      unfold eventIndicator
      split_ifs <;> rfl
    _ = _ := indicatorCount_finset (internalCandidates U) (fun e => e ∈ G.edgeSet)
  congr 2
  ext e
  simp

theorem cut_indicator_count (U : Finset V) (G : SimpleGraph V) :
    indicatorCount (fun e : cutCandidates U => fun H : SimpleGraph V => H.Adj e.val.1 e.val.2) G =
      (cutCount U G : ℝ) :=
  indicatorCount_finset (cutCandidates U) (fun e => G.Adj e.1 e.2)

omit [Fintype L] [Fintype R] in
theorem rectangle_indicator_count (U : Finset L) (W : Finset R) (E : CrossEdges L R) :
    indicatorCount (fun e : U ×ˢ W => fun F : CrossEdges L R => e.val ∈ F) E =
      (rectangleCount U W E : ℝ) :=
  indicatorCount_finset (U ×ˢ W) (fun e => e ∈ E)

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
