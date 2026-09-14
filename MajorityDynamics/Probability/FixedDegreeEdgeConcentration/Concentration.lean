import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Counts

/-! Actual fixed-degree-law tail bounds from single-edge errors and one-sided
joint bounds. The second moment is proved, not supplied as a hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

/-- The induced-edge center includes a precisely quantified diagonal correction. -/
theorem internal_tail_of_edge_estimates (d : V → ℕ) (m : ℕ) (U : Finset V)
    (δ t : ℝ) (hn : (graphFamily d).Nonempty) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hmarg : ∀ e : Sym2 V, ¬ e.IsDiag →
      |(fixedDegreeLaw d).real {G | e ∈ G.edgeSet} - graphWeight d m e| ≤
        δ * graphWeight d m e)
    (hpair : ∀ e f : Sym2 V, ¬ e.IsDiag → ¬ f.IsDiag → e ≠ f →
      (fixedDegreeLaw d).real {G | e ∈ G.edgeSet ∧ f ∈ G.edgeSet} ≤
        (1 + δ) * graphWeight d m e * graphWeight d m f) :
    let c : ℝ := (∑ v ∈ U, (d v : ℝ))^2 / (4*m)
    let q : ℝ := (∑ v ∈ U, (d v : ℝ)^2) / (4*m)
    (fixedDegreeLaw d).real {G | t ≤ |(internalCount U G : ℝ) - c|} ≤
      (2 * ((1+δ)*(c-q) + 3*δ*(c-q)^2) + 2*q^2) / t^2 := by
  let := fixedDegreeLaw_normalized d hn
  let c : ℝ := (∑ v ∈ U, (d v : ℝ))^2 / (4*m)
  let q : ℝ := (∑ v ∈ U, (d v : ℝ)^2) / (4*m)
  have hw : (∑ e : internalCandidates U, graphWeight d m e.val) = c-q := by
    rw [Finset.sum_coe_sort, internal_weight_sum, sub_div]
  have h := measure_indicator_tail (fixedDegreeLaw d)
    (fun e : internalCandidates U => fun G : SimpleGraph V => e.val ∈ G.edgeSet)
    (fun e => graphWeight d m e.val) δ c t hδ
    (fun e => graphWeight_nonneg d m e.val) ht
    (fun e => hmarg e.val (Finset.mem_filter.mp e.property).2)
    (fun e f hef => hpair e.val f.val (Finset.mem_filter.mp e.property).2
      (Finset.mem_filter.mp f.property).2 (fun he => hef (Subtype.ext he)))
  rw [hw] at h
  have hb : (c-q-c)^2 = q^2 := by ring
  rw [hb] at h
  simpa only [internal_indicator_count] using h

/-- A cut candidate has distinct endpoints, by its literal U/complement membership. -/
theorem cut_candidate_nondiag (U : Finset V) (e : cutCandidates U) :
    ¬ (s(e.val.1,e.val.2) : Sym2 V).IsDiag := by
  have he := Finset.mem_product.mp e.property
  rw [Sym2.mk_isDiag_iff]
  intro h
  exact (Finset.mem_sdiff.mp he.2).2 (h ▸ he.1)

/-- Cut counts use one orientation of each crossing edge, with the exact paper center. -/
theorem cut_tail_of_edge_estimates (d : V → ℕ) (m : ℕ) (U : Finset V)
    (δ t : ℝ) (hn : (graphFamily d).Nonempty) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hmarg : ∀ e : Sym2 V, ¬ e.IsDiag →
      |(fixedDegreeLaw d).real {G | e ∈ G.edgeSet} - graphWeight d m e| ≤
        δ * graphWeight d m e)
    (hpair : ∀ e f : Sym2 V, ¬ e.IsDiag → ¬ f.IsDiag → e ≠ f →
      (fixedDegreeLaw d).real {G | e ∈ G.edgeSet ∧ f ∈ G.edgeSet} ≤
        (1 + δ) * graphWeight d m e * graphWeight d m f) :
    let c : ℝ := (∑ v ∈ U, (d v : ℝ)) * (∑ v ∈ Finset.univ \ U, (d v : ℝ)) / (2*m)
    (fixedDegreeLaw d).real {G | t ≤ |(cutCount U G : ℝ) - c|} ≤
      2 * ((1+δ)*c + 3*δ*c^2) / t^2 := by
  let := fixedDegreeLaw_normalized d hn
  let c : ℝ := (∑ v ∈ U, (d v : ℝ)) * (∑ v ∈ Finset.univ \ U, (d v : ℝ)) / (2*m)
  have hw : (∑ e : cutCandidates U, graphWeight d m s(e.val.1,e.val.2)) = c := by
    rw [Finset.sum_coe_sort (cutCandidates U)
      (fun e : V × V => graphWeight d m s(e.1,e.2))]
    simp only [graphWeight, degreeProduct_mk, ← Finset.sum_div]
    rw [cut_product_sum (fun v => (d v : ℝ)) U]
  have h := measure_indicator_tail (fixedDegreeLaw d)
    (fun e : cutCandidates U => fun G : SimpleGraph V => G.Adj e.val.1 e.val.2)
    (fun e => graphWeight d m s(e.val.1,e.val.2)) δ c t hδ
    (fun e => graphWeight_nonneg d m _) ht
    (fun e => by
      simpa only [SimpleGraph.mem_edgeSet] using
        hmarg s(e.val.1,e.val.2) (cut_candidate_nondiag U e))
    (fun e f hef => by
      have he : (s(e.val.1,e.val.2) : Sym2 V) ≠ s(f.val.1,f.val.2) := by
        intro h
        exact hef (Subtype.ext (cut_sym2_injective U e.property f.property h))
      simpa only [SimpleGraph.mem_edgeSet] using hpair _ _
        (cut_candidate_nondiag U e) (cut_candidate_nondiag U f) he)
  rw [hw] at h
  simpa only [cut_indicator_count, sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] using h

/-- Rectangular bipartite counts retain the exact two side masses and edge total. -/
theorem rectangle_tail_of_edge_estimates (a : L → ℕ) (b : R → ℕ) (m : ℕ)
    (U : Finset L) (W : Finset R) (δ t : ℝ)
    (hn : (bipartiteFamily a b).Nonempty) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hmarg : ∀ e : L × R,
      |(bipartiteFixedDegreeLaw a b).real {E | e ∈ E} - bipartiteWeight a b m e| ≤
        δ * bipartiteWeight a b m e)
    (hpair : ∀ e f : L × R, e ≠ f →
      (bipartiteFixedDegreeLaw a b).real {E | e ∈ E ∧ f ∈ E} ≤
        (1 + δ) * bipartiteWeight a b m e * bipartiteWeight a b m f) :
    let c : ℝ := (∑ i ∈ U, (a i : ℝ)) * (∑ j ∈ W, (b j : ℝ)) / m
    (bipartiteFixedDegreeLaw a b).real {E | t ≤ |(rectangleCount U W E : ℝ) - c|} ≤
      2 * ((1+δ)*c + 3*δ*c^2) / t^2 := by
  let := bipartiteFixedDegreeLaw_normalized a b hn
  let c : ℝ := (∑ i ∈ U, (a i : ℝ)) * (∑ j ∈ W, (b j : ℝ)) / m
  have hw : (∑ e : U ×ˢ W, bipartiteWeight a b m e.val) = c := by
    rw [Finset.sum_coe_sort, rectangle_weight_sum]
  have h := measure_indicator_tail (bipartiteFixedDegreeLaw a b)
    (fun e : U ×ˢ W => fun E : CrossEdges L R => e.val ∈ E)
    (fun e => bipartiteWeight a b m e.val) δ c t hδ
    (fun e => bipartiteWeight_nonneg a b m e.val) ht
    (fun e => hmarg e.val)
    (fun e f hef => hpair e.val f.val (fun he => hef (Subtype.ext he)))
  rw [hw] at h
  simpa only [rectangle_indicator_count, sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] using h

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
