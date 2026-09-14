import MajorityDynamics.GraphProcess.CoarseKernel.Main
import MajorityDynamics.GraphProcess.GammaNumerator.Statistics
import MajorityDynamics.GraphProcess.RowConcentration.Degree

/-!
# The actual random-graph counts used in Proposition 5.7

Every scalar count is obtained from independent non-diagonal Bernoulli edge
sites. The degree law deletes the possible diagonal trial and then restores
the paper's centering at `p * partSizes`. Internal totals are twice a binomial
edge count; cross totals are a single binomial count. The only external input
is the already accepted scalar Chernoff inequality.
-/
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.DayOne
open Universal History Probability.DegreeConcentration
variable {V : Type*} [Fintype V]

def degreeSites (π : V → History 1) (v : V) (t : History 1) : Finset (Sym2 V) :=
  ((block π t).erase v).map ⟨fun w => s(v,w), fun _ _ h => Sym2.congr_right.mp h⟩

theorem degreeSites_nondiag (π : V → History 1) (v : V) (t : History 1) :
    (degreeSites π v t : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by
  intro e he
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp he
  change ¬ (s(v,w)).IsDiag
  exact (Finset.mem_erase.mp hw).1.symm

theorem degreeSites_card (π : V → History 1) (v : V) (t : History 1) :
    ((degreeSites π v t).card : ℝ) = (Local.partSizes π t : ℝ) -
      (if π v = t then 1 else 0) := by
  rw [degreeSites, Finset.card_map]
  by_cases h : π v = t
  · rw [Finset.card_erase_of_mem (by simpa using h), if_pos h]
    have hp : 1 ≤ (block π t).card := Finset.card_pos.mpr ⟨v,by simpa using h⟩
    rw [Nat.cast_sub hp, block_card_partSizes]
    norm_num
  · rw [Finset.erase_eq_of_notMem (by simpa using h), if_neg h, block_card_partSizes]
    simp

theorem degree_fromSites (π : V → History 1) (v : V) (t : History 1)
    (ω : Sym2 V → Prop) :
    degreeArray π (SimpleGraph.fromEdgeSet {e | ω e}) v t =
      (blockCount (degreeSites π v t) ω : ℤ) := by
  rw [degreeArray_eq_card, blockCount_eq_card, degreeSites,
    Finset.filter_map, Finset.card_map]
  congr 1
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_erase, SimpleGraph.fromEdgeSet_adj,
    Set.mem_ofPred_eq, Function.comp_apply]
  aesop

theorem degree_tail (π : V → History 1) (v : V) (t : History 1)
    (p : unitInterval) {x L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hm : (Local.partSizes π t : ℝ) * p ≤ 2*x)
    (hbias : (p:ℝ) ≤ Real.sqrt x * L / 2)
    (hscale : Real.sqrt x * L ≤ x) :
    (SimpleGraph.binomialRandom V p).real {G |
      Real.sqrt x * L < |(degreeArray π G v t : ℝ) - (p:ℝ)*Local.partSizes π t|} ≤
      2*Real.exp (-(3:ℝ)/80*L^2) := by
  have hb : |(p:ℝ)*Local.partSizes π t - ((degreeSites π v t).card:ℝ)*p| ≤
      Real.sqrt x*L/2 := by
    rw [degreeSites_card]
    split_ifs
    · calc
        _ = (p:ℝ) := by rw [show (p:ℝ)*Local.partSizes π t -
            ((Local.partSizes π t:ℝ)-1)*p = p by ring, abs_of_nonneg p.property.1]
        _ ≤ _ := hbias
    · simp only [sub_zero, mul_comm (p:ℝ), sub_self, abs_zero]
      positivity
  have hmc : ((degreeSites π v t).card:ℝ)*p ≤ 2*x := by
    rw [degreeSites_card]
    split_ifs <;> nlinarith [p.property.1]
  have htail := RowConcentration.shifted_binomial_tail (degreeSites π v t).card p
    hx hL hmc hb hscale
  rw [measureReal_def, ← siteLaw_map_blockCount _ p _ (degreeSites_nondiag π v t),
    Measure.map_apply (by fun_prop) (by measurability)] at htail
  rw [binomialRandom_eq_map_siteLaw, measureReal_def,
    Measure.map_apply (by fun_prop) (by measurability)]
  simpa only [measureReal_def, Set.preimage_ofPred_eq, degree_fromSites,
    Int.cast_natCast] using htail

theorem graph_edge_law (p : unitInterval) :
    (SimpleGraph.binomialRandom V p).map (fun G => G.edgeSet.ncard) =
      binomial ((Fintype.card V).choose 2) p := by
  let A : Finset (Sym2 V) := (Sym2.diagSetᶜ : Set (Sym2 V)).toFinset
  have hA : (A : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by simp [A]
  have hc : A.card = (Fintype.card V).choose 2 := by
    have he : A = Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag) := by
      ext e
      simp [A]
    rw [he]
    simpa only [Fintype.card_subtype, Sym2.mem_diagSet, Set.mem_compl_iff] using (Sym2.card_diagSet_compl (α := V))
  rw [binomialRandom_eq_map_siteLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : ((fun G : SimpleGraph V => G.edgeSet.ncard) ∘
      fun ω : Sym2 V → Prop => SimpleGraph.fromEdgeSet {e | ω e}) = blockCount A := by
    funext ω
    rw [Function.comp_apply, blockCount_eq_ncard]
    congr 1
    ext e
    induction e using Sym2.inductionOn with
    | _ a b => simp [A]
  rw [hf, siteLaw_map_blockCount _ p A hA, hc]

theorem internal_total (π : V → History 1) (s : History 1) (G : SimpleGraph V) :
    (edgeTotals π (degreeArray π G) s s : ℝ) =
      2 * ((GammaNumerator.internal π s G).edgeSet.ncard : ℝ) := by
  have h := (GammaNumerator.internal π s G).sum_degrees_eq_twice_card_edges
  have hr := congrArg (fun z : ℕ => (z:ℝ)) h
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at hr
  have hs := GammaNumerator.sum_values π s s G
  simp only [RowArray.totals_graphArray] at hs
  rw [← hs]
  simp only [← GammaNumerator.internal_degree]
  simpa only [graphDegree, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hr

theorem cross_total (π : V → History 1) (s t : History 1) (G : SimpleGraph V) :
    (edgeTotals π (degreeArray π G) s t : ℝ) =
      ((GammaNumerator.cross π s t G).ncard : ℝ) := by
  have hs := GammaNumerator.sum_values π s t G
  simp only [RowArray.totals_graphArray] at hs
  rw [← hs]
  simp only [← GammaNumerator.cross_left_degree, leftDegree,
    Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [← Nat.cast_sum]
  congr 1
  rw [Fintype.card_subtype]
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

theorem count_tail {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) (X : Ω → ℕ)
    (p : unitInterval) (m : ℕ) (hlaw : μ.map X = binomial m p)
    {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (hm : (m:ℝ)*p ≤ 2*x)
    (hscale : Real.sqrt x*L ≤ x) :
    μ.real {ω | Real.sqrt x*L < |(X ω:ℝ) - (m:ℝ)*p|} ≤
      2*Real.exp (-(3:ℝ)/80*L^2) := by
  have h := RowConcentration.shifted_binomial_tail m p hx hL hm
    (show |(m:ℝ)*p-(m:ℝ)*p| ≤ Real.sqrt x*L/2 by simp; positivity) hscale
  rw [measureReal_def, ← hlaw, Measure.map_apply (by fun_prop) (by measurability)] at h
  exact h

theorem edge_tail (π : V → History 1) (s t : History 1)
    (p : unitInterval) {x L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hm : (Fintype.card V:ℝ)^2*p ≤ x)
    (hscale : Real.sqrt x*L ≤ x) :
    (SimpleGraph.binomialRandom V p).real {G |
      2*Real.sqrt x*L < |(edgeTotals π (degreeArray π G) s t:ℝ) -
        (p:ℝ)*(Local.partSizes π s:ℝ)*((Local.partSizes π t:ℝ)-(if s=t then 1 else 0))|} ≤
      2*Real.exp (-(3:ℝ)/80*L^2) := by
  have hs : (Local.partSizes π s:ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset (s := (Finset.univ : Finset V)) (p := fun v => π v=s)))
  have ht : (Local.partSizes π t:ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset (s := (Finset.univ : Finset V)) (p := fun v => π v=t)))
  have hprod : (Local.partSizes π s:ℝ)*(Local.partSizes π t:ℝ)*p ≤ x := by
    calc
      _ ≤ (Fintype.card V:ℝ)^2*p := by
        apply mul_le_mul_of_nonneg_right _ p.property.1
        simpa only [pow_two] using mul_le_mul hs ht (by positivity : (0:ℝ) ≤ Local.partSizes π t) (by positivity : (0:ℝ) ≤ Fintype.card V)
      _ ≤ _ := hm
  by_cases hst : s=t
  · subst t
    let X : SimpleGraph V → ℕ := fun G => (GammaNumerator.internal π s G).edgeSet.ncard
    have hlaw : (SimpleGraph.binomialRandom V p).map X =
        binomial ((GammaNumerator.blockSize π s).choose 2) p := by
      rw [show X = (fun G => G.edgeSet.ncard) ∘ GammaNumerator.internal π s by rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop), GammaNumerator.internal_law, graphLaw]
      simpa only [Fintype.card_fin] using graph_edge_law (V := Fin (GammaNumerator.blockSize π s)) p
    have hmc : (((GammaNumerator.blockSize π s).choose 2:ℕ):ℝ)*p ≤ 2*x := by
      rw [Nat.cast_choose_two, GammaNumerator.blockSize_eq]
      nlinarith only [hprod, hx, mul_nonneg (p.property.1) (show (0:ℝ) ≤ Local.partSizes π s by positivity)]
    have hh := count_tail (SimpleGraph.binomialRandom V p) X p _ hlaw hx hL hmc hscale
    refine (measureReal_mono (show {G | _} ⊆ {G | _} from ?_)).trans hh
    intro G hG
    simp only [Set.mem_ofPred_eq, internal_total, ite_true] at hG
    change Real.sqrt x*L < |(X G:ℝ) - (((GammaNumerator.blockSize π s).choose 2:ℕ):ℝ)*p|
    rw [Nat.cast_choose_two, GammaNumerator.blockSize_eq]
    have he : |2*(X G:ℝ)-(p:ℝ)*(Local.partSizes π s:ℝ)*((Local.partSizes π s:ℝ)-1)| =
        2*|(X G:ℝ)-(Local.partSizes π s:ℝ)*((Local.partSizes π s:ℝ)-1)/2*p| := by
      calc
        _ = |2*((X G:ℝ)-(Local.partSizes π s:ℝ)*((Local.partSizes π s:ℝ)-1)/2*p)| := by congr 1; ring
        _ = _ := by rw [abs_mul]; norm_num
    rw [he] at hG
    linarith
  · let X : SimpleGraph V → ℕ := fun G => (GammaNumerator.cross π s t G).ncard
    have hlaw : (SimpleGraph.binomialRandom V p).map X =
        binomial (GammaNumerator.blockSize π s * GammaNumerator.blockSize π t) p := by
      rw [show X = Set.ncard ∘ GammaNumerator.cross π s t by rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop), GammaNumerator.cross_law π s t hst]
      have h := setBernoulli_map_ncard_eq_binomial
        (Finset.univ : Finset (Fin (GammaNumerator.blockSize π s) × Fin (GammaNumerator.blockSize π t))) p
      simpa [bipartiteLaw] using h
    have hmc : ((GammaNumerator.blockSize π s * GammaNumerator.blockSize π t:ℕ):ℝ)*p ≤ 2*x := by
      simp only [Nat.cast_mul, GammaNumerator.blockSize_eq]
      linarith
    have hh := count_tail (SimpleGraph.binomialRandom V p) X p _ hlaw hx hL hmc hscale
    refine (measureReal_mono (show {G | _} ⊆ {G | _} from ?_)).trans hh
    intro G hG
    simp only [Set.mem_ofPred_eq, if_neg hst, sub_zero, cross_total] at hG
    change Real.sqrt x*L < |(X G:ℝ) - ((GammaNumerator.blockSize π s * GammaNumerator.blockSize π t:ℕ):ℝ)*p|
    simp only [Nat.cast_mul, GammaNumerator.blockSize_eq]
    have he : (p:ℝ)*(Local.partSizes π s:ℝ)*(Local.partSizes π t:ℝ) =
      (Local.partSizes π s:ℝ)*(Local.partSizes π t:ℝ)*p := by ring
    rw [he] at hG
    nlinarith only [hG, mul_nonneg (Real.sqrt_nonneg x) hL.le]

end MajorityDynamics.GraphProcess.DayOne
