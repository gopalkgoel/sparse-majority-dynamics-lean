import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.TailAssembly
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseNumerics
noncomputable section
universe u v w
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling Numerics
theorem eventually_moment_absorption_sparse {θ T C K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N →
      0 < edgeThreshold N p ∧ 0 < Numerics.epsilon N p ∧
      ∀ W q : ℝ, 0 ≤ W → W ≤ K*(N:ℝ)^2*p → 0 ≤ q → q ≤ K*(p*N) →
        (2*((1+C*Numerics.epsilon N p)*W + 3*(C*Numerics.epsilon N p)*W^2)+2*q^2) /
          (edgeThreshold N p)^2 < 1/Real.log N := by
  obtain ⟨N₁,h₁⟩ := Numerics.eventually_final_absorption_sparse hθlo hθhi hT
    (B:=0) (C:=momentCoefficient C K) (by positivity) (by unfold momentCoefficient; positivity)
  obtain ⟨N₂,h₂⟩ := Numerics.eventually_epsilon_sparse hθlo hθhi hT (η:=1) zero_lt_one
  obtain ⟨N₃,h₃⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT
    (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp
  have hA := h₁ N ((le_max_left _ _).trans hN) p hp.1 hp.2
  have hE := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2
  have hW := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2
  simp only [zero_mul, sub_zero] at hA
  change 0 < Numerics.scale N p ∧ 0 ≤ Numerics.scale N p ∧
    0 < edgeThreshold N p ∧
    momentCoefficient C K*(Numerics.scale N p)^2/(edgeThreshold N p)^2 < 1/Real.log N at hA
  refine ⟨hA.2.2.1,hE.1,?_⟩
  intro W q hW0 hWu hq0 hqu
  exact (div_le_div_of_nonneg_right
    (finite_moment_scale_bound hW.2.2.1 hW.2.1 hW.2.2.2.1 hC hK hE.2 hW0 hWu hq0 hqu)
    (sq_nonneg _)).trans_lt hA.2.2.2

theorem eventually_tail_consumers_sparse {θ T C K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N →
      (∀ (V : Type*) [Fintype V] (d : V → ℕ) (m : ℕ) (U : Finset V),
        (graphFamily d).Nonempty → (∑ v, d v = 2*m) →
        (m : ℝ) ≤ K*(N:ℝ)^2*p → (∀ v, (d v : ℝ) ≤ K*(p*N)) →
        (∀ e : Sym2 V, ¬ e.IsDiag →
          |(fixedDegreeLaw d).real {G | e ∈ G.edgeSet} - graphWeight d m e| ≤
            (C*Numerics.epsilon N p) * graphWeight d m e) →
        (∀ e f : Sym2 V, ¬ e.IsDiag → ¬ f.IsDiag → e ≠ f →
          (fixedDegreeLaw d).real {G | e ∈ G.edgeSet ∧ f ∈ G.edgeSet} ≤
            (1+C*Numerics.epsilon N p) * graphWeight d m e * graphWeight d m f) →
        (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
          |(internalCount U G : ℝ)-(∑ v ∈ U, (d v : ℝ))^2/(4*m)|} < 1/Real.log N ∧
        (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
          |(cutCount U G : ℝ)-(∑ v ∈ U, (d v : ℝ)) *
            (∑ v ∈ Finset.univ \ U, (d v : ℝ))/(2*m)|} < 1/Real.log N) ∧
      (∀ (L R : Type*) [Fintype L] [Fintype R] (a : L → ℕ) (b : R → ℕ)
        (m : ℕ) (U : Finset L) (W : Finset R),
        (bipartiteFamily a b).Nonempty → (∑ v, a v = m) → (∑ w, b w = m) →
        (m : ℝ) ≤ K*(N:ℝ)^2*p →
        (∀ e : L × R,
          |(bipartiteFixedDegreeLaw a b).real {E | e ∈ E} - bipartiteWeight a b m e| ≤
            (C*Numerics.epsilon N p) * bipartiteWeight a b m e) →
        (∀ e f : L × R, e ≠ f →
          (bipartiteFixedDegreeLaw a b).real {E | e ∈ E ∧ f ∈ E} ≤
            (1+C*Numerics.epsilon N p) * bipartiteWeight a b m e * bipartiteWeight a b m f) →
        (bipartiteFixedDegreeLaw a b).real {E | edgeThreshold N p ≤
          |(rectangleCount U W E : ℝ)-(∑ v ∈ U, (a v : ℝ)) *
            (∑ w ∈ W, (b w : ℝ))/m|} < 1/Real.log N) := by
  obtain ⟨N₁,h₁⟩ := eventually_moment_absorption_sparse hθlo hθhi hT hC
    (K:=2*K) (mul_nonneg (by norm_num) hK)
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT
    (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hp
  have hh := h₁ N ((le_max_left _ _).trans hN) p hp
  have hz := h₂ N ((le_max_right _ _).trans hN) p hp.1 hp.2
  have hp0 : 0 < p := hz.2.1
  have hx0 : 0 ≤ p*N := (mul_pos hp0 hz.1).le
  have hbase0 : 0 ≤ K*(N:ℝ)^2*p := by positivity
  have hdelta : 0 ≤ C*Numerics.epsilon N p := mul_nonneg hC hh.2.1.le
  constructor
  · intro V _ d m U hn htotal hm hdeg hmarg hpair
    let c : ℝ := (∑ v ∈ U, (d v : ℝ))^2/(4*m)
    let q : ℝ := (∑ v ∈ U, (d v : ℝ)^2)/(4*m)
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hc : c ≤ K*(N:ℝ)^2*p := (internal_center_le_total d m U htotal).trans hm
    have hq : q ≤ K*(p*N) := internal_diagonal_le d m U _ (by positivity) htotal hdeg
    have hW0 : 0 ≤ c-q := by
      have hi := internal_weight_sum d m U
      rw [sub_div] at hi
      change (∑ e ∈ internalCandidates U, graphWeight d m e) = c-q at hi
      rw [← hi]
      exact Finset.sum_nonneg (fun e _ => graphWeight_nonneg d m e)
    have hW : c-q ≤ 2*K*(N:ℝ)^2*p := by nlinarith
    have hqu : q ≤ 2*K*(p*N) := by nlinarith [mul_nonneg hK hx0]
    constructor
    · exact (internal_tail_of_edge_estimates d m U _ _ hn hdelta hh.1 hmarg hpair).trans_lt
        (hh.2.2 (c-q) q hW0 hW hq0 hqu)
    · let cc : ℝ := (∑ v ∈ U, (d v : ℝ)) *
          (∑ v ∈ Finset.univ \ U, (d v : ℝ))/(2*m)
      have hcc0 : 0 ≤ cc := by dsimp [cc]; positivity
      have hcc : cc ≤ 2*K*(N:ℝ)^2*p := by
        have hc := cut_center_le_total d m U htotal
        dsimp [cc]
        nlinarith
      have hzq : (0:ℝ) ≤ 2*K*(p*N) := by positivity
      have hb := hh.2.2 cc 0 hcc0 hcc le_rfl hzq
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hb
      exact (cut_tail_of_edge_estimates d m U _ _ hn hdelta hh.1 hmarg hpair).trans_lt hb
  · intro L R _ _ a b m U W hn ha hb hm hmarg hpair
    let c : ℝ := (∑ v ∈ U, (a v : ℝ))*(∑ w ∈ W, (b w : ℝ))/m
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hc : c ≤ 2*K*(N:ℝ)^2*p := by
      have hh := (rectangle_center_le_total a b m U W ha hb).trans hm
      dsimp [c]
      nlinarith
    have hzq : (0:ℝ) ≤ 2*K*(p*N) := by positivity
    have hbound := hh.2.2 c 0 hc0 hc le_rfl hzq
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hbound
    exact (rectangle_tail_of_edge_estimates a b m U W _ _ hn hdelta hh.1 hmarg hpair).trans_lt hbound

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
