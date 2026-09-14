import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Concentration
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Basic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling

/-- A finite subset carries at most the total nonnegative degree mass. -/
theorem degree_mass_le_total {V : Type*} [Fintype V] (d : V → ℕ) (U : Finset V) :
    (∑ v ∈ U, (d v : ℝ)) ≤ ∑ v, (d v : ℝ) := by
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.cast_nonneg _)

/-- Total degree mass alone bounds the induced-edge center. -/
theorem internal_center_le_total {V : Type*} [Fintype V] (d : V → ℕ)
    (m : ℕ) (U : Finset V) (htotal : ∑ v, d v = 2*m) :
    (∑ v ∈ U, (d v : ℝ))^2 / (4*m) ≤ m := by
  have hs : (∑ v, (d v : ℝ)) = 2*(m:ℝ) := by exact_mod_cast htotal
  have hu := degree_mass_le_total d U
  rw [hs] at hu
  have hu0 : 0 ≤ ∑ v ∈ U, (d v : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_cases hm : m = 0
  · simp [hm]
  · have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 4*m)).mpr
    nlinarith

/-- The diagonal correction is bounded using the actual maximum degree. -/
theorem internal_diagonal_le {V : Type*} [Fintype V] (d : V → ℕ)
    (m : ℕ) (U : Finset V) (D : ℝ) (hD : 0 ≤ D)
    (htotal : ∑ v, d v = 2*m) (hdeg : ∀ v, (d v : ℝ) ≤ D) :
    (∑ v ∈ U, (d v : ℝ)^2) / (4*m) ≤ D := by
  have hs : (∑ v, (d v : ℝ)) = 2*(m:ℝ) := by exact_mod_cast htotal
  have hu := degree_mass_le_total d U
  rw [hs] at hu
  have hsq : (∑ v ∈ U, (d v : ℝ)^2) ≤ D * (∑ v ∈ U, (d v : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    nlinarith [hdeg v, Nat.cast_nonneg (α:=ℝ) (d v)]
  by_cases hm : m = 0
  · simp [hm, hD]
  · have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 4*m)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hu hD]

/-- A coarse bound for the exact cut center, with no subset assumptions. -/
theorem cut_center_le_total {V : Type*} [Fintype V] (d : V → ℕ)
    (m : ℕ) (U : Finset V) (htotal : ∑ v, d v = 2*m) :
    (∑ v ∈ U, (d v : ℝ)) * (∑ v ∈ Finset.univ \ U, (d v : ℝ)) / (2*m) ≤ 2*m := by
  have hs : (∑ v, (d v : ℝ)) = 2*(m:ℝ) := by exact_mod_cast htotal
  have hu := degree_mass_le_total d U
  have hv := degree_mass_le_total d (Finset.univ \ U)
  rw [hs] at hu hv
  have hu0 : 0 ≤ ∑ v ∈ U, (d v : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hv0 : 0 ≤ ∑ v ∈ Finset.univ \ U, (d v : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_cases hm : m = 0
  · simp [hm]
  · have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    exact (div_le_iff₀ (by positivity : (0:ℝ) < 2*m)).mpr (mul_le_mul hu hv hv0 (by positivity))

/-- A rectangle's exact center is bounded by the actual bipartite edge total. -/
theorem rectangle_center_le_total {L R : Type*} [Fintype L] [Fintype R]
    (a : L → ℕ) (b : R → ℕ) (m : ℕ) (U : Finset L) (W : Finset R)
    (ha : ∑ v, a v = m) (hb : ∑ w, b w = m) :
    (∑ v ∈ U, (a v : ℝ)) * (∑ w ∈ W, (b w : ℝ)) / m ≤ m := by
  have hsa : (∑ v, (a v : ℝ)) = (m:ℝ) := by exact_mod_cast ha
  have hsb : (∑ w, (b w : ℝ)) = (m:ℝ) := by exact_mod_cast hb
  have hu := degree_mass_le_total a U
  have hv := degree_mass_le_total b W
  rw [hsa] at hu
  rw [hsb] at hv
  have hv0 : 0 ≤ ∑ w ∈ W, (b w : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_cases hm : m = 0
  · simp [hm]
  · have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    exact (div_le_iff₀ hm0).mpr (mul_le_mul hu hv hv0 (Nat.cast_nonneg _))

/-- A universal coefficient bounds the proved centered second moment. -/
def momentCoefficient (C K : ℝ) : ℝ := 2*(1+C)*K+6*C*K^2+2*K^2

theorem finite_moment_scale_bound {N p C K W q : ℝ}
    (hN : 1 ≤ N) (hp : 0 < p) (hx : 1 ≤ p*N)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (he : Numerics.epsilon N p ≤ 1)
    (hW0 : 0 ≤ W) (hW : W ≤ K*N^2*p) (hq0 : 0 ≤ q) (hq : q ≤ K*(p*N)) :
    2*((1+C*Numerics.epsilon N p)*W + 3*(C*Numerics.epsilon N p)*W^2)+2*q^2 ≤
      momentCoefficient C K * (Numerics.scale N p)^2 := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < p*N := mul_pos hp hN0
  have he0 : 0 ≤ Numerics.epsilon N p := by unfold Numerics.epsilon; positivity
  have hr : 1 ≤ (p*N)^((1:ℝ)/7) := Real.one_le_rpow hx (by norm_num)
  have hS := Numerics.scale_sq hN0 hp
  have hlin : N^2*p ≤ (Numerics.scale N p)^2 := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul hx hr (by positivity) (by positivity))
      (show 0 ≤ N^2*p by positivity)
    rw [hS]
    nlinarith
  have hqscale : (p*N)^2 ≤ (Numerics.scale N p)^2 := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul hN hr (by positivity) (by positivity))
      (sq_nonneg (p*N))
    rw [hS]
    nlinarith
  have hcross : Numerics.epsilon N p * (K*N^2*p)^2 = K^2*(Numerics.scale N p)^2 := by
    rw [hS]
    unfold Numerics.epsilon
    field_simp
  have hδ : C*Numerics.epsilon N p ≤ C := by nlinarith
  have hterm1 : (1+C*Numerics.epsilon N p)*W ≤ (1+C)*K*(Numerics.scale N p)^2 := by
    calc
      _ ≤ (1+C)*(K*N^2*p) := mul_le_mul (by linarith) hW hW0 (by positivity)
      _ ≤ (1+C)*K*(Numerics.scale N p)^2 := by nlinarith [mul_le_mul_of_nonneg_left hlin (by positivity : 0 ≤ (1+C)*K)]
  have hWsq : W^2 ≤ (K*N^2*p)^2 := sq_le_sq₀ hW0 (by positivity) |>.mpr hW
  have hterm2 : 3*(C*Numerics.epsilon N p)*W^2 ≤ 3*C*K^2*(Numerics.scale N p)^2 := by
    calc
      _ ≤ 3*(C*Numerics.epsilon N p)*(K*N^2*p)^2 := mul_le_mul_of_nonneg_left hWsq (by positivity)
      _ = _ := by nlinarith [hcross]
  have hqsq : q^2 ≤ K^2*(p*N)^2 := by nlinarith [sq_le_sq₀ hq0 (by positivity : 0 ≤ K*(p*N)) |>.mpr hq]
  have hterm3 : q^2 ≤ K^2*(Numerics.scale N p)^2 := hqsq.trans (mul_le_mul_of_nonneg_left hqscale (sq_nonneg K))
  unfold momentCoefficient
  nlinarith

/-- Every coefficient is absorbed by the original final logarithm, uniformly in p. -/
theorem eventually_moment_absorption {θ T C K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N →
      0 < edgeThreshold N p ∧ 0 < Numerics.epsilon N p ∧
      ∀ W q : ℝ, 0 ≤ W → W ≤ K*(N:ℝ)^2*p → 0 ≤ q → q ≤ K*(p*N) →
        (2*((1+C*Numerics.epsilon N p)*W + 3*(C*Numerics.epsilon N p)*W^2)+2*q^2) /
          (edgeThreshold N p)^2 < 1/Real.log N := by
  obtain ⟨N₁,h₁⟩ := Numerics.eventually_final_absorption hθlo hθhi hT
    (B:=0) (C:=momentCoefficient C K) (by positivity) (by unfold momentCoefficient; positivity)
  obtain ⟨N₂,h₂⟩ := Numerics.eventually_epsilon hθlo hθhi hT (η:=1) zero_lt_one
  obtain ⟨N₃,h₃⟩ := GraphProcess.EnumerationBounds.eventually_window hθlo hθhi hT
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


/-- The three real laws satisfy the literal C.1 tails once their marginal and
joint estimates have been established. All numerical constants are absorbed
before the varying finite inputs. -/
theorem eventually_tail_consumers {θ T C K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N →
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
  obtain ⟨N₁,h₁⟩ := eventually_moment_absorption hθlo hθhi hT hC
    (K:=2*K) (mul_nonneg (by norm_num) hK)
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_window hθlo hθhi hT
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
