import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.RelativeNumerics
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.GraphError
import MajorityDynamics.Literature.EdgeProbabilities.WindowApplications

noncomputable section
universe u v
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling Numerics Literature.EdgeProbabilities

/-- The actual graph marginal has the paper's relative error, uniformly before
all original or residual degree data and all queried edges. -/
theorem graph_window_relative_error {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (V : Type u) [Fintype V] (n m : ℕ) (d : V → ℕ),
      GraphWindow N n m p K A d → ∀ a b, a ≠ b →
      |(fixedDegreeLaw d).real {G | G.Adj a b} - (d a:ℝ)*d b/(2*m)| ≤
        C*epsilon N p*((d a:ℝ)*d b/(2*m)) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨C,hC,N₁,h₁⟩ := graph_window_source_error.{u} hθlo hθhi hT hK (A:=A)
  obtain ⟨N₂,h₂⟩ := eventually_relativeData hθlo hθhi hT hK (A:=A)
  obtain ⟨N₃,h₃⟩ := eventually_graphWindow.{u} hθlo hθhi hT hK (A:=A)
  refine ⟨C*((2*K^3+8*K^6)*(8*K^4)) + ((2+32*K^2*(|A|+1)^2)*K),
    by positivity, max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp V _ n m d hw a b hab
  have hs := h₁ N ((le_max_left _ _).trans hN) p hp V n m d hw a b hab
  have hz := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have hg := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp V n m d hw
  have hx : 0 < p*N := mul_pos hz.p_pos hz.N_pos
  have hn0 := hz.dimension_pos hK hw.size_lower
  have hD0 : 0 < graphAverage n m := (div_pos hx (by positivity)).trans_le hg.2.1
  have hcenter : p*N/K ≤ p*N := by
    apply (div_le_iff₀ hK0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hK hx.le]
  have ha := hz.degree_lower hK hcenter (hw.degree_window a)
  have hb := hz.degree_lower hK hcenter (hw.degree_window b)
  have he := graph_error_relative hz.N_pos hz.degree_one rfl hz.degree_square hK
    hw.size_lower hw.size_upper hD0 hg.2.2
    (hz.log_degree n hn0 hw.size_upper) ha hb
  have hwgt : (d a:ℝ)*d b/(graphAverage n m*(n:ℝ)) = (d a:ℝ)*d b/(2*m) := by
    unfold graphAverage
    rw [div_mul_cancel₀ _ hn0.ne']
  rw [hwgt] at he
  have hc := graph_approximation_relative hK hz hw hg.2.1 hg.2.2 a b
  calc
    _ ≤ |(fixedDegreeLaw d).real {G | G.Adj a b} - graphApproximation n m (d a) (d b)| +
      |graphApproximation n m (d a) (d b) - (d a:ℝ)*d b/(2*m)| := abs_sub_le _ _ _
    _ ≤ C*graphErrorScale n m +
      ((2+32*K^2*(|A|+1)^2)*K)*epsilon N p*((d a:ℝ)*d b/(2*m)) := add_le_add hs hc
    _ ≤ C*(((2*K^3+8*K^6)*(8*K^4))*epsilon N p*((d a:ℝ)*d b/(2*m))) +
      ((2+32*K^2*(|A|+1)^2)*K)*epsilon N p*((d a:ℝ)*d b/(2*m)) :=
        add_le_add (mul_le_mul_of_nonneg_left he hC.le) le_rfl
    _ = _ := by ring

/-- The actual bipartite marginal has the same reference-scale relative error.
Both source variance corrections are proved small; no such bound is assumed. -/
theorem bipartite_window_relative_error {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ),
      BipartiteWindow N ell n m p K A a b → ∀ i j,
      |(bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} - (a i:ℝ)*b j/m| ≤
        C*epsilon N p*((a i:ℝ)*b j/m) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨C,hC,N₁,h₁⟩ := bipartite_window_source_error.{u,v} hθlo hθhi hT hK (A:=A)
  obtain ⟨N₂,h₂⟩ := eventually_relativeData hθlo hθhi hT hK (A:=A)
  obtain ⟨N₃,h₃⟩ := eventually_bipartiteWindow.{u,v} hθlo hθhi hT hK (A:=A)
  refine ⟨C*K+48*K^2*(|A|+1)^2, by positivity, max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp L R _ _ ell n m a b hw i j
  have hs := h₁ N ((le_max_left _ _).trans hN) p hp L R ell n m a b hw i j
  have hz := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have hg := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp L R ell n m a b hw
  have he0 := hz.dimension_pos hK hw.size_left_lower
  have hn0 := hz.dimension_pos hK hw.size_right_lower
  have hone : 1 ≤ p*N/(2*K) := (le_div_iff₀ (by positivity : 0 < 2*K)).mpr (by simpa using hz.degree_large)
  have herr := bipartite_error_reciprocal ell n m
    (by exact_mod_cast he0) (by exact_mod_cast hn0)
    (hone.trans hg.2.1) (hone.trans hg.2.2.2.1)
  have hmin : (N:ℝ)/K ≤ min (ell:ℝ) n := le_min hw.size_left_lower hw.size_right_lower
  have herr' := herr.trans (hz.reciprocal_le hK hmin)
  have hw0 : 0 ≤ bipartitePrefactor m (a i) (b j) := by unfold bipartitePrefactor; positivity
  have hsource : |(bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} -
      bipartiteApproximation ell n m a b i j| ≤
      (C*K)*epsilon N p*((a i:ℝ)*b j/m) := by
    apply hs.trans
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herr' hw0) hC.le
    exact hh.trans_eq (by unfold bipartitePrefactor; ring)
  have hc := bipartite_bracket_relative hK hz hw hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 i j
  have happ : |bipartiteApproximation ell n m a b i j - (a i:ℝ)*b j/m| ≤
      (48*K^2*(|A|+1)^2)*epsilon N p*((a i:ℝ)*b j/m) := by
    have heq : bipartiteApproximation ell n m a b i j - (a i:ℝ)*b j/m =
        bipartitePrefactor m (a i) (b j)*(bipartiteBracket ell n m a b i j-1) := by
      unfold bipartiteApproximation bipartitePrefactor
      ring
    rw [heq,abs_mul,abs_of_nonneg hw0]
    exact (mul_le_mul_of_nonneg_left hc hw0).trans_eq (by unfold bipartitePrefactor; ring)
  calc
    _ ≤ |(bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} - bipartiteApproximation ell n m a b i j| +
      |bipartiteApproximation ell n m a b i j - (a i:ℝ)*b j/m| := abs_sub_le _ _ _
    _ ≤ (C*K)*epsilon N p*((a i:ℝ)*b j/m) +
      (48*K^2*(|A|+1)^2)*epsilon N p*((a i:ℝ)*b j/m) := add_le_add hsource happ
    _ = _ := by ring

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
