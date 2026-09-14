import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Joint
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Original
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Counts
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Relative

/-! Original and one-vertex residual marginal laws give uniform actual edge estimates. -/
noncomputable section
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling
universe u v

/-- One shared marginal constant covers all original and residual graph windows. -/
theorem graph_edges_of_window_bound {N m : ℕ} {p T C : ℝ}
    {V : Type u} [Fintype V] (d : V → ℕ) (hi : GraphInput N m p T d)
    (hs : OriginalScales N p T) (hC : 0 ≤ C) (he : Numerics.epsilon N p ≤ 1)
    (hmargin : ∀ (W : Type u) [Fintype W] (n k : ℕ) (d' : W → ℕ),
      GraphWindow N n k p (2*T+2) 4 d' → ∀ a b, a ≠ b →
      |(fixedDegreeLaw d').real {G | G.Adj a b} - (d' a:ℝ)*d' b/(2*k)| ≤
        C*Numerics.epsilon N p*((d' a:ℝ)*d' b/(2*k))) :
    (∀ e : Sym2 V, ¬e.IsDiag →
      |(fixedDegreeLaw d).real {G | e ∈ G.edgeSet} - graphWeight d m e| ≤
        jointConstant C 8*Numerics.epsilon N p*graphWeight d m e) ∧
    (∀ e f : Sym2 V, ¬e.IsDiag → ¬f.IsDiag → e ≠ f →
      (fixedDegreeLaw d).real {G | e ∈ G.edgeSet ∧ f ∈ G.edgeSet} ≤
        (1+jointConstant C 8*Numerics.epsilon N p)*graphWeight d m e*graphWeight d m f) := by
  have he0 : 0 ≤ Numerics.epsilon N p :=
    (by positivity : 0 ≤ 1/(N:ℝ)).trans hs.epsilon_ge_inv
  have hrpow : 1 ≤ (p*N)^((4:ℝ)/7) := Real.one_le_rpow hs.degree_large (by norm_num)
  have hsize : 2*T ≤ (N:ℝ) := by nlinarith [hs.T_large,hs.size_large]
  have hmarg := hmargin V N m d (original_graph_window N m p T d hi hs.T_large.le hrpow (hi.realized hs))
  have hrat (z : V) : (d z:ℝ)/m ≤ 8*Numerics.epsilon N p := by
    apply (hi.degree_ratio hs z).trans
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hs.epsilon_ge_inv (by norm_num : (0:ℝ) ≤ 8)
  constructor
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro hab
      have hab' : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using hab
      have hh := hmarg a b hab'
      have hw0 : 0 ≤ (d a:ℝ)*d b/(2*m) := by positivity
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_jointConstant hC (by norm_num : (0:ℝ) ≤ 8)) he0) hw0
      simpa only [graphWeight,degreeProduct_mk,SimpleGraph.mem_edgeSet] using hh.trans hmul
  · intro e f
    induction e using Sym2.ind with
    | _ a b =>
      induction f using Sym2.ind with
      | _ x y =>
        intro hab hxy hef
        have hab' : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using hab
        have hxy' : x ≠ y := by simpa only [Sym2.mk_isDiag_iff] using hxy
        have hh := graph_joint_of_marginals d m C 8 (Numerics.epsilon N p)
          (hi.count_pos hs) hC (by norm_num) he0 he (hi.degree_le_half hs) hrat hmarg
          (fun z S hS hn x y hxy => hmargin (Remaining z) (N-1) (m-d z)
            (residualDegree d z S)
            (graph_residual_window N m p T d hi hs.T_large.le hsize hrpow z S hS hn) x y hxy)
          a b x y hab' hxy' hef
        simpa only [graphWeight,degreeProduct_mk,SimpleGraph.mem_edgeSet] using hh

/-- One shared bipartite marginal constant covers deletion on either actual side. -/
theorem bipartite_edges_of_window_bound {ell N m : ℕ} {p T C : ℝ}
    {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (a : L → ℕ) (b : R → ℕ) (hi : BipartiteInput ell N m p T a b)
    (hs : OriginalScales N p T) (hp1 : p ≤ 1) (hC : 0 ≤ C)
    (he : Numerics.epsilon N p ≤ 1)
    (hmargin : ∀ (L' : Type u) (R' : Type v) [Fintype L'] [Fintype R']
      (ell' n k : ℕ) (a' : L' → ℕ) (b' : R' → ℕ),
      BipartiteWindow N ell' n k p (2*T+2) 4 a' b' → ∀ i j,
      |(bipartiteFixedDegreeLaw a' b').real {E | (i,j) ∈ E} - (a' i:ℝ)*b' j/k| ≤
        C*Numerics.epsilon N p*((a' i:ℝ)*b' j/k)) :
    (∀ e : L × R,
      |(bipartiteFixedDegreeLaw a b).real {E | e ∈ E} - bipartiteWeight a b m e| ≤
        jointConstant C (4*T^2)*Numerics.epsilon N p*bipartiteWeight a b m e) ∧
    (∀ e f : L × R, e ≠ f →
      (bipartiteFixedDegreeLaw a b).real {E | e ∈ E ∧ f ∈ E} ≤
        (1+jointConstant C (4*T^2)*Numerics.epsilon N p)*bipartiteWeight a b m e*bipartiteWeight a b m f) := by
  have he0 : 0 ≤ Numerics.epsilon N p :=
    (by positivity : 0 ≤ 1/(N:ℝ)).trans hs.epsilon_ge_inv
  have hrpow : 1 ≤ (p*N)^((4:ℝ)/7) := Real.one_le_rpow hs.degree_large (by norm_num)
  have hsize : 2*T ≤ (N:ℝ) := by nlinarith [hs.T_large,hs.size_large]
  have hK : 0 ≤ 4*T^2 := by positivity
  have hmarg := hmargin L R ell N m a b
    (original_bipartite_window N ell m p T a b hi hs.T_large.le hrpow (hi.realized hs))
  have hrat : 4*T^2/(N:ℝ) ≤ (4*T^2)*Numerics.epsilon N p := by
    simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hs.epsilon_ge_inv hK
  have hratA := fun z => (hi.degree_ratios hs).1 z |>.trans hrat
  have hratB := fun z => (hi.degree_ratios hs).2 z |>.trans hrat
  have hhA := (hi.degrees_le_half hs).1
  have hhB := (hi.degrees_le_half hs).2
  constructor
  · rintro ⟨i,j⟩
    have hh := hmarg i j
    have hw0 : 0 ≤ (a i:ℝ)*b j/m := by positivity
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_jointConstant hC hK) he0) hw0
    exact hh.trans hmul
  · rintro ⟨i,j⟩ ⟨x,y⟩ hne
    exact bipartite_joint_of_marginals a b m C (4*T^2) (Numerics.epsilon N p)
      (hi.count_pos hs) hC hK he0 he hhA hhB hratA hratB hmarg
      (fun z S hS hn x y => hmargin (Remaining z) R (ell-1) N (m-a z)
        (fun w : Remaining z => a w) (residualRightDegree b S)
        (bipartite_left_residual_window N ell m p T a b hi hs.T_large.le hsize hs.p_pos.le hp1 hrpow z S hS hn) x y)
      (fun z S hS hn x y => hmargin L (Remaining z) ell (N-1) (m-b z)
        (residualRightDegree a S) (fun w : Remaining z => b w)
        (bipartite_right_residual_window N ell m p T a b hi hs.T_large.le hsize hs.p_pos.le hp1 hrpow z S hS hn) x y)
      i x j y hne

/-- Uniform graph marginal errors and all distinct-pair upper bounds, with only the
original manuscript density and degree data as input. All constants precede the carrier. -/
theorem uniform_graph_edges {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (V : Type u) [Fintype V] (m : ℕ) (d : V → ℕ),
      GraphInput N m p T d →
      (∀ e : Sym2 V, ¬e.IsDiag →
        |(fixedDegreeLaw d).real {G | e ∈ G.edgeSet} - graphWeight d m e| ≤
          C*Numerics.epsilon N p*graphWeight d m e) ∧
      (∀ e f : Sym2 V, ¬e.IsDiag → ¬f.IsDiag → e ≠ f →
        (fixedDegreeLaw d).real {G | e ∈ G.edgeSet ∧ f ∈ G.edgeSet} ≤
          (1+C*Numerics.epsilon N p)*graphWeight d m e*graphWeight d m f) := by
  obtain ⟨C,hC,N₁,h₁⟩ := graph_window_relative_error.{u} hθlo hθhi hT
    (K:=2*T+2) (A:=4) (by linarith)
  obtain ⟨N₂,h₂⟩ := eventually_originalScales hθlo hθhi hT
  obtain ⟨N₃,h₃⟩ := Numerics.eventually_epsilon hθlo hθhi hT (η:=1) zero_lt_one
  refine ⟨jointConstant C 8, hC.trans_le (le_jointConstant hC.le (by norm_num)),
    max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp V _ m d hi
  have hs := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have he := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2
  exact graph_edges_of_window_bound d hi hs hC.le he.2
    (h₁ N ((le_max_left _ _).trans hN) p hp)

/-- Uniform bipartite edge estimates include both orientations of incident pairs,
using the actual residual laws after deletion on the corresponding side. -/
theorem uniform_bipartite_edges {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      (ell m : ℕ) (a : L → ℕ) (b : R → ℕ),
      BipartiteInput ell N m p T a b →
      (∀ e : L × R,
        |(bipartiteFixedDegreeLaw a b).real {E | e ∈ E} - bipartiteWeight a b m e| ≤
          C*Numerics.epsilon N p*bipartiteWeight a b m e) ∧
      (∀ e f : L × R, e ≠ f →
        (bipartiteFixedDegreeLaw a b).real {E | e ∈ E ∧ f ∈ E} ≤
          (1+C*Numerics.epsilon N p)*bipartiteWeight a b m e*bipartiteWeight a b m f) := by
  obtain ⟨C,hC,N₁,h₁⟩ := bipartite_window_relative_error.{u,v} hθlo hθhi hT
    (K:=2*T+2) (A:=4) (by linarith)
  obtain ⟨N₂,h₂⟩ := eventually_originalScales hθlo hθhi hT
  obtain ⟨N₃,h₃⟩ := Numerics.eventually_epsilon hθlo hθhi hT (η:=1) zero_lt_one
  refine ⟨jointConstant C (4*T^2), hC.trans_le (le_jointConstant hC.le (by positivity)),
    max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp L R _ _ ell m a b hi
  have hs := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have he := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2
  exact bipartite_edges_of_window_bound a b hi hs hs.p_le_one hC.le he.2
    (h₁ N ((le_max_left _ _).trans hN) p hp)

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
