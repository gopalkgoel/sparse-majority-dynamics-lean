import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Residual
import Mathlib.Tactic

noncomputable section
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling

/-- The exact denominator cost of deleting at most half the edges. -/
theorem reciprocal_deletion {m d k ε : ℝ} (hm : 0 < m) (hd : 0 ≤ d)
    (hhalf : d ≤ m/2) (hratio : d/m ≤ k*ε) :
    0 < m-d ∧ m/(m-d) ≤ 1+2*k*ε := by
  have hgap : 0 < m-d := by linarith
  refine ⟨hgap, ?_⟩
  have hdK : d ≤ k*ε*m := (div_le_iff₀ hm).mp hratio
  have hkε : 0 ≤ k*ε := (div_nonneg hd hm.le).trans hratio
  apply (div_le_iff₀ hgap).mpr
  nlinarith [mul_nonneg hkε (show 0 ≤ m-2*d by linarith)]

/-- Deletion can only decrease the endpoint degrees; only the edge-total denominator grows. -/
theorem residual_weight_le {m d a b a' b' k ε c : ℝ}
    (hm : 0 < m) (hd : 0 ≤ d) (hhalf : d ≤ m/2) (hratio : d/m ≤ k*ε)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (ha : a' ≤ a) (hb : b' ≤ b)
    (hc : 0 < c) :
    a'*b'/(c*(m-d)) ≤ (1+2*k*ε)*(a*b/(c*m)) := by
  obtain ⟨hgap,hrec⟩ := reciprocal_deletion hm hd hhalf hratio
  have hab : a'*b' ≤ a*b := mul_le_mul ha hb hb' (ha'.trans ha)
  have ha0 : 0 ≤ a := ha'.trans ha
  have hb0 : 0 ≤ b := hb'.trans hb
  calc
    _ ≤ a*b/(c*(m-d)) := div_le_div_of_nonneg_right hab (by positivity)
    _ = m/(m-d)*(a*b/(c*m)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hrec (by positivity)

/-- Multiplicative one-edge errors remain linear in epsilon on [0,1]. -/
theorem product_relative_errors {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1+a*ε)*(1+b*ε) ≤ 1+(a+b+a*b)*ε := by
  nlinarith [mul_nonneg (mul_nonneg ha hb) (show 0 ≤ ε-ε^2 by nlinarith)]

/-- Uniform constant for one original marginal, one residual marginal, and deletion. -/
def jointConstant (C K : ℝ) : ℝ :=
  C + (C+2*K+C*(2*K)) + C*(C+2*K+C*(2*K))

theorem jointConstant_nonneg {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ jointConstant C K := by unfold jointConstant; positivity

theorem le_jointConstant {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    C ≤ jointConstant C K := by
  unfold jointConstant
  have hh : 0 ≤ C+2*K+C*(2*K) := by positivity
  nlinarith

theorem triple_relative_errors {C K ε : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1+C*ε)*((1+C*ε)*(1+2*K*ε)) ≤ 1+jointConstant C K*ε := by
  have hfirst := product_relative_errors hC (by positivity : 0 ≤ 2*K) hε hε1
  have hsecond := product_relative_errors hC
    (by positivity : 0 ≤ C+2*K+C*(2*K)) hε hε1
  calc
    _ ≤ (1+C*ε)*(1+(C+2*K+C*(2*K))*ε) :=
      mul_le_mul_of_nonneg_left hfirst (by positivity)
    _ ≤ _ := hsecond

/-- Every distinct graph pair is controlled by the actual original and one-vertex
residual marginal laws. No pair estimate is imported. -/
theorem graph_joint_of_marginals {V : Type*} [Fintype V]
    (d : V → ℕ) (m : ℕ) (C K ε : ℝ)
    (hm : 0 < (m:ℝ)) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hhalf : ∀ v, (d v:ℝ) ≤ (m:ℝ)/2)
    (hratio : ∀ v, (d v:ℝ)/m ≤ K*ε)
    (hmarg : ∀ a b : V, a ≠ b →
      |(fixedDegreeLaw d).real {G | G.Adj a b} - (d a:ℝ)*d b/(2*m)| ≤
        C*ε*((d a:ℝ)*d b/(2*m)))
    (hres : ∀ (v : V) (S : Finset V), graphAdmissible d v S →
      (graphFamily (residualDegree d v S)).Nonempty →
      ∀ x y : Remaining v, x ≠ y →
      |(fixedDegreeLaw (residualDegree d v S)).real {G | G.Adj x y} -
        (residualDegree d v S x:ℝ)*residualDegree d v S y/(2*(m-d v:ℕ))| ≤
        C*ε*((residualDegree d v S x:ℝ)*residualDegree d v S y/(2*(m-d v:ℕ))))
    (a b x y : V) (hab : a ≠ b) (hxy : x ≠ y)
    (hef : (s(a,b):Sym2 V) ≠ s(x,y)) :
    (fixedDegreeLaw d).real {G | G.Adj a b ∧ G.Adj x y} ≤
      (1+jointConstant C K*ε)*((d a:ℝ)*d b/(2*m))*((d x:ℝ)*d y/(2*m)) := by
  let wa : ℝ := (d a:ℝ)*d b/(2*m)
  let wb : ℝ := (d x:ℝ)*d y/(2*m)
  have hwa : 0 ≤ wa := by dsimp [wa]; positivity
  have hwb : 0 ≤ wb := by dsimp [wb]; positivity
  have hma : (fixedDegreeLaw d).real {G | G.Adj a b} ≤ (1+C*ε)*wa := by
    have hh := (abs_le.mp (hmarg a b hab)).2
    dsimp [wa]; nlinarith
  have hp := graph_pair_upper_distinct d a b x y hef
    (B := ((1+C*ε)*(1+2*K*ε))*wb) (by
      intro v _ hx hy S hS hn
      have hmn : d v ≤ m := by
        exact_mod_cast (show (d v:ℝ) ≤ m by linarith [hhalf v])
      have hh := hres v S hS hn ⟨x,hx⟩ ⟨y,hy⟩ (fun he => hxy (congrArg Subtype.val he))
      have hr := residual_weight_le hm (Nat.cast_nonneg (d v)) (hhalf v) (hratio v)
        (a := (d x:ℝ)) (b := (d y:ℝ))
        (a' := (residualDegree d v S ⟨x,hx⟩:ℝ))
        (b' := (residualDegree d v S ⟨y,hy⟩:ℝ))
        (by positivity) (by positivity)
        (by exact_mod_cast Nat.sub_le (d x) (if x ∈ S then 1 else 0))
        (by exact_mod_cast Nat.sub_le (d y) (if y ∈ S then 1 else 0))
        (c := 2) (by norm_num)
      rw [← Nat.cast_sub hmn] at hr
      have hu := (abs_le.mp hh).2
      have hmult := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 1+C*ε)
      dsimp [wb]
      nlinarith)
  calc
    _ ≤ (fixedDegreeLaw d).real {G | G.Adj a b} * (((1+C*ε)*(1+2*K*ε))*wb) := hp
    _ ≤ ((1+C*ε)*wa)*(((1+C*ε)*(1+2*K*ε))*wb) :=
      mul_le_mul_of_nonneg_right hma (by positivity)
    _ = ((1+C*ε)*((1+C*ε)*(1+2*K*ε)))*(wa*wb) := by ring
    _ ≤ (1+jointConstant C K*ε)*(wa*wb) :=
      mul_le_mul_of_nonneg_right (triple_relative_errors hC hK hε hε1) (mul_nonneg hwa hwb)
    _ = _ := by ring

/-- A residual marginal and endpoint monotonicity give an upper bound in original weights. -/
theorem residual_probability_upper (m d a b a' b' : ℕ) (C K ε P : ℝ)
    (hm : 0 < (m:ℝ)) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hhalf : (d:ℝ) ≤ (m:ℝ)/2) (hratio : (d:ℝ)/m ≤ K*ε)
    (ha : a' ≤ a) (hb : b' ≤ b)
    (hP : |P - (a':ℝ)*b'/(m-d:ℕ)| ≤ C*ε*((a':ℝ)*b'/(m-d:ℕ))) :
    P ≤ ((1+C*ε)*(1+2*K*ε))*((a:ℝ)*b/m) := by
  have hmn : d ≤ m := by exact_mod_cast (show (d:ℝ) ≤ m by linarith)
  have hr := residual_weight_le hm (Nat.cast_nonneg d) hhalf hratio
    (a := (a:ℝ)) (b := (b:ℝ)) (a' := (a':ℝ)) (b' := (b':ℝ))
    (by positivity) (by positivity) (by exact_mod_cast ha) (by exact_mod_cast hb)
    (c := 1) (by norm_num)
  simp only [one_mul, ← Nat.cast_sub hmn] at hr
  have hu := (abs_le.mp hP).2
  have hmultiply := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 1+C*ε)
  nlinarith

/-- Bipartite pairs use left or right deletion according to which endpoint lies
outside the other edge. This includes both orientations of incident pairs. -/
theorem bipartite_joint_of_marginals {L R : Type*} [Fintype L] [Fintype R]
    (a : L → ℕ) (b : R → ℕ) (m : ℕ) (C K ε : ℝ)
    (hm : 0 < (m:ℝ)) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hhalfA : ∀ v, (a v:ℝ) ≤ (m:ℝ)/2) (hhalfB : ∀ w, (b w:ℝ) ≤ (m:ℝ)/2)
    (hratioA : ∀ v, (a v:ℝ)/m ≤ K*ε) (hratioB : ∀ w, (b w:ℝ)/m ≤ K*ε)
    (hmarg : ∀ v u, |(bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E} -
      (a v:ℝ)*b u/m| ≤ C*ε*((a v:ℝ)*b u/m))
    (hleft : ∀ (v : L) (S : Finset R), bipartiteAdmissible a b v S →
      (bipartiteFamily (fun z : Remaining v => a z) (residualRightDegree b S)).Nonempty →
      ∀ (x : Remaining v) (y : R),
      |(bipartiteFixedDegreeLaw (fun z : Remaining v => a z) (residualRightDegree b S)).real
        {E | (x,y) ∈ E} - (a x:ℝ)*residualRightDegree b S y/(m-a v:ℕ)| ≤
        C*ε*((a x:ℝ)*residualRightDegree b S y/(m-a v:ℕ)))
    (hright : ∀ (u : R) (S : Finset L), bipartiteAdmissible b a u S →
      (bipartiteFamily (residualRightDegree a S) (fun z : Remaining u => b z)).Nonempty →
      ∀ (x : L) (y : Remaining u),
      |(bipartiteFixedDegreeLaw (residualRightDegree a S) (fun z : Remaining u => b z)).real
        {E | (x,y) ∈ E} - (residualRightDegree a S x:ℝ)*b y/(m-b u:ℕ)| ≤
        C*ε*((residualRightDegree a S x:ℝ)*b y/(m-b u:ℕ)))
    (v x : L) (u y : R) (hne : (v,u) ≠ (x,y)) :
    (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E ∧ (x,y) ∈ E} ≤
      (1+jointConstant C K*ε)*((a v:ℝ)*b u/m)*((a x:ℝ)*b y/m) := by
  let wa : ℝ := (a v:ℝ)*b u/m
  let wb : ℝ := (a x:ℝ)*b y/m
  let B : ℝ := ((1+C*ε)*(1+2*K*ε))*wb
  have hwa : 0 ≤ wa := by dsimp [wa]; positivity
  have hwb : 0 ≤ wb := by dsimp [wb]; positivity
  have hma : (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E} ≤ (1+C*ε)*wa := by
    have hh := (abs_le.mp (hmarg v u)).2
    dsimp [wa]; nlinarith
  have hp : (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E ∧ (x,y) ∈ E} ≤
      (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E} * B := by
    by_cases hx : x ≠ v
    · apply bipartite_joint_le_of_left_residual a b v x u y hx B
      intro S hS hn
      exact residual_probability_upper m (a v) (a x) (b y) (a x)
        (residualRightDegree b S y) C K ε _ hm hC hε (hhalfA v) (hratioA v)
        le_rfl (Nat.sub_le _ _) (hleft v S hS hn ⟨x,hx⟩ y)
    · have hy : y ≠ u := by
        intro he
        apply hne
        exact Prod.ext (not_ne_iff.mp hx).symm he.symm
      apply bipartite_joint_le_of_right_residual a b v x u y hy B
      intro S hS hn
      exact residual_probability_upper m (b u) (a x) (b y)
        (residualRightDegree a S x) (b y) C K ε _ hm hC hε (hhalfB u) (hratioB u)
        (Nat.sub_le _ _) le_rfl (hright u S hS hn x ⟨y,hy⟩)
  calc
    _ ≤ (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E} * B := hp
    _ ≤ ((1+C*ε)*wa)*B := mul_le_mul_of_nonneg_right hma (by dsimp [B]; positivity)
    _ = ((1+C*ε)*((1+C*ε)*(1+2*K*ε)))*(wa*wb) := by dsimp [B]; ring
    _ ≤ (1+jointConstant C K*ε)*(wa*wb) :=
      mul_le_mul_of_nonneg_right (triple_relative_errors hC hK hε hε1) (mul_nonneg hwa hwb)
    _ = _ := by ring

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
