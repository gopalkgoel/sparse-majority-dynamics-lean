import MajorityDynamics.Literature.EdgeProbabilities.Applications
import MajorityDynamics.Literature.EdgeProbabilities.Growth
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Regime

/-! Uniform source formulas from the original sparse-density and degree windows. -/
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology Classical
namespace MajorityDynamics.Literature.EdgeProbabilities
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
universe u v

/-- Original density windows give a fixed polynomial scale for the expected degree. -/
theorem window_degree_isTheta {N : ℕ → ℕ} {p : ℕ → ℝ} {θ T : ℝ}
    (hT : 0 < T) (hN : Tendsto N atTop atTop)
    (hp : ∀ k, DensityWindow θ T (p k) (N k)) :
    (fun k => p k * N k) =Θ[atTop] (fun k => (N k : ℝ)^(1-θ)) := by
  have hpos := (tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)
  apply isTheta_of_eventual_bounds (c := T⁻¹) (C := T) (inv_pos.mpr hT)
  · filter_upwards [hpos] with k hk
    have hpk : 0 < p k := (mul_pos (inv_pos.mpr hT)
      (Real.rpow_pos_of_pos hk _)).trans (hp k).1
    positivity
  · exact .of_forall fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  · filter_upwards [hpos] with k hk
    change 0 < (N k : ℝ) at hk
    have hlo := mul_le_mul_of_nonneg_right (hp k).1.le hk.le
    have hhi := mul_le_mul_of_nonneg_right (hp k).2.le hk.le
    have heq : (N k : ℝ)^(-θ) * N k = (N k : ℝ)^(1-θ) := by
      rw [rpow_mul_self hk]
      congr 1
      ring
    exact ⟨by simpa only [mul_assoc, heq] using hlo,
      by simpa only [mul_assoc, heq] using hhi⟩

/-- A comparable side and comparable actual mean recover the total polynomial scale. -/
theorem total_isTheta_of_average {N n m : ℕ → ℕ} {p : ℕ → ℝ} {θ : ℝ}
    (hN : Tendsto N atTop atTop)
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hp : (fun k => p k * N k) =Θ[atTop] (fun k => (N k : ℝ)^(1-θ)))
    (hm : (fun k => (m k : ℝ)/(n k : ℝ)) =Θ[atTop] (fun k => p k*N k)) :
    (fun k => (m k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)^(2-θ)) := by
  have hprod := (hm.trans hp).mul hn
  have heq : (fun k => (N k : ℝ)^(1-θ)*N k) =ᶠ[atTop]
      (fun k => (N k : ℝ)^(2-θ)) := by
    filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)] with k hk
    change 0 < (N k : ℝ) at hk
    rw [rpow_mul_self hk]
    congr 1
    ring
  have heqleft : (fun k => (m k : ℝ)) =ᶠ[atTop]
      (fun k => (m k : ℝ)/(n k : ℝ)*n k) := by
    filter_upwards [(tendsto_natCast_atTop_atTop.comp (nat_tendsto_of_isTheta hN hn)).eventually_gt_atTop (0 : ℝ)] with k hk
    change 0 < (n k : ℝ) at hk
    rw [div_mul_cancel₀ _ hk.ne']
  exact heqleft.trans_isTheta (hprod.trans_eventuallyEq heq)

/-- Pack the arbitrary carrier so source uniformity includes the graph and queried vertices. -/
structure GraphWindowDatum where
  N : ℕ
  n : ℕ
  m : ℕ
  p : ℝ
  V : Type u
  fintype : Fintype V
  d : V → ℕ
  a : V
  b : V
attribute [instance] GraphWindowDatum.fintype

private theorem graph_datum_bound {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ x : GraphWindowDatum.{u}, N₀ ≤ x.N →
      DensityWindow θ T x.p x.N → GraphWindow x.N x.n x.m x.p K A x.d → x.a ≠ x.b →
      |(fixedDegreeLaw x.d).real {G | G.Adj x.a x.b} -
        graphApproximation x.n x.m (x.d x.a) (x.d x.b)| ≤ C*graphErrorScale x.n x.m := by
  let Valid (x : GraphWindowDatum.{u}) := DensityWindow θ T x.p x.N ∧
    GraphWindow x.N x.n x.m x.p K A x.d ∧ x.a ≠ x.b
  suffices hh : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ x : GraphWindowDatum.{u}, N₀ ≤ x.N → Valid x →
      |(fixedDegreeLaw x.d).real {G | G.Adj x.a x.b} -
        graphApproximation x.n x.m (x.d x.a) (x.d x.b)| ≤ C*graphErrorScale x.n x.m by
    obtain ⟨C,hC,N₀,hh⟩ := hh
    exact ⟨C,hC,N₀,fun x hn hp hw hab => hh x hn ⟨hp,hw,hab⟩⟩
  apply uniform_bound_of_sequence_bound (fun x => x.N) Valid
  · intro x _
    unfold graphErrorScale graphAverage
    positivity
  · intro x hx hN
    have hK0 : 0 < K := by linarith
    have hT0 : 0 < T := by linarith
    have hn : (fun k => ((x k).n : ℝ)) =Θ[atTop] (fun k => ((x k).N : ℝ)) := by
      apply isTheta_of_eventual_bounds (c := K⁻¹) (C := K) (inv_pos.mpr hK0)
      · exact .of_forall fun k => Nat.cast_nonneg _
      · exact .of_forall fun k => Nat.cast_nonneg _
      · exact .of_forall fun k => ⟨by simpa [div_eq_mul_inv,mul_comm] using (hx k).2.1.size_lower,
          (hx k).2.1.size_upper⟩
    have hp := window_degree_isTheta hT0 hN (fun k => (hx k).1)
    obtain ⟨N₁,h₁⟩ := Numerics.eventually_graphWindow.{u} hθlo hθhi hT hK (A:=A)
    have hev := (hN.eventually_ge_atTop N₁).mono fun k hk =>
      h₁ (x k).N hk (x k).p (hx k).1 (x k).V (x k).n (x k).m (x k).d (hx k).2.1
    have hav : (fun k => graphAverage (x k).n (x k).m) =Θ[atTop]
        (fun k => (x k).p*(x k).N) := by
      apply isTheta_of_eventual_bounds (c := (2*K)⁻¹) (C := 2*K) (by positivity)
      · exact .of_forall fun _ => by unfold graphAverage; positivity
      · filter_upwards [hev, (hN.eventually_gt_atTop 0)] with k hk hkN
        have hNp : (0:ℝ) < (x k).N := by exact_mod_cast hkN
        have hpp := (mul_pos (inv_pos.mpr hT0) (Real.rpow_pos_of_pos hNp (-θ))).trans (hx k).1.1
        positivity
      · filter_upwards [hev] with k hk
        exact ⟨by simpa [div_eq_mul_inv,mul_comm] using hk.2.1, hk.2.2⟩
    have hav' : (fun k => 2*(((x k).m : ℝ)/(x k).n)) =Θ[atTop]
        (fun k => (x k).p*(x k).N) := by
      simpa only [graphAverage, mul_div_assoc] using hav
    have hm := total_isTheta_of_average hN hn hp
      (hav'.of_const_mul_left (by norm_num : (2:ℝ) ≠ 0))
    obtain ⟨hd,hl⟩ := graph_sequence_growth (by linarith : 0 < θ) hθhi hN hn hm
    obtain ⟨μ₀,hμ₀,hsource⟩ := graph_edge_probability.{u}
    obtain ⟨C,hC,hbound⟩ := hsource ((7:ℝ)/12) (by norm_num) (by norm_num)
      (fun k => (x k).n) (fun k => (x k).m) (nat_tendsto_of_isTheta hN hn)
      (hd.eventually_le_const hμ₀) hl
    refine ⟨C,hC,?_⟩
    filter_upwards [hev,hbound] with k hk hb
    exact hb (x k).V (x k).d hk.1 (x k).a (x k).b (hx k).2.2

/-- LW17's full formula on the original window, uniformly in all data and vertices. -/
theorem graph_window_source_error {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (V : Type u) [Fintype V] (n m : ℕ) (d : V → ℕ),
      GraphWindow N n m p K A d → ∀ a b, a ≠ b →
      |(fixedDegreeLaw d).real {G | G.Adj a b} - graphApproximation n m (d a) (d b)| ≤
        C*graphErrorScale n m := by
  obtain ⟨C,hC,N₀,hh⟩ := graph_datum_bound.{u} hθlo hθhi hT hK (A:=A)
  exact ⟨C,hC,N₀,fun N hN p hp V f n m d hw a b hab =>
    hh ⟨N,n,m,p,V,f,d,a,b⟩ hN hp hw hab⟩

-- The packed data intentionally contain two independent carrier universes.
set_option linter.checkUnivs false in
/-- Pack both arbitrary carrier types and a queried bipartite edge. -/
structure BipartiteWindowDatum where
  N : ℕ
  ell : ℕ
  n : ℕ
  m : ℕ
  p : ℝ
  L : Type u
  R : Type v
  fintypeL : Fintype L
  fintypeR : Fintype R
  a : L → ℕ
  b : R → ℕ
  i : L
  j : R
attribute [instance] BipartiteWindowDatum.fintypeL BipartiteWindowDatum.fintypeR

private theorem bipartite_datum_bound {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ x : BipartiteWindowDatum.{u,v}, N₀ ≤ x.N →
      DensityWindow θ T x.p x.N → BipartiteWindow x.N x.ell x.n x.m x.p K A x.a x.b →
      |(bipartiteFixedDegreeLaw x.a x.b).real {E | (x.i,x.j) ∈ E} -
        bipartiteApproximation x.ell x.n x.m x.a x.b x.i x.j| ≤
          C*(bipartitePrefactor x.m (x.a x.i) (x.b x.j)*
            bipartiteErrorScale x.ell x.n x.m ((7:ℝ)/12)) := by
  let Valid (x : BipartiteWindowDatum.{u,v}) := DensityWindow θ T x.p x.N ∧
    BipartiteWindow x.N x.ell x.n x.m x.p K A x.a x.b
  suffices hh : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ x : BipartiteWindowDatum.{u,v}, N₀ ≤ x.N → Valid x →
      |(bipartiteFixedDegreeLaw x.a x.b).real {E | (x.i,x.j) ∈ E} -
        bipartiteApproximation x.ell x.n x.m x.a x.b x.i x.j| ≤
          C*(bipartitePrefactor x.m (x.a x.i) (x.b x.j)*
            bipartiteErrorScale x.ell x.n x.m ((7:ℝ)/12)) by
    obtain ⟨C,hC,N₀,hh⟩ := hh
    exact ⟨C,hC,N₀,fun x hn hp hw => hh x hn ⟨hp,hw⟩⟩
  apply uniform_bound_of_sequence_bound (fun x => x.N) Valid
  · intro x _
    unfold bipartitePrefactor bipartiteErrorScale leftAverage rightAverage
    positivity
  · intro x hx hN
    have hK0 : 0 < K := by linarith
    have hT0 : 0 < T := by linarith
    have hn : (fun k => ((x k).n : ℝ)) =Θ[atTop] (fun k => ((x k).N : ℝ)) := by
      apply isTheta_of_eventual_bounds (c := K⁻¹) (C := K) (inv_pos.mpr hK0)
      · exact .of_forall fun k => Nat.cast_nonneg _
      · exact .of_forall fun k => Nat.cast_nonneg _
      · exact .of_forall fun k => ⟨by simpa [div_eq_mul_inv,mul_comm] using (hx k).2.size_right_lower,
          (hx k).2.size_right_upper⟩
    have hell : (fun k => ((x k).ell : ℝ)) =Θ[atTop] (fun k => ((x k).N : ℝ)) := by
      apply isTheta_of_eventual_bounds (c := K⁻¹) (C := K) (inv_pos.mpr hK0)
      · exact .of_forall fun k => Nat.cast_nonneg _
      · exact .of_forall fun k => Nat.cast_nonneg _
      · exact .of_forall fun k => ⟨by simpa [div_eq_mul_inv,mul_comm] using (hx k).2.size_left_lower,
          (hx k).2.size_left_upper⟩
    have hp := window_degree_isTheta hT0 hN (fun k => (hx k).1)
    obtain ⟨N₁,h₁⟩ := Numerics.eventually_bipartiteWindow.{u,v} hθlo hθhi hT hK (A:=A)
    have hev := (hN.eventually_ge_atTop N₁).mono fun k hk =>
      h₁ (x k).N hk (x k).p (hx k).1 (x k).L (x k).R
        (x k).ell (x k).n (x k).m (x k).a (x k).b (hx k).2
    have hav : (fun k => rightAverage (x k).n (x k).m) =Θ[atTop]
        (fun k => (x k).p*(x k).N) := by
      apply isTheta_of_eventual_bounds (c := (2*K)⁻¹) (C := 2*K) (by positivity)
      · exact .of_forall fun _ => by unfold rightAverage; positivity
      · filter_upwards [(hN.eventually_gt_atTop 0)] with k hkN
        have hNp : (0:ℝ) < (x k).N := by exact_mod_cast hkN
        have hpp := (mul_pos (inv_pos.mpr hT0) (Real.rpow_pos_of_pos hNp (-θ))).trans (hx k).1.1
        positivity
      · filter_upwards [hev] with k hk
        exact ⟨by simpa [div_eq_mul_inv,mul_comm] using hk.2.2.2.1, hk.2.2.2.2⟩
    have hm := total_isTheta_of_average hN hn hp hav
    obtain ⟨hellTop,hd,hpowers,hlogs⟩ := bipartite_sequence_growth
      (by linarith : 0 < θ) hθhi hN hell hn hm
    obtain ⟨μ₀,hμ₀,hsource⟩ := bipartite_edge_probability.{u,v}
    obtain ⟨C,hC,hbound⟩ := hsource ((7:ℝ)/12) (by norm_num) (by norm_num)
      (fun k => (x k).ell) (fun k => (x k).n) (fun k => (x k).m)
      (nat_tendsto_of_isTheta hN hn) hellTop (hd.eventually_lt_const hμ₀) hpowers hlogs
    refine ⟨C,hC,?_⟩
    filter_upwards [hev,hbound] with k hk hb
    simpa only [mul_left_comm] using
      hb (x k).L (x k).R (x k).a (x k).b hk.1 (x k).i (x k).j

/-- LW20's full variance-corrected formula on the original window. The error retains
its degree prefactor; the uniform constants precede both carriers and every edge. -/
theorem bipartite_window_source_error {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ),
      BipartiteWindow N ell n m p K A a b → ∀ i j,
      |(bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} -
        bipartiteApproximation ell n m a b i j| ≤
          C*(bipartitePrefactor m (a i) (b j)*bipartiteErrorScale ell n m ((7:ℝ)/12)) := by
  obtain ⟨C,hC,N₀,hh⟩ := bipartite_datum_bound.{u,v} hθlo hθhi hT hK (A:=A)
  exact ⟨C,hC,N₀,fun N hN p hp L R fL fR ell n m a b hw i j =>
    hh ⟨N,ell,n,m,p,L,R,fL,fR,a,b,i,j⟩ hN hp hw⟩

end MajorityDynamics.Literature.EdgeProbabilities
