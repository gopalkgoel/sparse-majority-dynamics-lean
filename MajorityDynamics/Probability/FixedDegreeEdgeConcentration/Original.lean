import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Regime
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Graphical

noncomputable section
universe u v
open scoped BigOperators Classical
open MeasureTheory
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling

/-- Finite numerical consequences of the original density window. -/
structure OriginalScales (N : ℕ) (p T : ℝ) : Prop where
  T_large : 1 < T
  N_pos : 0 < (N : ℝ)
  p_pos : 0 < p
  degree_large : 1 ≤ p*N
  p_le_one : p ≤ 1
  size_large : 16*T^2 ≤ (N : ℝ)
  error_small : (p*N)^((4:ℝ)/7) ≤ p*N/(2*T)
  graphical_bound : (2*T*(p*N))*(2*T*(p*N)+1) ≤ p*N^2/(2*T)

/-- One threshold works before every original graph and bipartite degree vector. -/
theorem eventually_originalScales {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N → OriginalScales N p T := by
  have hT0 : 0 < T := by linarith
  obtain ⟨X,hX,hpow⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=(4:ℝ)/7) (b:=1) (A:=1) (B:=1/(2*T)) (by norm_num) (by positivity)
  obtain ⟨N₀,h₀⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L:=max 1 X) (by positivity)
    (U:=1/(64*T^3)) (by positivity) (M:=16*T^2) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN p hp
  have hw := h₀ N hN p hp.1 hp.2
  have hp0 := hw.2.1
  have hx : 1 ≤ p*N := (le_max_left _ _).trans hw.2.2.2.1
  have hx0 : 0 ≤ p*N := by positivity
  have he := hpow (p*N) ((le_max_right _ _).trans hw.2.2.2.1)
  simp only [one_mul, Real.rpow_one] at he
  have hp1 : p ≤ 1 := by
    apply hw.2.2.2.2.trans
    apply (div_le_iff₀ (by positivity : 0 < 64*T^3)).mpr
    have hT2 : 1 ≤ T^2 := by nlinarith
    have hT3 : 1 ≤ T^3 := by nlinarith [mul_le_mul_of_nonneg_right hT.le (sq_nonneg T)]
    nlinarith
  refine ⟨hT,hw.1,hw.2.1,hx,hp1,hw.2.2.1,by simpa [div_eq_mul_inv,mul_comm] using he,?_⟩
  have hsmall : 12*T^3*p ≤ 1 := by
    have hz := (le_div_iff₀ (by positivity : 0 < 64*T^3)).mp hw.2.2.2.2
    have hn : 0 ≤ T^3*p := by positivity
    nlinarith
  have hTx : 1 ≤ T*(p*N) := by nlinarith
  calc
    (2*T*(p*N))*(2*T*(p*N)+1) ≤ (2*T*(p*N))*(3*T*(p*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = (12*T^3*p)*(p*N^2)/(2*T) := by field_simp; ring
    _ ≤ p*N^2/(2*T) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ p*N^2)]

variable {V : Type u} {L : Type u} {R : Type v} [Fintype V] [Fintype L] [Fintype R]

omit [Fintype L] [Fintype R] in
/-- Actual degree bounds and edge-count scale, derived by summing the original windows. -/
theorem GraphInput.original_bounds {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) :
    (∀ v, p*N/2 ≤ (d v : ℝ) ∧ (d v : ℝ) ≤ 2*(p*N)) ∧
    p*N^2/4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p*N^2 := by
  have hp0 := hs.p_pos
  have hT0 : 0 < T := by linarith [hs.T_large]
  have hr : (p*N)^((4:ℝ)/7) ≤ p*N/2 := by
    apply hs.error_small.trans
    apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs.T_large.le (show 0 ≤ p*N by positivity)]
  have hd : ∀ v, p*N/2 ≤ (d v : ℝ) ∧ (d v : ℝ) ≤ 2*(p*N) := by
    intro v
    have hh := abs_le.mp (hi.degree_window v)
    constructor <;> linarith
  have hlo := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => (hd v).1)
  have hhi := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => (hd v).2)
  have hsum : ∑ v, (d v : ℝ) = 2*(m:ℝ) := by exact_mod_cast hi.total
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hi.card,hsum] at hlo hhi
  refine ⟨hd,?_,?_⟩ <;> nlinarith

omit [Fintype V] in
/-- Both actual bipartite degree sides have one common bound. -/
theorem BipartiteInput.original_bounds {ell N m : ℕ} {p T : ℝ}
    {a : L → ℕ} {b : R → ℕ} (hi : BipartiteInput ell N m p T a b)
    (hs : OriginalScales N p T) :
    (∀ v, p*N/2 ≤ (a v : ℝ) ∧ (a v : ℝ) ≤ 2*T*(p*N)) ∧
    (∀ w, p*N/(2*T) ≤ (b w : ℝ) ∧ (b w : ℝ) ≤ 2*T*(p*N)) ∧
    p*N^2/(2*T) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*T*p*N^2 := by
  have hp0 := hs.p_pos
  have hT0 : 0 < T := by linarith [hs.T_large]
  have hx0 : 0 ≤ p*N := by positivity
  have hcenterlo : p*N/T ≤ p*ell := by
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hi.size_lower hs.p_pos.le
  have hcenterhi : p*ell ≤ T*(p*N) := by
    nlinarith [mul_le_mul_of_nonneg_left hi.size_upper hs.p_pos.le]
  have hTx : p*N ≤ T*(p*N) := by nlinarith [mul_le_mul_of_nonneg_right hs.T_large.le hx0]
  have hr : (p*N)^((4:ℝ)/7) ≤ p*N/2 := by
    apply hs.error_small.trans
    apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
    nlinarith
  have ha : ∀ v, p*N/2 ≤ (a v : ℝ) ∧ (a v : ℝ) ≤ 2*T*(p*N) := by
    intro v
    have hh := abs_le.mp (hi.degree_left v)
    constructor <;> linarith
  have hb : ∀ w, p*N/(2*T) ≤ (b w : ℝ) ∧ (b w : ℝ) ≤ 2*T*(p*N) := by
    intro w
    have hh := abs_le.mp (hi.degree_right w)
    have heq : p*N/T = 2*(p*N/(2*T)) := by ring
    constructor <;> linarith [hs.error_small]
  have hlo := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => (hb w).1)
  have hhi := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => (hb w).2)
  have hsum : ∑ w, (b w : ℝ) = (m:ℝ) := by exact_mod_cast hi.total_right
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hi.card_right,hsum] at hlo hhi
  refine ⟨ha,hb,?_,?_⟩
  · calc
      _ = (N:ℝ)*(p*N/(2*T)) := by ring
      _ ≤ m := hlo
  · nlinarith

omit [Fintype L] [Fintype R] in
theorem GraphInput.realized {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) : (graphFamily d).Nonempty := by
  have hb := hi.original_bounds hs
  have hp0 := hs.p_pos
  have hT0 : 0 < T := by linarith [hs.T_large]
  apply graphFamily_nonempty_of_degree_bound d m (2*T*(p*N)) (by positivity)
  · intro v
    exact (hb.1 v).2.trans (by nlinarith [mul_le_mul_of_nonneg_right hs.T_large.le (show 0 ≤ p*N by positivity)])
  · exact hi.total
  · apply hs.graphical_bound.trans
    apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
    have hm0 : 0 ≤ (m:ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hs.T_large.le hm0]

omit [Fintype V] in
theorem BipartiteInput.realized {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (hs : OriginalScales N p T) :
    (bipartiteFamily a b).Nonempty := by
  have hb := hi.original_bounds hs
  have hp0 := hs.p_pos
  have hT0 : 0 < T := by linarith [hs.T_large]
  apply bipartiteFamily_nonempty_of_degree_bound a b m (2*T*(p*N)) (by positivity)
    (fun v => (hb.1 v).2) (fun w => (hb.2.1 w).2) hi.total_left hi.total_right
  have hh := hs.graphical_bound.trans hb.2.2.1
  nlinarith [show 0 ≤ 2*T*(p*N) by positivity]

omit [Fintype L] [Fintype R] in
theorem GraphInput.normalized {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) :
    IsProbabilityMeasure (fixedDegreeLaw d) := fixedDegreeLaw_normalized d (hi.realized hs)

omit [Fintype V] in
theorem BipartiteInput.normalized {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (hs : OriginalScales N p T) :
    IsProbabilityMeasure (bipartiteFixedDegreeLaw a b) :=
  bipartiteFixedDegreeLaw_normalized a b (hi.realized hs)

omit [Fintype L] [Fintype R] in
theorem GraphInput.count_pos {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) : (0:ℝ) < m := by
  have hp0 := hs.p_pos
  have hN0 := hs.N_pos
  exact (show 0 < p*N^2/4 by positivity).trans_le (hi.original_bounds hs).2.1

omit [Fintype V] in
theorem BipartiteInput.count_pos {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (hs : OriginalScales N p T) : (0:ℝ) < m := by
  have hp0 := hs.p_pos
  have hN0 := hs.N_pos
  have hT0 : 0 < T := by linarith [hs.T_large]
  exact (show 0 < p*N^2/(2*T) by positivity).trans_le (hi.original_bounds hs).2.2.1

omit [Fintype L] [Fintype R] in
theorem GraphInput.degree_ratio {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) (v : V) :
    (d v : ℝ)/m ≤ 8/(N:ℝ) := by
  have hb := hi.original_bounds hs
  apply (div_le_div_iff₀ (hi.count_pos hs) hs.N_pos).mpr
  have hz := mul_le_mul_of_nonneg_right (hb.1 v).2 hs.N_pos.le
  nlinarith [hb.2.1]

omit [Fintype V] in
theorem BipartiteInput.degree_ratios {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (hs : OriginalScales N p T) :
    (∀ v, (a v : ℝ)/m ≤ 4*T^2/(N:ℝ)) ∧ (∀ w, (b w : ℝ)/m ≤ 4*T^2/(N:ℝ)) := by
  have hb := hi.original_bounds hs
  have hT0 : 0 < T := by linarith [hs.T_large]
  have hlo := (div_le_iff₀ (by positivity : 0 < 2*T)).mp hb.2.2.1
  have hprod := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2*T)
  constructor
  · intro v
    apply (div_le_div_iff₀ (hi.count_pos hs) hs.N_pos).mpr
    have hz := mul_le_mul_of_nonneg_right (hb.1 v).2 hs.N_pos.le
    nlinarith
  · intro w
    apply (div_le_div_iff₀ (hi.count_pos hs) hs.N_pos).mpr
    have hz := mul_le_mul_of_nonneg_right (hb.2.1 w).2 hs.N_pos.le
    nlinarith

omit [Fintype L] [Fintype R] in
theorem GraphInput.degree_le_half {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) (v : V) :
    (d v : ℝ) ≤ (m:ℝ)/2 := by
  have hN : 16 ≤ (N:ℝ) := by nlinarith [hs.size_large,hs.T_large]
  have hr : (d v : ℝ)/m ≤ 1/2 := (hi.degree_ratio hs v).trans
    ((div_le_iff₀ hs.N_pos).mpr (by linarith))
  have hh := (div_le_iff₀ (hi.count_pos hs)).mp hr
  linarith

omit [Fintype V] in
theorem BipartiteInput.degrees_le_half {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (hs : OriginalScales N p T) :
    (∀ v, (a v : ℝ) ≤ (m:ℝ)/2) ∧ (∀ w, (b w : ℝ) ≤ (m:ℝ)/2) := by
  have hb := hi.degree_ratios hs
  have hr : 4*T^2/(N:ℝ) ≤ 1/2 := (div_le_iff₀ hs.N_pos).mpr (by nlinarith [hs.size_large,sq_nonneg T])
  constructor
  · intro v
    have hh := (div_le_iff₀ (hi.count_pos hs)).mp ((hb.1 v).trans hr)
    linarith
  · intro w
    have hh := (div_le_iff₀ (hi.count_pos hs)).mp ((hb.2 w).trans hr)
    linarith

omit [Fintype L] [Fintype R] in
theorem GraphInput.toWindow {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) :
    GraphWindow N N m p T 1 d := by
  have hT0 : 0 < T := by linarith [hs.T_large]
  have hn : (N:ℝ) ≤ T*N := by nlinarith [mul_le_mul_of_nonneg_right hs.T_large.le hs.N_pos.le]
  refine ⟨hi.card,(div_le_iff₀ hT0).mpr (by nlinarith),hn,hi.bounded,hi.total,?_,hi.realized hs⟩
  intro v
  simpa only [one_mul] using (hi.degree_window v).trans (by linarith : (p*N)^((4:ℝ)/7) ≤ 1*(p*N)^((4:ℝ)/7)+1)

omit [Fintype V] in
theorem BipartiteInput.toWindow {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (hs : OriginalScales N p T) :
    BipartiteWindow N ell N m p T 1 a b := by
  have hT0 : 0 < T := by linarith [hs.T_large]
  have hn : (N:ℝ) ≤ T*N := by nlinarith [mul_le_mul_of_nonneg_right hs.T_large.le hs.N_pos.le]
  refine ⟨hi.card_left,hi.card_right,hi.size_lower,hi.size_upper,
    (div_le_iff₀ hT0).mpr (by nlinarith),hn,hi.bounded_left,hi.bounded_right,
    hi.total_left,hi.total_right,?_,?_,hi.realized hs⟩
  · intro v
    simpa only [one_mul] using (hi.degree_left v).trans (by linarith : (p*N)^((4:ℝ)/7) ≤ 1*(p*N)^((4:ℝ)/7)+1)
  · intro w
    simpa only [one_mul] using (hi.degree_right w).trans (by linarith : (p*N)^((4:ℝ)/7) ≤ 1*(p*N)^((4:ℝ)/7)+1)

omit [Fintype L] [Fintype R] in
/-- A subset's actual natural degree mass is at most the total degree mass. -/
theorem subset_degree_sum_le (d : V → ℕ) (U : Finset V) :
    (∑ v ∈ U, (d v : ℝ)) ≤ ∑ v, (d v : ℝ) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (by intros; positivity)

omit [Fintype L] [Fintype R] in
theorem GraphInput.subset_mass {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) (U : Finset V) :
    (∑ v ∈ U, (d v : ℝ)) ≤ 2*m ∧ (∑ v ∈ U, (d v : ℝ)) ≤ 2*p*N^2 := by
  have hsum : ∑ v, (d v : ℝ) = 2*(m:ℝ) := by exact_mod_cast hi.total
  have hh := subset_degree_sum_le d U
  rw [hsum] at hh
  exact ⟨hh,by nlinarith [(hi.original_bounds hs).2.2]⟩

omit [Fintype L] [Fintype R] in
/-- The internal-edge center correction is only one expected-degree scale. -/
theorem GraphInput.diagonal_bound {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) (U : Finset V) :
    (∑ v ∈ U, (d v : ℝ)^2)/(4*m) ≤ p*N := by
  have hd := (hi.original_bounds hs).1
  have hm := hi.count_pos hs
  have hp0 := hs.p_pos
  have hsum : (∑ v ∈ U, (d v : ℝ)^2) ≤ 2*(p*N)*(∑ v ∈ U, (d v : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    nlinarith [mul_le_mul_of_nonneg_right (hd v).2 (show 0 ≤ (d v : ℝ) by positivity)]
  have hmass := mul_le_mul_of_nonneg_left (hi.subset_mass hs U).1 (show 0 ≤ 2*(p*N) by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 4*(m:ℝ))).mpr
  nlinarith

theorem OriginalScales.size_two_T {N : ℕ} {p T : ℝ} (hs : OriginalScales N p T) :
    2*T ≤ (N:ℝ) := by nlinarith [hs.size_large,hs.T_large]

theorem OriginalScales.error_ge_one {N : ℕ} {p T : ℝ} (hs : OriginalScales N p T) :
    1 ≤ (p*N)^((4:ℝ)/7) := by
  simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hs.degree_large (by norm_num : (0:ℝ) ≤ 4/7)

theorem OriginalScales.epsilon_ge_inv {N : ℕ} {p T : ℝ} (hs : OriginalScales N p T) :
    1/(N:ℝ) ≤ Numerics.epsilon N p := by
  have hh : 1 ≤ (p*N)^((1:ℝ)/7) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hs.degree_large (by norm_num : (0:ℝ) ≤ 1/7)
  exact div_le_div_of_nonneg_right hh hs.N_pos.le

omit [Fintype L] [Fintype R] in
theorem GraphInput.internal_center_bound {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) (U : Finset V) :
    (∑ v ∈ U, (d v : ℝ))^2/(4*m) ≤ p*N^2 := by
  have hm := hi.count_pos hs
  have hU := (hi.subset_mass hs U).1
  have hU0 : 0 ≤ ∑ v ∈ U, (d v : ℝ) := Finset.sum_nonneg (by intros; positivity)
  apply le_trans _ (hi.original_bounds hs).2.2
  apply (div_le_iff₀ (by positivity : 0 < 4*(m:ℝ))).mpr
  nlinarith [sq_le_sq₀ hU0 (by positivity : 0 ≤ 2*(m:ℝ)) |>.mpr hU]

omit [Fintype L] [Fintype R] in
theorem GraphInput.cut_center_bound {N m : ℕ} {p T : ℝ} {d : V → ℕ}
    (hi : GraphInput N m p T d) (hs : OriginalScales N p T) (U W : Finset V) :
    (∑ v ∈ U, (d v : ℝ))*(∑ w ∈ W, (d w : ℝ))/(2*m) ≤ 2*p*N^2 := by
  have hm := hi.count_pos hs
  have hU := (hi.subset_mass hs U).1
  have hW := (hi.subset_mass hs W).1
  have hW0 : 0 ≤ ∑ w ∈ W, (d w : ℝ) := Finset.sum_nonneg (by intros; positivity)
  have hh := mul_le_mul hU hW hW0 (by positivity : 0 ≤ 2*(m:ℝ))
  have hquot : (∑ v ∈ U, (d v : ℝ))*(∑ w ∈ W, (d w : ℝ))/(2*m) ≤ 2*m := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(m:ℝ))).mpr
    nlinarith
  exact hquot.trans (by nlinarith [(hi.original_bounds hs).2.2])

omit [Fintype V] in
theorem BipartiteInput.subset_masses {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (U : Finset L) (W : Finset R) :
    (∑ v ∈ U, (a v : ℝ)) ≤ m ∧ (∑ w ∈ W, (b w : ℝ)) ≤ m := by
  have hsa : ∑ v, (a v : ℝ) = (m:ℝ) := by exact_mod_cast hi.total_left
  have hsb : ∑ w, (b w : ℝ) = (m:ℝ) := by exact_mod_cast hi.total_right
  exact ⟨by simpa [hsa] using subset_degree_sum_le a U,
    by simpa [hsb] using subset_degree_sum_le b W⟩

omit [Fintype V] in
theorem BipartiteInput.rectangle_center_bound {ell N m : ℕ} {p T : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hi : BipartiteInput ell N m p T a b) (hs : OriginalScales N p T) (U : Finset L) (W : Finset R) :
    (∑ v ∈ U, (a v : ℝ))*(∑ w ∈ W, (b w : ℝ))/m ≤ 2*T*p*N^2 := by
  have hm := hi.count_pos hs
  have hmass := hi.subset_masses U W
  have hW0 : 0 ≤ ∑ w ∈ W, (b w : ℝ) := Finset.sum_nonneg (by intros; positivity)
  have hh := mul_le_mul hmass.1 hmass.2 hW0 hm.le
  apply le_trans _ (hi.original_bounds hs).2.2.2
  exact (div_le_iff₀ hm).mpr hh

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
