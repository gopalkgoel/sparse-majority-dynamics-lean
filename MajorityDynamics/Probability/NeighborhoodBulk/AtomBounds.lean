import MajorityDynamics.Probability.NeighborhoodBulk.CountControl
import MajorityDynamics.Probability.NeighborhoodBulk.WeightBridges
import MajorityDynamics.Combinatorics.DegreeRatios.Main

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Combinatorics.DegreeRatios

theorem bound_enlarge {P Q A B : ℝ} (hQ : 0 ≤ Q) (hAB : A ≤ B)
    (h : Real.exp (-A) * Q ≤ P ∧ P ≤ Real.exp A * Q) :
    Real.exp (-B) * Q ≤ P ∧ P ≤ Real.exp B * Q := by
  exact ⟨(mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hAB)) hQ).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hAB) hQ)⟩

theorem log_error_enlarge {L C T : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C) (hT : 1 < T) :
    (16400 * L ^ 4 + 1 + (1025 * L ^ 4 + 1)) + C * L + 32 * (T + 1) * L ^ 2 ≤
      (17427 + C + 32 * (T + 1)) * L ^ 4 := by
  have hL0 : 0 ≤ L := by linarith
  have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have h4 : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have h24 : L ^ 2 ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  have h14 : L ≤ L ^ 4 := by nlinarith [mul_nonneg hL0 (by linarith : 0 ≤ L - 1)]
  have hC' := mul_le_mul_of_nonneg_left h14 hC
  have hT' := mul_le_mul_of_nonneg_left h24 (by linarith : 0 ≤ 32 * (T + 1))
  nlinarith

theorem graph_atom_bounds (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (R : Finset (Fin n)), v ∉ R → R.card = (d v).toNat →
          MultiplicativeBound C n
            ((fixedDegreeLaw (fun i => (d i).toNat)).real {G | G.neighborFinset v = R})
            (Real.exp (graphWeight p d v R) / ((n - 1).choose (d v).toNat : ℝ)) := by
  obtain ⟨C, N, hC, _, hratio⟩ := graph_degree_ratio θ T hθlo hθhi hT
  refine ⟨17427 + C + 32 * (T + 1), by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (3 : ℕ),
    eventually_large_parameters θ T hθlo hθhi hT,
    eventually_graph_count_control θ T hθlo hθhi hT,
    eventually_graph_residual_count_control θ T hθlo hθhi hT,
    eventually_graph_residual_source θ T hθlo hθhi hT,
    eventually_graph_profile θ T hθlo hθhi hT] with n hnN hn hl ho hr hs hpB
  intro p hp m d hd v R hv hR
  have hlarge := hl p hp
  have hx : 0 < p * n := mul_pos hlarge.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hdwin : DegreeWindow n p (d v) :=
    (standardizedDegree_bound_iff p n (d v) (Real.log n) hx).mp (hd.2.2.2 v)
  have hc3 := hratio n hnN p hp m (d v) ⟨hd.2.2.1, hdwin⟩
  have hdo : ∀ i, (d i).toNat ≤ n - 1 := by intro i; have := hd.1 i; omega
  have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (graph_input_nat_sum hd).1
  have hdn : ∀ i, ((d i).toNat : ℤ) = d i := fun i => Int.toNat_of_nonneg (hd.1 i).1
  have hdreal : ∀ i, ((d i).toNat : ℝ) = (d i : ℝ) := by intro i; exact_mod_cast hdn i
  have hmod := graph_model_ratio (m := m.toNat) (fun i => (d i).toNat) v R (by omega) hv hdo
    (hs p hp m d hd v R hv hR).1.2.2
  rw [hmn, hdn] at hmod
  simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, hdreal] at hmod
  have horig := ho p hp m d hd
  have hres := hr p hp m d hd v R hv hR
  have hprof := hpB p hp m d hd v R hv hR
  have hchoose : 0 < ((n - 1).choose (d v).toNat : ℝ) := by
    exact_mod_cast Nat.choose_pos (hdo v)
  have hlog := count_ratio_log_control hres.2.1 horig.2.1 hres.1 horig.1 hres.2.2 horig.2.2
  have hbound := profile_ratio_log_control
    (z := (d v : ℝ) * Real.log p - p * n) (w := graphWeight p d v R)
    (D := C * Real.log n) (E := 32 * (T + 1) * Real.log n ^ 2) (div_pos hres.2.1 horig.2.1) hc3.2.1 hprof.1
    hchoose hmod hlog
    (by convert hc3.2.2 using 1; congr 1; ring)
    (by convert hprof.2 using 1; congr 1; ring)
  have he := bound_enlarge (le_of_lt (div_pos (Real.exp_pos _) hchoose))
    (log_error_enlarge hlarge.2.1 hC.le hT) hbound
  unfold MultiplicativeBound
  rw [graph_removal_real _ _ _ (hs p hp m d hd v R hv hR).1]
  rw [graphResidualFin_count] at he
  simp only [neg_mul]
  convert he using 1 <;> congr!

theorem bipartite_atom_bounds (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (R : Finset (Fin n)), R.card = (a v).toNat →
            MultiplicativeBound C n
              ((bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)).real
                {E | leftNeighbors E v = R})
              (Real.exp (bipartiteWeight p ell b R) / (n.choose (a v).toNat : ℝ)) := by
  obtain ⟨C, N, hC, _, hratio⟩ := bipartite_degree_ratio θ T hθlo hθhi hT
  refine ⟨17427 + C + 32 * (T + 1), by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (3 : ℕ),
    eventually_large_parameters θ T hθlo hθhi hT,
    eventually_bipartite_count_control θ T hθlo hθhi hT,
    eventually_bipartite_residual_count_control θ T hθlo hθhi hT,
    eventually_bipartite_residual_source θ T hθlo hθhi hT,
    eventually_bipartite_profile θ T hθlo hθhi hT] with n hnN hn hl ho hr hs hpB
  intro p hp ell m a b hd v R hR
  have hlarge := hl p hp
  have hx : 0 < p * n := mul_pos hlarge.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hdwin : DegreeWindow n p (a v) :=
    (standardizedDegree_bound_iff p n (a v) (Real.log n) hx).mp (hd.2.2.2.2.2.2.2.1 v)
  have hc3 := hratio n hnN p hp ell m (a v)
    ⟨by simpa only [div_eq_mul_inv, mul_comm] using hd.1, hd.2.1, hd.2.2.2.2.2.2.1, hdwin⟩
  have ha : ∀ i, (a i).toNat ≤ n := by intro i; have := hd.2.2.1 i; omega
  have hb : ∀ j, (b j).toNat ≤ ell.toNat := by intro j; have := hd.2.2.2.1 j; omega
  have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (bipartite_input_nat_sums hd).1
  have helln : (ell.toNat : ℤ) = ell := Int.toNat_of_nonneg (by have := hc3.1.1; omega)
  have han : ∀ i, ((a i).toNat : ℤ) = a i := fun i => Int.toNat_of_nonneg (hd.2.2.1 i).1
  have hbreal : ∀ j, ((b j).toNat : ℝ) = (b j : ℝ) := by
    intro j
    exact_mod_cast Int.toNat_of_nonneg (hd.2.2.2.1 j).1
  have hellreal : (ell.toNat : ℝ) = (ell : ℝ) := by exact_mod_cast helln
  have hmod := bipartite_model_ratio (m := m.toNat) (fun i => (a i).toNat)
    (fun j => (b j).toNat) v R (by have := hc3.1.1; omega) ha hb
    (hs p hp ell m a b hd v R hR).1.2
  rw [hmn, helln, han] at hmod
  simp only [hbreal, hellreal] at hmod
  have horig := ho p hp ell m a b hd
  have hres := hr p hp ell m a b hd v R hR
  have hprof := hpB p hp ell m a b hd v R hR
  have hchoose : 0 < (n.choose (a v).toNat : ℝ) := by exact_mod_cast Nat.choose_pos (ha v)
  have hlog := count_ratio_log_control hres.2.1 horig.2.1 hres.1 horig.1 hres.2.2 horig.2.2
  have hlog' : |Real.log ((bipartiteCount (leftResidualFin (fun i => (a i).toNat) v)
      (residualRightDegree (fun j => (b j).toNat) R) : ℝ) /
        bipartiteCount (fun i => (a i).toNat) (fun j => (b j).toNat)) -
      Real.log (bipartiteCountModel (m.toNat - (a v).toNat)
        (leftResidualFin (fun i => (a i).toNat) v) (residualRightDegree (fun j => (b j).toNat) R) /
        bipartiteCountModel m.toNat (fun i => (a i).toNat) (fun j => (b j).toNat))| ≤
      16400 * Real.log n ^ 4 + 1 + (1025 * Real.log n ^ 4 + 1) := by
    exact hlog.trans (by nlinarith [(by positivity : 0 ≤ Real.log n ^ 4)])
  have hbound := profile_ratio_log_control
    (z := (a v : ℝ) * Real.log p - p * n) (w := bipartiteWeight p ell b R)
    (D := C * Real.log n) (E := 32 * (T + 1) * Real.log n ^ 2)
    (div_pos hres.2.1 horig.2.1) hc3.2.1 hprof.1 hchoose hmod hlog'
    (by convert hc3.2.2 using 1; congr 1; ring)
    (by convert hprof.2 using 1; congr 1; ring)
  have he := bound_enlarge (le_of_lt (div_pos (Real.exp_pos _) hchoose))
    (log_error_enlarge hlarge.2.1 hC.le hT) hbound
  unfold MultiplicativeBound
  rw [bipartite_removal_real _ _ _ _ (hs p hp ell m a b hd v R hR).1]
  rw [bipartiteResidualFin_count] at he
  simp only [neg_mul]
  convert he using 1 <;> congr!

end MajorityDynamics.Probability.NeighborhoodBulk
