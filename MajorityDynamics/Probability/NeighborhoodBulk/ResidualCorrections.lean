import MajorityDynamics.Probability.NeighborhoodBulk.ResidualEnumeration
import MajorityDynamics.Probability.NeighborhoodBulk.CorrectionBounds

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem graph_correction_of_control {n m : ℕ} (d : Fin n → ℕ) (x L : ℝ)
    (hn : 2 ≤ n) (hx : 0 < x) (hL : 1 ≤ L) (hρ : graphDensity n m ≤ 1 / 2)
    (h : CenteredControl d (graphAverage n m) x L) :
    Real.exp (-1025 * L ^ 4) ≤ graphCorrection m d ∧
      graphCorrection m d ≤ Real.exp (1025 * L ^ 4) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) - 1 := by linarith
  have hav : 0 < graphAverage n m := (by positivity : 0 < x / 2).trans_le h.2.1
  have hμ : 0 < graphDensity n m := div_pos hav hN
  have hsum := centered_square_sum_le (fun i => (d i : ℝ)) (graphAverage n m)
    (2 * (Real.sqrt x * L)) (by positivity) h.2.2
  have hsum' : (∑ i, ((d i : ℝ) - graphAverage n m) ^ 2) ≤ (n : ℝ) * (4 * x * L ^ 2) := by
    simpa only [Fintype.card_fin, mul_pow, Real.sq_sqrt hx.le,
      show (2 : ℝ)^2 = 4 by norm_num, mul_assoc] using hsum
  have hsum'' : (∑ i, ((d i : ℝ) - graphAverage n m) ^ 2) ≤
      16 * ((n : ℝ) - 1) * graphAverage n m * L ^ 2 := by
    calc
      _ ≤ (n : ℝ) * (4 * x * L ^ 2) := hsum'
      _ ≤ (n : ℝ) * (8 * graphAverage n m * L ^ 2) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (by linarith [h.2.1] : 4 * x ≤ 8 * graphAverage n m) (sq_nonneg _)) (by positivity)
      _ ≤ (2 * ((n : ℝ) - 1)) * (8 * graphAverage n m * L ^ 2) := by gcongr; linarith
      _ = _ := by ring
  have hγ : graphGamma m d ≤ 16 * graphDensity n m * L ^ 2 := by
    unfold graphGamma graphDensity
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    have he : 16 * (graphAverage n m / ((n : ℝ) - 1)) * L ^ 2 * ((n : ℝ) - 1) ^ 2 =
        16 * ((n : ℝ) - 1) * graphAverage n m * L ^ 2 := by field_simp
    rw [he]
    exact hsum''
  have hγ32 : graphGamma m d ≤ 32 * graphDensity n m * (1 - graphDensity n m) * L ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ 32 * graphDensity n m * L ^ 2)
    nlinarith
  simpa only [show (32 : ℝ)^2 + 1 = 1025 by norm_num] using
    graphCorrection_bounds d 32 L (by norm_num) hL hμ (by linarith) hγ32

theorem bipartite_correction_of_control {ell n m : ℕ} (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (x y L : ℝ) (hell : 0 < ell) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hL : 1 ≤ L)
    (hρ : bipartiteDensity ell n m ≤ 1 / 2)
    (ha : CenteredControl a (leftAverage ell m) x L)
    (hb : CenteredControl b (rightAverage n m) y L) :
    Real.exp (-289 * L ^ 4) ≤ bipartiteCorrection m a b ∧
      bipartiteCorrection m a b ≤ Real.exp (289 * L ^ 4) := by
  have : Nonempty (Fin ell) := Fin.pos_iff_nonempty.mp hell
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hA := variance_ratio_bounds (fun i => (a i : ℝ)) (leftAverage ell m)
    x (bipartiteDensity ell n m) L hx (by linarith) ha.2.1 hρ ha.2.2
  have hB := variance_ratio_bounds (fun j => (b j : ℝ)) (rightAverage n m)
    y (bipartiteDensity ell n m) L hy (by linarith) hb.2.1 hρ hb.2.2
  simp only [Fintype.card_fin] at hA hB
  simpa only [show ((16 : ℝ) + 1)^2 = 289 by norm_num] using
    bipartiteCorrection_bounds a b 16 L (by norm_num) hL hA.1 hB.1 hA.2 hB.2

theorem eventually_graph_residual_correction (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          let d' := graphResidualFin (fun i => (d i).toNat) v S
          let m' := m.toNat - (d v).toNat
          Real.exp (-16400 * Real.log n ^ 4) ≤ graphCorrection m' d' ∧
            graphCorrection m' d' ≤ Real.exp (16400 * Real.log n ^ 4) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_graph_scale_domain θ (16 * T) (1 / 2) (by linarith) (by linarith) (by norm_num))
  filter_upwards [eventually_ge_atTop (N + 1), eventually_ge_atTop (3 : ℕ),
    eventually_large_parameters θ T hθlo hθhi hT,
    eventually_graph_residual_regular θ T hθlo hθhi hT,
    eventually_graph_residual_scale θ T hθlo hθhi hT] with n hnN hn hlarge hregular hscale
  intro p hp m d hd v S hv hS
  have hl := hlarge p hp
  have hcontrol := (hregular p hp m d hd v S hv hS).2.2
  have hρ := (hN (n - 1) (by omega) _ (hscale p hp m d hd v)).2.1
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hh := graph_correction_of_control _ (p * n) (2 * Real.log n) (by omega) hx
    (by linarith [hl.2.1]) hρ hcontrol
  norm_num [mul_pow, ← mul_assoc] at hh
  simpa only [neg_mul] using hh

theorem eventually_bipartite_residual_correction (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (S : Finset (Fin n)), S.card = (a v).toNat →
            let a' := leftResidualFin (fun i => (a i).toNat) v
            let b' := residualRightDegree (fun j => (b j).toNat) S
            let m' := m.toNat - (a v).toNat
            Real.exp (-4624 * Real.log n ^ 4) ≤ bipartiteCorrection m' a' b' ∧
              bipartiteCorrection m' a' b' ≤ Real.exp (4624 * Real.log n ^ 4) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_large_parameters θ T hθlo hθhi hT,
    eventually_bipartite_residual_regular θ T hθlo hθhi hT,
    eventually_bipartite_residual_scale θ T hθlo hθhi hT,
    eventually_bipartite_degree_room θ T hθlo hθhi hT,
    eventually_bipartite_scale_domain θ (8 * T ^ 2) (1 / 2) (by linarith) (by nlinarith)
      (by norm_num)] with n hn hlarge hregular hscale hroom hdom
  intro p hp ell m a b hd v S hS
  have hl := hlarge p hp
  have hr := hroom p hp ell m a b hd
  have hc := (hregular p hp ell m a b hd v S hS).2.2
  have hρ := (hdom _ _ (hscale p hp ell m a b hd v)).2.2.1.le
  have helln : 0 < ell.toNat - 1 := by omega
  have hell : 0 < ell := by omega
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast hn)
  have hy : 0 < p * ell := mul_pos hl.2.2.1 (by exact_mod_cast hell)
  have hh := bipartite_correction_of_control _ _ (p * n) (p * ell) (2 * Real.log n)
    helln (by omega) hx hy (by linarith [hl.2.1]) hρ hc.1 hc.2
  norm_num [mul_pow, ← mul_assoc] at hh
  simpa only [neg_mul] using hh

end MajorityDynamics.Probability.NeighborhoodBulk
