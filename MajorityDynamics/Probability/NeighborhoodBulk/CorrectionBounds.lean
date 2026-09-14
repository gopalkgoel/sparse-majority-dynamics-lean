import MajorityDynamics.Probability.NeighborhoodBulk.Regularity

/-! Explicit control of the exponential correction factors in the two source
theorems. All estimates here have only foundational dependencies. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Literature.DegreeEnumeration

theorem centered_square_sum_le {V : Type*} [Fintype V] (d : V → ℝ) (μ B : ℝ)
    (hB : 0 ≤ B) (h : ∀ i, |d i - μ| ≤ B) :
    ∑ i, (d i - μ) ^ 2 ≤ Fintype.card V * B ^ 2 := by
  calc
    _ ≤ ∑ _ : V, B ^ 2 := Finset.sum_le_sum (fun i _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (h i))
    _ = _ := by simp

theorem graphCorrection_bounds {n m : ℕ} (d : Fin n → ℕ) (K L : ℝ)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (hμ : 0 < graphDensity n m)
    (hμ1 : graphDensity n m < 1)
    (hγ : graphGamma m d ≤ K * graphDensity n m * (1 - graphDensity n m) * L ^ 2) :
    Real.exp (-(K ^ 2 + 1) * L ^ 4) ≤ graphCorrection m d ∧
      graphCorrection m d ≤ Real.exp ((K ^ 2 + 1) * L ^ 4) := by
  have hγ0 : 0 ≤ graphGamma m d := by unfold graphGamma; positivity
  have hden : 0 < graphDensity n m * (1 - graphDensity n m) :=
    mul_pos hμ (sub_pos.mpr hμ1)
  have hq : 0 ≤ graphGamma m d / (graphDensity n m * (1 - graphDensity n m)) := by
    positivity
  have hqle : graphGamma m d / (graphDensity n m * (1 - graphDensity n m)) ≤ K * L ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [hγ]
  have hsq := (sq_le_sq₀ hq (by positivity : 0 ≤ K * L ^ 2)).mpr hqle
  have he : graphGamma m d ^ 2 /
      (4 * graphDensity n m ^ 2 * (1 - graphDensity n m) ^ 2) =
      (graphGamma m d / (graphDensity n m * (1 - graphDensity n m))) ^ 2 / 4 := by
    field_simp
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL
  unfold graphCorrection
  rw [he]
  constructor <;> apply Real.exp_le_exp.mpr
  · nlinarith [sq_nonneg (graphGamma m d / (graphDensity n m * (1 - graphDensity n m))),
      sq_nonneg K, mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hL4)]
  · nlinarith [sq_nonneg (graphGamma m d / (graphDensity n m * (1 - graphDensity n m))),
      mul_nonneg (sq_nonneg K) (by positivity : 0 ≤ L ^ 4)]

theorem bipartiteCorrection_bounds {ell n m : ℕ} (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (ha : 0 ≤ leftVariance m a / (leftAverage ell m * (1 - bipartiteDensity ell n m)))
    (hb : 0 ≤ rightVariance m b / (rightAverage n m * (1 - bipartiteDensity ell n m)))
    (haK : leftVariance m a / (leftAverage ell m * (1 - bipartiteDensity ell n m)) ≤ K * L ^ 2)
    (hbK : rightVariance m b / (rightAverage n m * (1 - bipartiteDensity ell n m)) ≤ K * L ^ 2) :
    Real.exp (-(K + 1) ^ 2 * L ^ 4) ≤ bipartiteCorrection m a b ∧
      bipartiteCorrection m a b ≤ Real.exp ((K + 1) ^ 2 * L ^ 4) := by
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have haabs : |1 - leftVariance m a /
      (leftAverage ell m * (1 - bipartiteDensity ell n m))| ≤ (K + 1) * L ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hK (sq_nonneg L)]
  have hbabs : |1 - rightVariance m b /
      (rightAverage n m * (1 - bipartiteDensity ell n m))| ≤ (K + 1) * L ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hK (sq_nonneg L)]
  have hab := mul_le_mul haabs hbabs (abs_nonneg _) (by positivity : 0 ≤ (K + 1) * L ^ 2)
  rw [← abs_mul] at hab
  obtain ⟨hlo, hhi⟩ := abs_le.mp hab
  unfold bipartiteCorrection
  constructor <;> apply Real.exp_le_exp.mpr <;>
    nlinarith [mul_nonneg (sq_nonneg (K + 1)) (by positivity : 0 ≤ L ^ 4)]

theorem eventually_graph_correction_bounds (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.DensityWindow θ T n p →
        ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
          Real.exp (-1025 * Real.log n ^ 4) ≤ graphCorrection m.toNat (fun i => (d i).toNat) ∧
            graphCorrection m.toNat (fun i => (d i).toNat) ≤ Real.exp (1025 * Real.log n ^ 4) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    MajorityDynamics.Combinatorics.DegreeRatios.eventually_large_parameters θ T hθlo hθhi hT,
    eventually_density_log_le_rpow θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hn hlarge hsmall
  intro p hp m d hd
  have hl := hlarge p hp
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hN : 0 < (n : ℝ) - 1 := by linarith
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast hn0)
  have hc := graph_input_centered hn0 hl.2.2.1 hd
  have hL : 0 ≤ Real.log (n : ℝ) := by linarith [hl.2.1]
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hav := average_ge_half hx.le hc.1 hs
  have hav0 : 0 < graphAverage n m.toNat := (by positivity : 0 < p * n / 2).trans_le hav
  have havhi : graphAverage n m.toNat ≤ 3 * (p * n) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (p * n))
    nlinarith [(abs_le.mp hc.1).2, Real.sq_sqrt hx.le]
  have hμ : 0 < graphDensity n m.toNat := div_pos hav0 hN
  have hμhalf : graphDensity n m.toNat ≤ 1 / 2 := by
    apply (div_le_iff₀ hN).mpr
    have hh := mul_le_mul_of_nonneg_right hl.2.2.2.1 (by positivity : (0 : ℝ) ≤ n)
    linarith
  have hsum := centered_square_sum_le (fun i => ((d i).toNat : ℝ))
    (graphAverage n m.toNat) (2 * (Real.sqrt (p * n) * Real.log n)) (by positivity) hc.2
  have hsum' : (∑ i, (((d i).toNat : ℝ) - graphAverage n m.toNat) ^ 2) ≤
      (n : ℝ) * (4 * (p * n) * Real.log n ^ 2) := by
    simpa only [Fintype.card_fin, mul_pow, Real.sq_sqrt hx.le, show (2 : ℝ)^2 = 4 by norm_num,
      mul_assoc] using hsum
  have hsum'' : (∑ i, (((d i).toNat : ℝ) - graphAverage n m.toNat) ^ 2) ≤
      16 * ((n : ℝ) - 1) * graphAverage n m.toNat * Real.log n ^ 2 := by
    calc
      _ ≤ (n : ℝ) * (4 * (p * n) * Real.log n ^ 2) := hsum'
      _ ≤ (n : ℝ) * (8 * graphAverage n m.toNat * Real.log n ^ 2) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (by linarith : 4 * (p * n) ≤ 8 * graphAverage n m.toNat) (sq_nonneg _))
            (by positivity)
      _ ≤ (2 * ((n : ℝ) - 1)) * (8 * graphAverage n m.toNat * Real.log n ^ 2) := by
        gcongr
        linarith
      _ = _ := by ring
  have hγ : graphGamma m.toNat (fun i => (d i).toNat) ≤
      16 * graphDensity n m.toNat * Real.log n ^ 2 := by
    unfold graphGamma graphDensity
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    have he : 16 * (graphAverage n m.toNat / ((n : ℝ) - 1)) * Real.log n ^ 2 *
        ((n : ℝ) - 1) ^ 2 =
          16 * ((n : ℝ) - 1) * graphAverage n m.toNat * Real.log n ^ 2 := by
      field_simp
    rw [he]
    exact hsum''
  have hγ32 : graphGamma m.toNat (fun i => (d i).toNat) ≤
      32 * graphDensity n m.toNat * (1 - graphDensity n m.toNat) * Real.log n ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hμhalf
      (by positivity : 0 ≤ 32 * graphDensity n m.toNat * Real.log n ^ 2)
    nlinarith [hγ]
  simpa only [show (32 : ℝ)^2 + 1 = 1025 by norm_num] using
    graphCorrection_bounds (fun i => (d i).toNat) 32 (Real.log n) (by norm_num) hl.2.1
      hμ (by linarith) hγ32

theorem variance_ratio_bounds {V : Type*} [Fintype V] [Nonempty V]
    (d : V → ℝ) (μ x ρ L : ℝ) (hx : 0 < x) (hL : 0 ≤ L)
    (hμ : x / 2 ≤ μ) (hρ : ρ ≤ 1 / 2)
    (hd : ∀ i, |d i - μ| ≤ 2 * (Real.sqrt x * L)) :
    0 ≤ ((∑ i, (d i - μ) ^ 2) / Fintype.card V) / (μ * (1 - ρ)) ∧
      ((∑ i, (d i - μ) ^ 2) / Fintype.card V) / (μ * (1 - ρ)) ≤ 16 * L ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hμ0 : 0 < μ := (by positivity : 0 < x / 2).trans_le hμ
  have hρ1 : 0 < 1 - ρ := by linarith
  have hden : 0 < μ * (1 - ρ) := mul_pos hμ0 hρ1
  have hsum := centered_square_sum_le d μ (2 * (Real.sqrt x * L)) (by positivity) hd
  have hvar : (∑ i, (d i - μ) ^ 2) / Fintype.card V ≤ 4 * x * L ^ 2 := by
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ Fintype.card V * (2 * (Real.sqrt x * L)) ^ 2 := hsum
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hx.le]; ring
  refine ⟨by positivity, (div_le_iff₀ hden).mpr ?_⟩
  have hdenlo : 4 * x ≤ 16 * (μ * (1 - ρ)) := by
    have := mul_le_mul_of_nonneg_left hρ hμ0.le
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hdenlo (sq_nonneg L)
  nlinarith

theorem eventually_bipartite_correction_bounds (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.DensityWindow θ T n p →
        ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
          BipartiteInput T n p ell m a b →
            Real.exp (-289 * Real.log n ^ 4) ≤
                bipartiteCorrection m.toNat (fun i => (a i).toNat) (fun j => (b j).toNat) ∧
              bipartiteCorrection m.toNat (fun i => (a i).toNat) (fun j => (b j).toNat) ≤
                Real.exp (289 * Real.log n ^ 4) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    MajorityDynamics.Combinatorics.DegreeRatios.eventually_large_parameters θ T hθlo hθhi hT,
    eventually_density_log_le_rpow θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num),
    eventually_density_log_le_side_rpow θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hn hlarge hsmall hsmall'
  intro p hp ell m a b hd
  have hl := hlarge p hp
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hell0 : (0 : ℝ) < ell := (div_pos hn0r (by linarith)).trans_le hd.1
  have hell : 0 < ell := by exact_mod_cast hell0
  have helln : 0 < ell.toNat := by omega
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have : Nonempty (Fin ell.toNat) := Fin.pos_iff_nonempty.mp helln
  have hx : 0 < p * n := mul_pos hl.2.2.1 hn0r
  have hy : 0 < p * ell := mul_pos hl.2.2.1 hell0
  have hc := bipartite_input_centered hn0 hell hl.2.2.1 hd
  have hL : 0 ≤ Real.log (n : ℝ) := by linarith [hl.2.1]
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hs' : 2 * Real.log n ≤ Real.sqrt (p * ell) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall' p hp ell hd.1
  have havhi : leftAverage ell.toNat m.toNat ≤ 3 * (p * n) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (p * n))
    nlinarith [(abs_le.mp hc.1.1).2, Real.sq_sqrt hx.le]
  have hρ : bipartiteDensity ell.toNat n m.toNat ≤ 1 / 2 := by
    have he : bipartiteDensity ell.toNat n m.toNat = leftAverage ell.toNat m.toNat / n := by
      unfold bipartiteDensity leftAverage
      rw [div_div]
    rw [he]
    apply (div_le_iff₀ hn0r).mpr
    have hh := mul_le_mul_of_nonneg_right hl.2.2.2.1 hn0r.le
    linarith
  have ha := variance_ratio_bounds (fun i => ((a i).toNat : ℝ)) (leftAverage ell.toNat m.toNat)
    (p * n) (bipartiteDensity ell.toNat n m.toNat) (Real.log n) hx hL
    (average_ge_half hx.le hc.1.1 hs) hρ hc.1.2
  have hb := variance_ratio_bounds (fun j => ((b j).toNat : ℝ)) (rightAverage n m.toNat)
    (p * ell) (bipartiteDensity ell.toNat n m.toNat) (Real.log n) hy hL
    (average_ge_half hy.le hc.2.1 hs') hρ hc.2.2
  simp only [Fintype.card_fin] at ha hb
  simpa only [show ((16 : ℝ) + 1)^2 = 289 by norm_num] using
    bipartiteCorrection_bounds (fun i => (a i).toNat) (fun j => (b j).toNat)
      16 (Real.log n) (by norm_num) hl.2.1 ha.1 hb.1 ha.2 hb.2

end MajorityDynamics.Probability.NeighborhoodBulk
