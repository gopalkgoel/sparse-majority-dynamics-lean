import MajorityDynamics.Probability.NeighborhoodBulk.Regularity
import MajorityDynamics.Combinatorics.DegreeRatios.SparseUniform

/-! Uniform sparse-range preparation, preserving the original finite bounds. -/
noncomputable section
open Filter
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_graph_probability_range_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p → 0 < p ∧ p < 1 := by
  filter_upwards [eventually_sparse_large_parameters θ T hθlo hθhi hT] with n hn
  intro p hp
  have h := hn p hp
  exact ⟨h.2.2.1, lt_of_le_of_lt h.2.2.2.1 (by norm_num)⟩

/-- Every fixed positive power of the expected degree dominates the logarithm,
uniformly throughout the density window. -/

theorem eventually_density_log_le_rpow_sparse (θ T K δ : ℝ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      K * Real.log n ≤ (p * n) ^ δ := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := ((isLittleO_log_rpow_rpow_atTop 1
    (mul_pos (sub_pos.mpr hθ) hδ)).comp_tendsto hn).bound
      (show 0 < (T⁻¹ : ℝ) ^ δ / K by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with n hn1 hbound
  intro p hp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hbound' : Real.log n ≤ (T⁻¹ : ℝ) ^ δ / K * (n : ℝ) ^ ((1 - θ) * δ) := by
    simpa only [Function.comp_apply, Real.rpow_one, Real.norm_of_nonneg hln,
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hbound
  have hlow : T⁻¹ * (n : ℝ) ^ (1 - θ) ≤ p * n := by
    calc
      _ = (T⁻¹ * (n : ℝ) ^ (-θ)) * n := by
        rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hn0.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp.1.le hn0.le
  calc
    K * Real.log n ≤ (T⁻¹ : ℝ) ^ δ * (n : ℝ) ^ ((1 - θ) * δ) := by
      have := mul_le_mul_of_nonneg_left hbound' hK.le
      field_simp at this ⊢
      nlinarith
    _ = (T⁻¹ * (n : ℝ) ^ (1 - θ)) ^ δ := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hlow hδ.le

theorem eventually_graph_source_data_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        GraphSourceData (7 / 12) n m.toNat (fun i => (d i).toNat) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_graph_probability_range_sparse θ T hθlo hθhi hT,
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num),
    eventually_density_log_le_rpow_sparse θ T 4 (7 / 12 - 1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hn hp0 hsmall hspread
  intro p hp m d hd
  have hn0 : 0 < n := by omega
  have hx : 0 < p * n := mul_pos (hp0 p hp).1 (by exact_mod_cast hn0)
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hc := graph_input_centered hn0 (hp0 p hp).1 hd
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hav : p * n / 2 ≤ graphAverage n m.toNat := by
    exact average_ge_half hx.le hc.1 hs
  refine ⟨?_, (graph_input_nat_sum hd).2, fun i => ?_⟩
  · intro i
    change (d i).toNat ≤ n - 1
    have := (hd.1 i).2
    omega
  · calc
      _ ≤ 2 * (Real.sqrt (p * n) * Real.log n) := hc.2 i
      _ ≤ (p * n / 2) ^ (7 / 12 : ℝ) :=
        sqrt_log_le_half_rpow hx hL (by norm_num) (hspread p hp)
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hav (by norm_num)

theorem eventually_density_log_le_side_rpow_sparse (θ T K δ : ℝ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ ell : ℝ, (n : ℝ) / T ≤ ell → K * Real.log n ≤ (p * ell) ^ δ := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_density_log_le_rpow_sparse θ T (K * T ^ δ) δ hθ hT (by positivity) hδ]
      with n hn hbound
  intro p hp ell hell
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := (by positivity : 0 < T⁻¹ * (n : ℝ) ^ (-θ)).trans hp.1
  have hlow : p * n / T ≤ p * ell := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hell hp0.le
  calc
    K * Real.log n ≤ (p * n / T) ^ δ := by
      rw [Real.div_rpow (by positivity) hT.le]
      apply (le_div_iff₀ (by positivity : 0 < T ^ δ)).mpr
      nlinarith [hbound p hp]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hlow hδ.le

theorem eventually_bipartite_source_data_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          BipartiteSourceData (7 / 12) ell.toNat n m.toNat
            (fun i => (a i).toNat) (fun j => (b j).toNat) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_graph_probability_range_sparse θ T hθlo hθhi hT,
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num),
    eventually_density_log_le_rpow_sparse θ T 4 (7 / 12 - 1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num),
    eventually_density_log_le_side_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num),
    eventually_density_log_le_side_rpow_sparse θ T 4 (7 / 12 - 1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hn hp0 hsmall hspread hsmall' hspread'
  intro p hp ell m a b hd
  have hn0 : 0 < n := by omega
  have hell0 : (0 : ℝ) < ell := (div_pos (by exact_mod_cast hn0) (by linarith)).trans_le hd.1
  have hell : 0 < ell := by exact_mod_cast hell0
  have hx : 0 < p * n := mul_pos (hp0 p hp).1 (by exact_mod_cast hn0)
  have hy : 0 < p * ell := mul_pos (hp0 p hp).1 hell0
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hc := bipartite_input_centered hn0 hell (hp0 p hp).1 hd
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hs' : 2 * Real.log n ≤ Real.sqrt (p * ell) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall' p hp ell hd.1
  refine ⟨?_, ?_, (bipartite_input_nat_sums hd).2.1,
    (bipartite_input_nat_sums hd).2.2, ?_, ?_⟩
  · intro i
    change (a i).toNat ≤ n
    have := (hd.2.2.1 i).2
    omega
  · intro j
    change (b j).toNat ≤ ell.toNat
    exact Int.toNat_le_toNat (hd.2.2.2.1 j).2
  · intro i
    calc
      _ ≤ 2 * (Real.sqrt (p * n) * Real.log n) := hc.1.2 i
      _ ≤ (p * n / 2) ^ (7 / 12 : ℝ) :=
        sqrt_log_le_half_rpow hx hL (by norm_num) (hspread p hp)
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (average_ge_half hx.le hc.1.1 hs) (by norm_num)
  · intro j
    calc
      _ ≤ 2 * (Real.sqrt (p * ell) * Real.log n) := hc.2.2 j
      _ ≤ (p * ell / 2) ^ (7 / 12 : ℝ) :=
        sqrt_log_le_half_rpow hy hL (by norm_num) (hspread' p hp ell hd.1)
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (average_ge_half hy.le hc.2.1 hs') (by norm_num)

end MajorityDynamics.Probability.NeighborhoodBulk

