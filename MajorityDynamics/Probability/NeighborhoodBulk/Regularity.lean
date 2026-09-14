import MajorityDynamics.Probability.NeighborhoodBulk.Basic
import MajorityDynamics.Combinatorics.DegreeRatios.Uniform
import MajorityDynamics.Literature.DegreeEnumeration.Consequences

/-! Conversion of the literal integer hypotheses and centering at the actual
average. The numerical threshold is uniform in the density and degree data. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem standardizedDegree_bound_iff (p size : ℝ) (d : ℤ) (B : ℝ)
    (h : 0 < p * size) :
    |standardizedDegree p size d| ≤ B ↔
      |(d : ℝ) - p * size| ≤ Real.sqrt (p * size) * B := by
  rw [standardizedDegree, abs_div, abs_of_pos (Real.sqrt_pos.mpr h),
    div_le_iff₀ (Real.sqrt_pos.mpr h)]
  rw [mul_comm B]

theorem centered_deviation_bound {V : Type*} [Fintype V] [Nonempty V]
    (d : V → ℝ) (c μ B : ℝ) (hs : ∑ i, d i = Fintype.card V * μ)
    (hd : ∀ i, |d i - c| ≤ B) :
    |μ - c| ≤ B ∧ ∀ i, |d i - μ| ≤ 2 * B := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsum : |(Fintype.card V : ℝ) * (μ - c)| ≤ Fintype.card V * B := by
    calc
      _ = |∑ i, (d i - c)| := by
        congr 1
        rw [Finset.sum_sub_distrib, hs]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ ∑ i, |d i - c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : V, B := Finset.sum_le_sum (fun i _ => hd i)
      _ = _ := by simp
  rw [abs_mul, abs_of_pos hn] at hsum
  have hm := (mul_le_mul_iff_right₀ hn).mp hsum
  refine ⟨hm, fun i => ?_⟩
  calc
    |d i - μ| = |(d i - c) - (μ - c)| := by congr 1; ring
    _ ≤ |d i - c| + |μ - c| := abs_sub _ _
    _ ≤ 2 * B := by linarith [hd i]

theorem graph_input_nat_sum {T p : ℝ} {n : ℕ} {m : ℤ} {d : Fin n → ℤ}
    (h : GraphInput T n p m d) :
    0 ≤ m ∧ (∑ i, (d i).toNat) = 2 * m.toNat := by
  have hm : 0 ≤ m := by
    have : 0 ≤ ∑ i, d i := Finset.sum_nonneg (fun i _ => (h.1 i).1)
    rw [h.2.1] at this
    omega
  refine ⟨hm, ?_⟩
  apply Int.ofNat_inj.mp
  push_cast
  simpa only [Int.toNat_of_nonneg hm, Int.toNat_of_nonneg (h.1 _).1] using h.2.1

theorem graph_input_centered {T p : ℝ} {n : ℕ} {m : ℤ} {d : Fin n → ℤ}
    (hn : 0 < n) (hp : 0 < p) (h : GraphInput T n p m d) :
    |graphAverage n m.toNat - p * n| ≤ Real.sqrt (p * n) * Real.log n ∧
      ∀ i, |((d i).toNat : ℝ) - graphAverage n m.toNat| ≤
        2 * (Real.sqrt (p * n) * Real.log n) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  apply centered_deviation_bound (fun i => ((d i).toNat : ℝ))
  · simp only [Fintype.card_fin, graphAverage]
    rw [mul_div_cancel₀ _ hn0]
    exact_mod_cast (graph_input_nat_sum h).2
  · intro i
    have hi := (standardizedDegree_bound_iff p n (d i) (Real.log n) (by positivity)).mp
      (h.2.2.2 i)
    have he : ((d i).toNat : ℝ) = (d i : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (h.1 i).1
    simpa only [he] using hi

theorem bipartite_input_nat_sums {T p : ℝ} {n : ℕ} {ell m : ℤ}
    {a : Fin ell.toNat → ℤ} {b : Fin n → ℤ}
    (h : BipartiteInput T n p ell m a b) :
    0 ≤ m ∧ (∑ i, (a i).toNat) = m.toNat ∧ (∑ j, (b j).toNat) = m.toNat := by
  have hm : 0 ≤ m := by
    rw [← h.2.2.2.2.1]
    exact Finset.sum_nonneg (fun i _ => (h.2.2.1 i).1)
  refine ⟨hm, ?_, ?_⟩
  · apply Int.ofNat_inj.mp
    push_cast
    simpa only [Int.toNat_of_nonneg hm, Int.toNat_of_nonneg (h.2.2.1 _).1]
      using h.2.2.2.2.1
  · apply Int.ofNat_inj.mp
    push_cast
    simpa only [Int.toNat_of_nonneg hm, Int.toNat_of_nonneg (h.2.2.2.1 _).1]
      using h.2.2.2.2.2.1

theorem bipartite_input_centered {T p : ℝ} {n : ℕ} {ell m : ℤ}
    {a : Fin ell.toNat → ℤ} {b : Fin n → ℤ}
    (hn : 0 < n) (hell : 0 < ell) (hp : 0 < p)
    (h : BipartiteInput T n p ell m a b) :
    (|leftAverage ell.toNat m.toNat - p * n| ≤ Real.sqrt (p * n) * Real.log n ∧
      ∀ i, |((a i).toNat : ℝ) - leftAverage ell.toNat m.toNat| ≤
        2 * (Real.sqrt (p * n) * Real.log n)) ∧
    (|rightAverage n m.toNat - p * ell| ≤ Real.sqrt (p * ell) * Real.log n ∧
      ∀ j, |((b j).toNat : ℝ) - rightAverage n m.toNat| ≤
        2 * (Real.sqrt (p * ell) * Real.log n)) := by
  have helln : 0 < ell.toNat := by omega
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have : Nonempty (Fin ell.toNat) := Fin.pos_iff_nonempty.mp helln
  constructor
  · apply centered_deviation_bound (fun i => ((a i).toNat : ℝ))
    · simp only [Fintype.card_fin, leftAverage]
      rw [mul_div_cancel₀ _ (by positivity : (ell.toNat : ℝ) ≠ 0)]
      exact_mod_cast (bipartite_input_nat_sums h).2.1
    · intro i
      have hi := (standardizedDegree_bound_iff p n (a i) (Real.log n)
        (by positivity)).mp (h.2.2.2.2.2.2.2.1 i)
      have he : ((a i).toNat : ℝ) = (a i : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (h.2.2.1 i).1
      simpa only [he] using hi
  · apply centered_deviation_bound (fun j => ((b j).toNat : ℝ))
    · simp only [Fintype.card_fin, rightAverage]
      rw [mul_div_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)]
      exact_mod_cast (bipartite_input_nat_sums h).2.2
    · intro j
      have hi := (standardizedDegree_bound_iff p ell (b j) (Real.log n)
        (by positivity)).mp (h.2.2.2.2.2.2.2.2 j)
      have he : ((b j).toNat : ℝ) = (b j : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (h.2.2.2.1 j).1
      simpa only [he] using hi

theorem eventually_graph_probability_range (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p → 0 < p ∧ p < 1 := by
  filter_upwards [eventually_large_parameters θ T hθlo hθhi hT] with n hn
  intro p hp
  have h := hn p hp
  exact ⟨h.2.2.1, lt_of_le_of_lt h.2.2.2.1 (by norm_num)⟩

/-- Every fixed positive power of the expected degree dominates the logarithm,
uniformly throughout the density window. -/
theorem eventually_density_log_le_rpow (θ T K δ : ℝ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
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

theorem sqrt_log_le_half_rpow {x L α : ℝ} (hx : 0 < x) (hL : 0 ≤ L)
    (hα1 : α ≤ 1) (h : 4 * L ≤ x ^ (α - 1 / 2)) :
    2 * (Real.sqrt x * L) ≤ (x / 2) ^ α := by
  have ht : (2 : ℝ) ^ α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
  have he : Real.sqrt x * x ^ (α - 1 / 2) = x ^ α := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg x)
  rw [he] at hh
  rw [Real.div_rpow hx.le (by norm_num)]
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ α)).mpr
  have hmul := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * (Real.sqrt x * L))
  nlinarith

theorem average_ge_half {x μ L : ℝ} (hx : 0 ≤ x)
    (h : |μ - x| ≤ Real.sqrt x * L) (hs : 2 * L ≤ Real.sqrt x) : x / 2 ≤ μ := by
  have hb := (abs_le.mp h).1
  have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg x)
  nlinarith [Real.sq_sqrt hx]

/-- The source exponent is fixed independently of the input degrees. -/
theorem eventually_graph_source_data (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        GraphSourceData (7 / 12) n m.toNat (fun i => (d i).toNat) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_graph_probability_range θ T hθlo hθhi hT,
    eventually_density_log_le_rpow θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num),
    eventually_density_log_le_rpow θ T 4 (7 / 12 - 1 / 2) hθhi (by linarith)
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

theorem eventually_density_log_le_side_rpow (θ T K δ : ℝ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ ell : ℝ, (n : ℝ) / T ≤ ell → K * Real.log n ≤ (p * ell) ^ δ := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_density_log_le_rpow θ T (K * T ^ δ) δ hθ hT (by positivity) hδ]
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

theorem eventually_bipartite_source_data (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          BipartiteSourceData (7 / 12) ell.toNat n m.toNat
            (fun i => (a i).toNat) (fun j => (b j).toNat) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_graph_probability_range θ T hθlo hθhi hT,
    eventually_density_log_le_rpow θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num),
    eventually_density_log_le_rpow θ T 4 (7 / 12 - 1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num),
    eventually_density_log_le_side_rpow θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num),
    eventually_density_log_le_side_rpow θ T 4 (7 / 12 - 1 / 2) hθhi (by linarith)
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
