import MajorityDynamics.Idealized.Process.Positivity
import MajorityDynamics.Idealized.Process.TiltUniform
import MajorityDynamics.Idealized.RowLimits.SparseGeometry
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.Process
open Universal Local Binomial Binomial.Approximation RowLimits
variable {n : ℕ}
theorem eventually_level_sizes_sparse (θ T : ℝ) (ell : ℕ) (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Probability, SparseRange θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ t,
        0 < x.sizes t ∧ (N : ℝ) * ν n t / 2 < x.sizes t ∧
        (x.sizes t : ℝ) < 2 * N * ν n t := by
  have he : ∀ᶠ N : ℕ in atTop, ∀ t : History (n + 1), 0 < N ∧
      ∀ p : Probability, SparseRange θ T N p →
        Real.log N ^ ell / scale N p + 1 / N < ν n t / 2 :=
    Filter.eventually_all.mpr fun t => RowLimits.eventually_size_error_small_sparse θ T
      (ν n t / 2) ell hθ hT (half_pos (ν_positive n t))
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N he hN
  refine ⟨hN, ?_⟩
  intro p hp x hx t
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh := hx.relative_sizes hN t
  have hb := (he t).2 p hp
  have hi : (0 : ℝ) ≤ 1 / N := by positivity
  have hv := ν_positive n t
  have hlo : ν n t / 2 < (x.sizes t : ℝ) / N := by
    have hh' := (abs_le.mp hh).1
    linarith
  have hhi : (x.sizes t : ℝ) / N < 2 * ν n t := by
    have hh' := (abs_le.mp hh).2
    linarith
  have hl := (lt_div_iff₀ hn).mp hlo
  have hu := (div_lt_iff₀ hn).mp hhi
  have hz : (0 : ℝ) < x.sizes t := by nlinarith
  exact ⟨by exact_mod_cast hz, by nlinarith, by nlinarith⟩

theorem eventually_level_sizes_ge_sparse (θ T : ℝ) (ell K : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ t, K ≤ x.sizes t := by
  have hlarge : ∀ᶠ N : ℕ in atTop, ∀ t : History (n + 1),
      2 * (K : ℝ) / ν n t ≤ (N : ℝ) :=
    Filter.eventually_all.mpr fun t =>
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_ge_atTop (2 * (K : ℝ) / ν n t))
  filter_upwards [eventually_level_sizes_sparse (n := n) θ T ell hθ hT, hlarge]
    with N hsize hlarge
  intro p hp x hx t
  have hlo := (hsize.2 p hp x hx t).2.1
  have hv := ν_positive n t
  have hn := (div_le_iff₀ hv).mp (hlarge t)
  have hK : (K : ℝ) ≤ x.sizes t := by linarith
  exact_mod_cast hK

theorem eventually_support_sizes_sparse (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ t, 2 * n + 5 ≤ x.sizes t :=
  eventually_level_sizes_ge_sparse θ T ell (2 * n + 5) hθ hT

theorem eventually_fullAffineSupport_sparse (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      ∀ x : State n, LevelEstimates N p ell x →
        (∀ s, Analysis.FiniteTilt.FullAffineSupport
          (Local.historySupport x.sizes s) Binomial.vector) ∧
        ∀ s b, Analysis.FiniteTilt.FullAffineSupport
          (Local.childSupport x.sizes s b) Binomial.vector := by
  filter_upwards [eventually_support_sizes_sparse (n := n) θ T ell hθ hT] with N hN
  intro p hp x hx
  have hsize := hN p hp x hx
  exact ⟨historySupport_fullAffineSupport x.sizes hsize,
    childSupport_fullAffineSupport x.sizes hsize⟩

theorem eventually_level_edges_positive_sparse (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ s t, 0 < x.edges s t := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ∀ st : History (n + 1) × History (n + 1), 0 < N ∧
      ∀ p : Probability, SparseRange θ T N p →
        Real.log N ^ ell / scale N p + 1 / N < 1 / (2 * (|μ n st.1 st.2| + 1)) :=
    Filter.eventually_all.mpr fun st => RowLimits.eventually_size_error_small_sparse θ T
      (1 / (2 * (|μ n st.1 st.2| + 1))) ell hθ hT (by positivity)
  filter_upwards [eventually_level_sizes_sparse (n := n) θ T ell hθ hT, hlog, hsmall,
    RowLimits.density_scale_lower_power_sparse θ T 1 0 hθ hT zero_lt_one]
    with N hsize hlog hsmall hscale
  intro p hp x hx s t
  have hs := hsize.2 p hp x hx
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hsize.1
  have ha : 1 ≤ scale N p := by simpa using hscale p hp
  have hL : 1 ≤ Real.log (N : ℝ) ^ ell := one_le_pow₀ hlog
  have hB : 0 < (p : ℝ) * x.sizes s * x.sizes t :=
    mul_pos (mul_pos p.property.1 (by exact_mod_cast (hs s).1))
      (by exact_mod_cast (hs t).1)
  have hr : Real.log N ^ ell / scale N p < 1 / (2 * (|μ n s t| + 1)) := by
    have hh := (hsmall (s, t)).2 p hp
    have hi : (0 : ℝ) ≤ 1 / N := by positivity
    linarith
  have hcombined : (|μ n s t| + 1) * (Real.log N ^ ell / scale N p) < 1 := by
    have hh := (lt_div_iff₀ (show 0 < 2 * (|μ n s t| + 1) by positivity)).mp hr
    nlinarith
  apply edge_pos_of_relative_error hB ha hL hcombined
  simpa only [scale, Real.sq_sqrt (mul_nonneg p.property.1.le hn.le)] using hx.edges s t

theorem eventually_solvable_of_solves_sparse (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ q : Local.Tilt n,
        Local.Solves x.sizes x.edges q → Solvable x q := by
  filter_upwards [eventually_support_sizes_sparse (n := n) θ T ell hθ hT,
    eventually_level_edges_positive_sparse (n := n) θ T ell hθ hT] with N hs he
  intro p hp x hx q hq
  exact solvable_of_solves x (hs p hp x hx) (he p hp x hx) q hq

theorem eventually_tilt_estimates_sparse (θ T : ℝ) (n L : ℕ) (R C : ℝ)
    (_hθ : 0 < θ) (hθ' : θ < 1) (hT : 0 < T) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, SparseRange θ T N p →
      ∀ σ : History (n + 1) → Row (n + 1),
      (∀ s t, |σ s t| ≤ R) → (∀ s t, |γ n s t| ≤ R) →
      (∀ s t, |σ s t - γ n s t| ≤ C * (Real.log N ^ L / scale N p)) →
      TiltEstimates N p (L + 1) (fun s => RowLimits.rowTilt N p (σ s)) := by
  classical
  let B := 1 + ∑ t : History (n + 1), 2 * Real.exp (R / ν n t) / ν n t * C
  have hB : 1 ≤ B := by
    dsimp [B]
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg fun t _ => mul_nonneg
      (div_nonneg (by positivity) (ν_positive n t).le) hC
  have hBt (t : History (n + 1)) : 2 * Real.exp (R / ν n t) / ν n t * C ≤ B := by
    have hh : 2 * Real.exp (R / ν n t) / ν n t * C ≤
        ∑ j : History (n + 1), 2 * Real.exp (R / ν n j) / ν n j * C := Finset.single_le_sum
      (fun j _ => show 0 ≤ 2 * Real.exp (R / ν n j) / ν n j * C from
        mul_nonneg (div_nonneg (by positivity) (ν_positive n j).le) hC)
      (Finset.mem_univ t)
    dsimp [B]
    linarith
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop B)
  have ht : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-(1/2:ℝ))) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).const_mul T
  have hupper := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hlog, hupper,
    RowLimits.density_scale_lower_power_sparse θ T 1 0 hθ' hT zero_lt_one]
      with N hlog hupper hscale
  intro p hp σ hσ hγ hclose s t
  have hs : 1 ≤ Real.sqrt ((p : ℝ) * N) := by simpa [scale] using hscale p hp
  have hlog0 : 0 ≤ Real.log (N : ℝ) := le_trans zero_le_one (hB.trans hlog)
  have hh := logitTilt_error N p (ν n t) R (σ s t) (γ n s t) C (Real.log N ^ L)
    (ν_positive n t) hR hC (pow_nonneg hlog0 _) (hp.2.trans hupper).le
    hs (hσ s t) (hγ s t) (by simpa [scale, mul_div_assoc] using hclose s t)
  calc
    _ ≤ (2 * Real.exp (R / ν n t) / ν n t * C) * Real.log N ^ L / N := hh
    _ ≤ Real.log N * Real.log N ^ L / N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((hBt t).trans hlog) (pow_nonneg hlog0 _))
        (Nat.cast_nonneg _)
    _ = Real.log N ^ (L + 1) / N := by rw [pow_succ]; ring

end MajorityDynamics.Idealized.Process
