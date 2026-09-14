import MajorityDynamics.Idealized.Process.SupportUniform

/-! Positive edge counts for all approximately universal idealized states. -/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Idealized.Process
open Universal Binomial Binomial.Approximation
variable {n : ℕ}

/-- A first-order center and a second-order error remain positive once their
combined relative error is less than one. -/
theorem edge_pos_of_relative_error {B a m L edge : ℝ}
    (hB : 0 < B) (ha : 1 ≤ a) (hL : 1 ≤ L)
    (hsmall : (|m| + 1) * (L / a) < 1)
    (hedge : |edge - B * (1 + m / a)| ≤ B * (L / a ^ 2)) :
    0 < edge := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hm : |m / a| ≤ |m| * (L / a) := by
    rw [abs_div, abs_of_pos ha0]
    calc
      _ ≤ (|m| * L) / a :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg m) hL) ha0.le
      _ = _ := by ring
  have he : L / a ^ 2 ≤ L / a :=
    div_le_div_of_nonneg_left hL0 ha0
      (by simpa [pow_two] using mul_le_mul_of_nonneg_left ha ha0.le)
  have hf : 0 < 1 + m / a - L / a ^ 2 := by
    have hm' := (abs_le.mp hm).1
    nlinarith
  have hpositive := mul_pos hB hf
  have hlower := (abs_le.mp hedge).1
  nlinarith

/-- One common threshold makes every edge positive for every density and every
state satisfying the displayed Theorem 5.2 asymptotics. -/
theorem eventually_level_edges_positive (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, Density θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ s t, 0 < x.edges s t := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ∀ st : History (n + 1) × History (n + 1), 0 < N ∧
      ∀ p : Probability, Density θ T N p →
        Real.log N ^ ell / scale N p + 1 / N < 1 / (2 * (|μ n st.1 st.2| + 1)) :=
    Filter.eventually_all.mpr fun st => RowLimits.eventually_size_error_small θ T
      (1 / (2 * (|μ n st.1 st.2| + 1))) ell hθ hT (by positivity)
  filter_upwards [eventually_level_sizes (n := n) θ T ell hθ hT, hlog, hsmall,
    RowLimits.density_scale_lower_power θ T 1 0 hθ hT zero_lt_one]
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

/-- For large enough coordinate boxes, solving the mean equations supplies
every remaining exact clause of solvability. -/
theorem solvable_of_solves (x : State n) (hsize : ∀ t, 2 * n + 5 ≤ x.sizes t)
    (hedges : ∀ s t, 0 < x.edges s t) (q : Local.Tilt n)
    (hsolve : Local.Solves x.sizes x.edges q) : Solvable x q where
  sizes_pos t := by have := hsize t; omega
  edges_pos := hedges
  conditioning_pos s := history_eventMass_pos x.sizes hsize s (q s)
  solves := hsolve
  unique q' hq' := solving_tilt_unique x.sizes hsize x.edges hq' hsolve

/-- The analytic existence step only has to produce a tilt solving the mean
equations: positivity and global uniqueness are already uniform theorems. -/
theorem eventually_solvable_of_solves (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, Density θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ q : Local.Tilt n,
        Local.Solves x.sizes x.edges q → Solvable x q := by
  filter_upwards [eventually_support_sizes (n := n) θ T ell hθ hT,
    eventually_level_edges_positive (n := n) θ T ell hθ hT] with N hs he
  intro p hp x hx q hq
  exact solvable_of_solves x (hs p hp x hx) (he p hp x hx) q hq

end MajorityDynamics.Idealized.Process
