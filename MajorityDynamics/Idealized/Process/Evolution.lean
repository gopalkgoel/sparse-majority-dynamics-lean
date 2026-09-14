import MajorityDynamics.Idealized.Process.EvolutionEdges

/-! Step 7 of Theorem 5.2, with all constants absorbed into a single larger
logarithmic exponent, uniformly over the varying state and density. -/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Idealized.Process
open Universal Local RowLimits Binomial Binomial.Approximation
variable {n : ℕ}

theorem RowAsymptotics.mono {N : ℕ} {p : Probability} {sizes : Local.Sizes n}
    {q : Local.Tilt n} {e f : ℝ} (h : RowAsymptotics N p sizes q e) (hef : e ≤ f) :
    RowAsymptotics N p sizes q f :=
  ⟨fun s b => (h.split s b).trans hef, fun s b t => (h.child_mean s b t).trans hef⟩

theorem eventual_evolution_estimates (θ T : ℝ) (n ell L : ℕ) (K : ℝ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 ≤ K) :
    ∃ ell' : ℕ, ell ≤ ell' ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Probability, Density θ T N p → ∀ x : State n, ∀ q : Local.Tilt n,
        LevelEstimates N p ell x →
        RowAsymptotics N p x.sizes q (K * (Real.log N ^ L / scale N p)) →
        LevelEstimates N p ell' (nextState x q) := by
  obtain ⟨B, hB, hv, hv', hμ, hμ', hb⟩ := universal_evolution_bounds n
  let J := max ell L
  let S := 2 * K + 2
  let E := edgeErrorConstant B K
  let ε := min (1 / 4 : ℝ) (min (1 / (4 * B)) (1 / (2 * B * S)))
  have hB0 : 0 < B := by linarith
  have hS0 : 0 < S := by dsimp [S]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlog : ∀ᶠ N : ℕ in atTop, max 1 (max S E) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop _)
  refine ⟨J + 1, by dsimp [J]; omega, ?_⟩
  filter_upwards [hlog, eventually_size_error_small θ T ε J hθ hT hε,
    density_scale_lower_power θ T 1 0 hθ hT zero_lt_one] with N hlogN hsmall ha
  intro p hp x q hx hrow
  have hN : 1 ≤ N := hsmall.1
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp0 := p.property.1
  have hlog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlogN
  have hlogS : S ≤ Real.log (N : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlogN)
  have hlogE : E ≤ Real.log (N : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlogN)
  have ha1 : 1 ≤ scale N p := by simpa using ha p hp
  have ha0 : 0 < scale N p := by linarith
  have ha2 : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
  let ρ := Real.log (N : ℝ) ^ J / scale N p
  let δ := Real.log (N : ℝ) ^ J / ((p : ℝ) * N)
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hρsmall : ρ ≤ ε := by
    have hh := hsmall.2 p hp
    have hn : 0 ≤ 1 / (N : ℝ) := by positivity
    dsimp [ρ]
    linarith
  have hρquarter : ρ ≤ 1 / 4 := hρsmall.trans (min_le_left _ _)
  have hρB : ρ ≤ 1 / (4 * B) :=
    hρsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρS : ρ ≤ 1 / (2 * B * S) :=
    hρsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδeq : ρ / scale N p = δ := by
    dsimp [ρ, δ]
    rw [← ha2]
    ring
  have hδρ : δ ≤ ρ := by rw [← hδeq]; exact div_le_self hρ ha1
  have hpow : 1 ≤ Real.log (N : ℝ) ^ J := one_le_pow₀ hlog1
  have hrate : 1 / scale N p ≤ ρ := div_le_div_of_nonneg_right hpow ha0.le
  have hμsmall : B / scale N p ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left (hrate.trans hρB) hB0.le
    calc
      B / scale N p = B * (1 / scale N p) := by ring
      _ ≤ B * (1 / (4 * B)) := hh
      _ = 1 / 4 := by field_simp
  have hsq : (1 / scale N p) ^ 2 ≤ δ := by
    dsimp [δ]
    rw [← ha2]
    have hh := div_le_div_of_nonneg_right hpow (sq_nonneg (scale N p))
    simpa only [one_div, inv_pow] using hh
  have hinv : 1 / (N : ℝ) ≤ δ := by
    dsimp [δ]
    apply (div_le_div_iff₀ hN0 (mul_pos p.property.1 hN0)).mpr
    have hp1 := mul_le_mul_of_nonneg_right (p.property.2.le.trans hpow) hN0.le
    simpa only [one_mul] using hp1
  have hround : 1 ≤ (N : ℝ) * ρ := by
    have hh := (elementary_errors_le_rate N J p hN hlog1).1
    have hh' := (div_le_iff₀ hN0).mp hh
    simpa only [mul_comm] using hh'
  have hbudget : (2 * K + 2) * ρ ≤ 1 / (2 * B) := by
    have hh := mul_le_mul_of_nonneg_left hρS hS0.le
    calc
      _ ≤ S * (1 / (2 * B * S)) := hh
      _ = _ := by field_simp
  have hsize : ∀ s, |(x.sizes s : ℝ) - N * ν n s| ≤ N * ρ := by
    intro s
    have hh := (hx.sizes s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog1 (le_max_left ell L))
        (show 0 ≤ (N : ℝ) / scale N p by positivity))
    calc
      _ ≤ (N : ℝ) / scale N p * Real.log (N : ℝ) ^ J := hh
      _ = _ := by dsimp [ρ]; ring
  have hedge : ∀ s t, |x.edges s t - (p : ℝ) * x.sizes s * x.sizes t *
      (1 + μ n s t / scale N p)| ≤ (p : ℝ) * x.sizes s * x.sizes t * δ := by
    intro s t
    apply (hx.edges s t).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog1 (le_max_left ell L)) (by positivity)
  have hrow' : RowAsymptotics N p x.sizes q (K * ρ) := hrow.mono
    (mul_le_mul_of_nonneg_left
      (logarithmic_rate_mono N L J p hlog1 (le_max_right ell L)) hK)
  have hs := next_sizes_quantitative N p x q ρ K hρ (by linarith) hK hround hsize hrow'
  have he := next_edges_quantitative N p x q ρ δ K B hN hK hB hρ (by linarith) hδ
    (hδρ.trans hρquarter) ha1 hμsmall hδeq hsq hinv hround hbudget hv hv' hμ hμ' hb
    hsize hedge hrow'
  constructor
  · intro u
    refine (hs u).trans ?_
    have hh := mul_le_mul_of_nonneg_right hlogS
      (show 0 ≤ (N : ℝ) * Real.log (N : ℝ) ^ J / scale N p by positivity)
    calc
      _ = S * ((N : ℝ) * Real.log (N : ℝ) ^ J / scale N p) := by dsimp [S, ρ]; ring
      _ ≤ Real.log (N : ℝ) * ((N : ℝ) * Real.log (N : ℝ) ^ J / scale N p) := hh
      _ = _ := by rw [pow_succ]; dsimp [scale]; ring
  · intro u v
    refine (he u v).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hlogE hδ
    calc
      _ ≤ Real.log (N : ℝ) * δ := hh
      _ = _ := by dsimp [δ]; rw [pow_succ]; ring

end MajorityDynamics.Idealized.Process
