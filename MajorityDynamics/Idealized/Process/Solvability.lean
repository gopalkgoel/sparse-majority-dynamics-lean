import MajorityDynamics.Idealized.Process.SolvabilityRows
import MajorityDynamics.Idealized.Process.Symmetry
import MajorityDynamics.Idealized.Process.TargetBounds
import MajorityDynamics.Idealized.RowLimits.Main

/-!
# Uniform solvability of the idealized binomial mean equations

This is Theorem 5.2, Step 2: apply the proved E.3 limits to the actual
binomial mean map, and invert its uniformly small perturbation of the
Gaussian strong bijection. The constants are chosen before the density and
the approximately universal state. The witnesses retain all E.3 estimates
for the following local-template evolution argument.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter Topology
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process
open Universal Binomial Binomial.Approximation RowLimits
variable {n : ℕ}

theorem StateSymmetric.rowLimits_admissible {N ell : ℕ} {p : Probability}
    {x : State n} (hx : StateSymmetric x) (he : LevelEstimates N p ell x)
    {T ξ : ℝ} (hT : 0 ≤ T) (hξ : 0 ≤ ξ) (s : History (n + 1)) :
    AdmissibleSizes N p ell T ξ s x.sizes where
  close := he.sizes
  history_balance r := by rw [symmetric_history_balance x hx s r, abs_zero]; positivity
  decision_balance := by
    rw [show nextImbalance x.sizes = 0 from symmetric_imbalance_eq_zero x hx (Fin.last n), abs_zero]
    positivity

theorem StateSymmetric.nextImbalance_zero {x : State n} (hx : StateSymmetric x) :
    nextImbalance x.sizes = 0 := symmetric_imbalance_eq_zero x hx (Fin.last n)

theorem enlarge_estimates {N : ℕ} {p : Probability} {sizes : Local.Sizes n}
    {s : History (n + 1)} {σ : Row (n + 1)} {u C ε C' ε' : ℝ}
    (h : Estimates N p sizes s σ u C ε) (he : C * ε ≤ C' * ε') :
    Estimates N p sizes s σ u C' ε' where
  history_probability := h.history_probability.trans he
  split_probability b := (h.split_probability b).trans he
  history_mean t := (h.history_mean t).trans he
  child_mean b t := (h.child_mean b t).trans he
  covariance t t' := (h.covariance t t').trans he

private theorem normalizedMeanMap_solves {N : ℕ} {p : Probability}
    {x : State n} (hN : 0 < N) (hs : ∀ t, 0 < x.sizes t)
    (σ : History (n + 1) → Row (n + 1))
    (he : ∀ s, normalizedMeanMap N p x.sizes s (σ s) =
      WithLp.toLp 2 (fun t => (x.edges s t / x.sizes s - (p : ℝ) * x.sizes t) / scale N p)) :
    Local.Solves x.sizes x.edges (fun s => rowTilt N p (σ s)) := by
  intro s t
  have ha : scale N p ≠ 0 := (Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hN))).ne'
  have hns : (x.sizes s : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hs s)).ne'
  have hh := congrArg (fun z : Row (n + 1) => z t) (he s)
  change (binomialMean N p x.sizes s (Local.historySupport x.sizes s) t (σ s) -
    (p : ℝ) * x.sizes t) / scale N p = _ at hh
  have hmean : binomialMean N p x.sizes s (Local.historySupport x.sizes s) t (σ s) =
      x.edges s t / x.sizes s := by
    have := (div_left_inj' ha).mp hh
    linarith
  have hm := (eq_div_iff hns).mp hmean
  rw [binomialMean_eq_conditionalMean] at hm
  simpa only [Local.rowMean, mul_comm] using hm

/-- Exact row solutions and quantitative approximation, simultaneously for all
rows and uniformly over the varying density and approximately universal data.
The returned constant controls both the tilt displacement and every clause
of E.3, with the same logarithmic rate. -/
theorem solvable_rows (θ T : ℝ) (hθ : 1 / 2 < θ) (hθ' : θ < 1)
    (hT : 1 < T) (n ell : ℕ) (hell : 1 ≤ ell) :
    ∃ L : ℕ, ell ≤ L ∧ ∃ R : ℝ, 0 < R ∧ (∀ s t, |γ n s t| ≤ R) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Probability, Density θ T N p →
      ∀ x : State n, StateSymmetric x → LevelEstimates N p ell x →
        ∃ σ : History (n + 1) → Row (n + 1),
          (∀ s t, |σ s t| ≤ R) ∧
          (∀ s t, |σ s t - γ n s t| ≤ C * (Real.log N ^ L / scale N p)) ∧
          Local.Solves x.sizes x.edges (fun s => rowTilt N p (σ s)) ∧
          ∀ s, Estimates N p x.sizes s (σ s) 0 C (Real.log N ^ L / scale N p) := by
  classical
  obtain ⟨R, hR, hγR, δ, hδ, A, hA, hsolve⟩ := stable_mean_inverse n
  obtain ⟨lower, hrow⟩ := row_limits n
  obtain ⟨ellE, hrow⟩ := hrow ell hell
  obtain ⟨_, hrow⟩ := hrow T R hT hR
  obtain ⟨C₀, hC₀, N₁, hrow⟩ := hrow θ hθ hθ'
  let L := max ell ellE
  let B := 1 + ∑ s : History (n + 1), ∑ t : History (n + 1),
    (2 * ν n t + |μ n s t|)
  have hcoef (s t : History (n + 1)) : 0 ≤ 2 * ν n t + |μ n s t| :=
    add_nonneg (mul_nonneg (by norm_num) (ν_positive n t).le) (abs_nonneg _)
  have hB : 0 < B := by
    have hb : 0 ≤ ∑ s : History (n + 1), ∑ t : History (n + 1),
        (2 * ν n t + |μ n s t|) :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => hcoef s t
    dsimp [B]
    linarith
  have hBt (s t : History (n + 1)) : 2 * ν n t + |μ n s t| ≤ B := by
    have h1 := Finset.single_le_sum
      (fun j _ => hcoef s j) (Finset.mem_univ t)
    have h2 : (∑ j, (2 * ν n j + |μ n s j|)) ≤
        ∑ i : History (n + 1), ∑ j : History (n + 1), (2 * ν n j + |μ n i j|) :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hcoef i j)
        (Finset.mem_univ s)
    dsimp [B]
    linarith
  let H := 1 + 2 * C₀ + B
  let C := 1 + A * H + 2 * C₀
  have hH : 0 < H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCB : B ≤ H := by dsimp [H]; linarith
  have hCH : 2 * C₀ ≤ H := by dsimp [H]; linarith
  have hCA : A * H ≤ C := by dsimp [C]; linarith
  have hCC : 2 * C₀ ≤ C := by dsimp [C]; nlinarith [mul_pos hA hH]
  have hsmall := eventually_size_error_small θ T (min (δ / H) T) L hθ'
    (by linarith) (lt_min (div_pos hδ hH) (by linarith))
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hsizes := eventually_level_sizes (n := n) θ T ell hθ' (by linarith)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((hsmall.and hlog).and hsizes)
  refine ⟨L, le_max_left _ _, R, hR, hγR, C, hC, max (max N₁ N₂) 1,
    le_max_right _ _, ?_⟩
  intro N hN p hp x hx he
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hfacts := hN₂ N hN₂'
  have hpos : 0 < N := hfacts.1.1.1
  have hlogN : 1 ≤ Real.log (N : ℝ) := hfacts.1.2
  have hsize := hfacts.2.2 p hp x he
  have hs : ∀ t, 0 < x.sizes t := fun t => (hsize t).1
  have hu : ∀ t, (x.sizes t : ℝ) ≤ 2 * N * ν n t := fun t => (hsize t).2.2.le
  let ρ := Real.log N ^ L / scale N p
  have hscale : 0 < scale N p := Real.sqrt_pos.mpr (mul_pos p.property.1 (Nat.cast_pos.mpr hpos))
  have hρ : 0 < ρ := div_pos (pow_pos (by linarith) _) hscale
  have hρsmall : ρ < min (δ / H) T := by
    have hh := hfacts.1.1.2 p hp
    have hinv : 0 ≤ (1 : ℝ) / N := by positivity
    dsimp [ρ]
    linarith
  have hρT : ρ ≤ T := (hρsmall.trans_le (min_le_right _ _)).le
  have hερ : H * ρ < δ := by
    have hh := (lt_div_iff₀ hH).mp (hρsmall.trans_le (min_le_left _ _))
    nlinarith
  have herr : error ellE N p ρ ≤ 2 * ρ := by
    have hh := logarithmic_rate_mono N ellE L p hlogN (le_max_right _ _)
    change Real.log N ^ ellE / scale N p + ρ ≤ 2 * ρ
    linarith
  have he0 (s : History (n + 1)) (σ : Row (n + 1)) (hσ : ∀ t, |σ t| ≤ R) :
      Estimates N p x.sizes s σ 0 C₀ (error ellE N p ρ) := by
    have hr := (hrow N hN₁ p hp.1 hp.2 ρ hρ hρT s x.sizes
      (hx.rowLimits_admissible he (by linarith) hρ.le s)).2 σ hσ
    exact (hr.2.2.2.2 (by rw [hx.nextImbalance_zero, abs_zero]; positivity)).2.2.2
  have hemean (s : History (n + 1)) (σ : Row (n + 1)) (hσ : ∀ t, |σ t| ≤ R) (t) :
      |normalizedMeanMap N p x.sizes s σ t - meanMap s (ν n) σ t| ≤ H * ρ := by
    have hh := (he0 s σ hσ).history_mean t
    rw [gaussianMean_history_eq_meanMap] at hh
    change |normalizedMeanMap N p x.sizes s σ t - meanMap s (ν n) σ t| ≤ _ at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left herr hC₀.le).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hCH hρ.le]))
  let target (s : History (n + 1)) : Row (n + 1) :=
    WithLp.toLp 2 (fun t => (x.edges s t / x.sizes s - (p : ℝ) * x.sizes t) / scale N p)
  have htarget (s : History (n + 1)) (t) : |target s t - ν n t * μ n s t| ≤ H * ρ := by
    have hh := he.normalized_target hpos (by linarith) hs hu s t
    have hm : Real.log N ^ ell / scale N p ≤ ρ :=
      logarithmic_rate_mono N ell L p hlogN (le_max_left _ _)
    have hb0 : 0 ≤ 2 * ν n t + |μ n s t| :=
      add_nonneg (mul_nonneg (by norm_num) (ν_positive n t).le) (abs_nonneg _)
    exact hh.trans ((mul_le_mul_of_nonneg_left hm hb0).trans
      (mul_le_mul_of_nonneg_right ((hBt s t).trans hCB) hρ.le))
  have hsolutions (s : History (n + 1)) := hsolve (H * ρ) (mul_pos hH hρ) hερ s
    (normalizedMeanMap N p x.sizes s) (normalizedMeanMap_continuous N p x.sizes s)
    (hemean s) (target s) (htarget s)
  choose σ hσeq hσR hσγ using hsolutions
  refine ⟨σ, hσR, ?_, normalizedMeanMap_solves hpos hs σ hσeq, ?_⟩
  · intro s t
    exact (hσγ s t).trans (by nlinarith [mul_le_mul_of_nonneg_right hCA hρ.le])
  · intro s
    apply enlarge_estimates (he0 s (σ s) (hσR s))
    calc
      C₀ * error ellE N p ρ ≤ C₀ * (2 * ρ) := mul_le_mul_of_nonneg_left herr hC₀.le
      _ ≤ C * ρ := by nlinarith [mul_le_mul_of_nonneg_right hCC hρ.le]

end MajorityDynamics.Idealized.Process
