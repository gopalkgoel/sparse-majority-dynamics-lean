import MajorityDynamics.Idealized.Process.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exact finite recursion, determination, and the day-one estimates -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace MajorityDynamics.Idealized.Process

open Universal Local

theorem recursion_determined {N D : ℕ} {p : Binomial.Probability} {a b : Data}
    (ha : Recursion N p D a) (hb : Recursion N p D b) : AgreeThrough D a b := by
  have states : ∀ n, n < D → a.state n = b.state n := by
    intro n
    induction n with
    | zero => intro _; exact ha.initial.trans hb.initial.symm
    | succ n ih =>
      intro hn
      have hs := ih (by omega)
      have hq : b.tilt n = a.tilt n := by
        apply (ha.solvable n hn).unique
        rw [hs]
        exact (hb.solvable n hn).solves
      rw [ha.evolution n hn, hb.evolution n hn, hs, hq]
  refine ⟨states, ?_⟩
  intro n hn
  symm
  apply (ha.solvable n hn).unique
  rw [states n (by omega)]
  exact (hb.solvable n hn).solves

theorem LevelEstimates.mono {N ell ell' n : ℕ} {p : Binomial.Probability}
    {x : State n} (h : LevelEstimates N p ell x)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hell : ell ≤ ell') :
    LevelEstimates N p ell' x where
  sizes s := (h.sizes s).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hlog hell) (by positivity))
  edges s t := (h.edges s t).trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog hell)
      (mul_nonneg p.property.1.le (Nat.cast_nonneg N)))
    (mul_nonneg (mul_nonneg p.property.1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))

theorem TiltEstimates.mono {N ell ell' n : ℕ} {p : Binomial.Probability}
    {q : Local.Tilt n} (h : TiltEstimates N p ell q)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hell : ell ≤ ell') :
    TiltEstimates N p ell' q := fun s t =>
  (h s t).trans (div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog hell) (by positivity))

theorem Solvable.templateDefined {n : ℕ} {x : State n} {q : Local.Tilt n}
    (h : Solvable x q) : Local.TemplateDefined x.sizes x.edges := by
  refine ⟨h.sizes_pos, ?_, fun s t => (h.edges_pos s t).ne'⟩
  intro s
  by_contra hS
  have he : Local.historySupport x.sizes s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
  have hp := h.conditioning_pos s
  simp [he, Binomial.eventMass] at hp

theorem next_templateSizes_nonneg {n : ℕ} (x : State n) (q : Local.Tilt n)
    (u : History (n + 2)) : 0 ≤ Local.templateSizes x.sizes q u := by
  unfold Local.templateSizes Local.splitProbability
  apply mul_nonneg (Nat.cast_nonneg _)
  apply div_nonneg <;> apply Finset.sum_nonneg <;>
    intro a _ <;> exact (Binomial.mass_pos _ _ _).le

/-- The natural-number recursion is exactly the paper's integer floor. -/
theorem nextState_sizes_int {n : ℕ} (x : State n) (q : Local.Tilt n)
    (u : History (n + 2)) :
    ((nextState x q).sizes u : ℤ) = ⌊Local.templateSizes x.sizes q u⌋ :=
  Int.natCast_floor_eq_floor (next_templateSizes_nonneg x q u)

theorem initialState_sizes_int (N : ℕ) (p : Binomial.Probability) (s : History 1) :
    ((initialState N p).sizes s : ℤ) = ⌊(N : ℝ) / 2⌋ := by
  simp only [initialState]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Int.floor_div_natCast, Int.floor_natCast]
  exact_mod_cast (rfl : (N / 2 : ℕ) = N / 2)

private theorem half_bounds (N : ℕ) :
    (N / 2 : ℕ) * (2 : ℝ) ≤ N ∧ (N : ℝ) < 2 * ((N / 2 : ℕ) + (1 : ℝ)) := by
  constructor
  · exact_mod_cast Nat.div_mul_le_self N 2
  · exact_mod_cast Nat.lt_mul_div_succ N (by decide : 0 < 2)

theorem initialState_estimates (N : ℕ) (p : Binomial.Probability)
    (hN : 6 ≤ N) (hlog : 3 ≤ Real.log (N : ℝ)) :
    LevelEstimates N p 1 (initialState N p) := by
  have hp0 := p.property.1
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn6 : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) ≤ (N / 2 : ℕ) := Nat.cast_nonneg _
  obtain ⟨hmlo, hmhi⟩ := half_bounds N
  have hm : (N : ℝ) / 3 ≤ (N / 2 : ℕ) := by nlinarith
  have hsc : Real.sqrt ((p : ℝ) * N) ≤ N := by
    apply (Real.sqrt_le_left hn.le).mpr
    have hp := mul_le_mul_of_nonneg_right p.property.2.le hn.le
    nlinarith
  have hspos : 0 < Real.sqrt ((p : ℝ) * N) :=
    Real.sqrt_pos.mpr (mul_pos p.property.1 hn)
  have hs : 1 ≤ (N : ℝ) / Real.sqrt ((p : ℝ) * N) :=
    (le_div_iff₀ hspos).mpr (by simpa using hsc)
  constructor
  · intro s
    simp only [initialState, ν_zero, pow_one]
    have habs : |((N / 2 : ℕ) : ℝ) - (N : ℝ) * (1 / 2)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    apply habs.trans
    have hlog1 : 1 ≤ Real.log (N : ℝ) := by linarith
    nlinarith
  · intro s t
    simp only [initialState, μ_zero, zero_div, add_zero, mul_one, pow_one]
    by_cases hst : s = t
    · simp only [if_pos hst]
      have heq : (p : ℝ) * (N / 2 : ℕ) * ((N / 2 : ℕ) - (1 : ℝ)) -
          (p : ℝ) * (N / 2 : ℕ) * (N / 2 : ℕ) = -(p : ℝ) * (N / 2 : ℕ) := by ring
      rw [heq, abs_mul, abs_neg, abs_of_pos p.property.1, abs_of_nonneg hm0]
      have hmlog : (N : ℝ) ≤ (N / 2 : ℕ) * Real.log (N : ℝ) := by
        have hh := mul_le_mul_of_nonneg_left hlog hm0
        nlinarith
      have hp : (p : ℝ) * N ≤ (N / 2 : ℕ) * Real.log (N : ℝ) :=
        (by nlinarith [mul_le_mul_of_nonneg_right p.property.2.le hn.le])
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (mul_pos p.property.1 hn)).mpr
      have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg p.property.1.le hm0)
      nlinarith
    · simp only [if_neg hst, sub_zero, sub_self, abs_zero]
      positivity

theorem eventually_initialState_estimates :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ p : Binomial.Probability, LevelEstimates N p 1 (initialState N p) := by
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (3 : ℝ))
  filter_upwards [eventually_ge_atTop (6 : ℕ), hlog] with N hN hl
  change 3 ≤ Real.log (N : ℝ) at hl
  exact ⟨by omega, by linarith, fun p => initialState_estimates N p hN hl⟩

end MajorityDynamics.Idealized.Process
