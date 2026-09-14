import MajorityDynamics.Analysis.LogTaylor
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Accumulating local logarithmic errors on a lattice window -/

noncomputable section

namespace MajorityDynamics.Analysis

theorem abs_sub_le_steps (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (e : ℝ)
    (hstep : ∀ j : ℕ, a ≤ j → j < b → |f (j + 1) - f j| ≤ e) :
    |f b - f a| ≤ ((b : ℝ) - a) * e := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hprev := ih (fun j haj hjb => hstep j haj (hjb.trans (Nat.lt_succ_self b)))
    calc
      _ ≤ |f (b + 1) - f b| + |f b - f a| := abs_sub_le _ _ _
      _ ≤ e + ((b : ℝ) - a) * e := add_le_add (hstep b hab (Nat.lt_succ_self b)) hprev
      _ = _ := by push_cast; ring

theorem window_log_error (f : ℕ → ℝ) (μ L e : ℝ) (he : 0 ≤ e)
    (a b : ℕ) (ha : |(a : ℝ) - μ| ≤ L) (hb : |(b : ℝ) - μ| ≤ L)
    (hstep : ∀ j : ℕ, |(j : ℝ) - μ| ≤ L → |(j + 1 : ℕ) - μ| ≤ L →
      |f (j + 1) - f j| ≤ e) : |f b - f a| ≤ 2 * L * e := by
  have go (a b : ℕ) (hab : a ≤ b) (ha : |(a : ℝ) - μ| ≤ L)
      (hb : |(b : ℝ) - μ| ≤ L) : |f b - f a| ≤ 2 * L * e := by
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hbound : (b : ℝ) - a ≤ 2 * L := by
      rcases abs_le.mp ha with ⟨ha₁, _⟩
      rcases abs_le.mp hb with ⟨_, hb₂⟩
      linarith
    apply (abs_sub_le_steps f a b hab e ?_).trans
      (mul_le_mul_of_nonneg_right hbound he)
    intro j haj hjb
    have haj' : (a : ℝ) ≤ j := by exact_mod_cast haj
    have hjb' : (j : ℝ) + 1 ≤ b := by exact_mod_cast hjb
    apply hstep j
    · apply abs_le.mpr
      rcases abs_le.mp ha with ⟨ha₁, _⟩
      rcases abs_le.mp hb with ⟨_, hb₂⟩
      constructor <;> linarith
    · apply abs_le.mpr
      rcases abs_le.mp ha with ⟨ha₁, _⟩
      rcases abs_le.mp hb with ⟨_, hb₂⟩
      push_cast
      constructor <;> linarith
  rcases le_total a b with hab | hba
  · exact go a b hab ha hb
  · rw [abs_sub_comm]
    exact go b a hba hb ha

/-- Pointwise log errors imply a common positive multiplicative normalizer.
The normalizer is chosen once at the floor of the real center. -/
theorem window_relative_error (P H : ℕ → ℝ) (μ L e : ℝ)
    (hμ : 0 ≤ μ) (hL : 1 ≤ L) (he : 0 ≤ e) (hsmall : 2 * L * e ≤ 1)
    (hP : ∀ k : ℕ, |(k : ℝ) - μ| ≤ L → 0 < P k)
    (hH : ∀ k : ℕ, |(k : ℝ) - μ| ≤ L → 0 < H k)
    (hstep : ∀ j : ℕ, |(j : ℝ) - μ| ≤ L → |(j + 1 : ℕ) - μ| ≤ L →
      |(Real.log (P (j + 1)) - Real.log (H (j + 1))) -
        (Real.log (P j) - Real.log (H j))| ≤ e) :
    ∃ N : ℝ, 0 < N ∧ ∀ k : ℕ, |(k : ℝ) - μ| ≤ L →
      |P k - N * H k| ≤ 4 * L * e * |N * H k| := by
  let a := Nat.floor μ
  have ha : |(a : ℝ) - μ| ≤ L := (Nat.abs_floor_sub_le hμ).trans hL
  let N := P a / H a
  have hN : 0 < N := div_pos (hP a ha) (hH a ha)
  refine ⟨N, hN, ?_⟩
  intro k hk
  have hNk : 0 < N * H k := mul_pos hN (hH k hk)
  have hlogN : Real.log N = Real.log (P a) - Real.log (H a) :=
    Real.log_div (hP a ha).ne' (hH a ha).ne'
  have hlog := window_log_error (fun j => Real.log (P j) - Real.log (H j))
    μ L e he a k ha hk hstep
  have heq : Real.log (P k) - Real.log (N * H k) =
      (Real.log (P k) - Real.log (H k)) - (Real.log (P a) - Real.log (H a)) := by
    rw [Real.log_mul hN.ne' (hH k hk).ne', hlogN]
    ring
  rw [← heq] at hlog
  have hrel := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_sub, Real.exp_log (hP k hk), Real.exp_log hNk] at hrel
  have hid : P k - N * H k = (P k / (N * H k) - 1) * (N * H k) := by
    field_simp [hN.ne', (hH k hk).ne']
  rw [hid, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ 2 * |Real.log (P k) - Real.log (N * H k)| := hrel
    _ ≤ 2 * (2 * L * e) := mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = _ := by ring

theorem abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x)| ≤ 2 * |x| := by
  have h := log_one_add_linear_error hx
  calc
    _ ≤ |Real.log (1 + x) - x| + |x| := by simpa using abs_sub_le (Real.log (1 + x)) x 0
    _ ≤ 2 * x ^ 2 + |x| := add_le_add h le_rfl
    _ ≤ _ := by nlinarith [sq_abs x, abs_nonneg x]

end MajorityDynamics.Analysis
