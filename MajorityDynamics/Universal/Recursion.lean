import MajorityDynamics.Universal.Splitting

/-!
# The actual universal recursion and its all-level invariants

Source: `def:universal-nu-mu`, `eq:gamma-defining`, `eq:children-sum`,
and `lem:universal-well-defined`. Each next level is constructed from the
actual Gaussian integrals. The validity proof is carried by induction; no
recurrence identity or cone invariant is supplied as an unproved input.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

variable {n : ℕ}

def Level.gamma (a : Level n) (h : a.Valid) (s : History (n + 1)) : Row (n + 1) :=
  (meanBijection s a.ν h.positive).invFun (a.weightedRow s)

theorem Level.gamma_defining (a : Level n) (h : a.Valid) (s : History (n + 1)) :
    meanMap s a.ν (a.gamma h s) = a.weightedRow s := by
  have hr := (meanBijection s a.ν h.positive).right_inv (a.weightedRow s) (h.cone s)
  rwa [meanBijection_toFun] at hr

def Level.next (a : Level n) (h : a.Valid) : Level (n + 1) where
  ν u := a.ν (parent u) * branchProbability (parent u) a.ν (a.gamma h (parent u)) (last u)
  μ u v := branchMean (parent u) a.ν (a.gamma h (parent u)) (last u) (parent v) / a.ν (parent v) +
    branchMean (parent v) a.ν (a.gamma h (parent v)) (last v) (parent u) / a.ν (parent u) -
    a.μ (parent u) (parent v)

@[simp] theorem Level.next_ν_append (a : Level n) (h : a.Valid) (s : History (n + 1)) (b : Bool) :
    (a.next h).ν (append s b) = a.ν s * branchProbability s a.ν (a.gamma h s) b := by
  simp [Level.next]

@[simp] theorem Level.next_μ_append (a : Level n) (h : a.Valid)
    (s t : History (n + 1)) (b c : Bool) :
    (a.next h).μ (append s b) (append t c) =
      branchMean s a.ν (a.gamma h s) b t / a.ν t +
      branchMean t a.ν (a.gamma h t) c s / a.ν s - a.μ s t := by
  simp [Level.next]

theorem Level.next_children_mass (a : Level n) (h : a.Valid) (s : History (n + 1)) :
    (a.next h).ν (append s false) + (a.next h).ν (append s true) = a.ν s := by
  rw [a.next_ν_append, a.next_ν_append, ← mul_add,
    branchProbability_add s a.ν h.positive, mul_one]

/-- The elementary cancellation in the paper's children-sum computation. -/
private theorem children_sum_algebra (u v p q A B C m : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hpq : p + q = 1) (hmean : p * B + q * C = u * m) :
    (v * p) * (A / v + B / u - m) + (v * q) * (A / v + C / u - m) = A := by
  calc
    _ = ((v * (p + q)) / v) * A + (v / u) * (p * B + q * C) - v * (p + q) * m := by
      field_simp
      ring
    _ = A := by
      rw [hpq, hmean]
      field_simp
      ring

theorem Level.children_sum (a : Level n) (h : a.Valid)
    (s t : History (n + 1)) (b : Bool) :
    (a.next h).weightedRow (append s b) (append t false) +
      (a.next h).weightedRow (append s b) (append t true) =
        branchMean s a.ν (a.gamma h s) b t := by
  have hm := congrArg (fun x : Row (n + 1) => x s)
    (branchMean_total t a.ν h.positive (a.gamma h t))
  rw [a.gamma_defining h t] at hm
  change branchProbability t a.ν (a.gamma h t) false * branchMean t a.ν (a.gamma h t) false s +
      branchProbability t a.ν (a.gamma h t) true * branchMean t a.ν (a.gamma h t) true s =
        a.ν s * a.μ t s at hm
  rw [h.symmetric t s] at hm
  change (a.next h).ν (append t false) * (a.next h).μ (append s b) (append t false) +
    (a.next h).ν (append t true) * (a.next h).μ (append s b) (append t true) = _
  simp only [Level.next_ν_append, Level.next_μ_append]
  exact children_sum_algebra _ _ _ _ _ _ _ _ (h.positive s).ne' (h.positive t).ne'
    (branchProbability_add t a.ν h.positive _) hm

theorem Level.next_valid (a : Level n) (h : a.Valid) : (a.next h).Valid where
  positive u := mul_pos (h.positive (parent u))
    (branchProbability_pos _ _ h.positive _ _)
  total := by rw [sum_children]; simpa only [Level.next_children_mass] using h.total
  symmetric u v := by
    change _ + _ - a.μ (parent u) (parent v) = _ + _ - a.μ (parent v) (parent u)
    rw [h.symmetric (parent u) (parent v), add_comm]
  cone u := by
    rw [← append_parent_last u]
    exact historyCone_of_children (parent u) (last u) _ _
      (fun t => a.children_sum h (parent u) t (last u))
      (branchMean_mem _ _ h.positive _ _)

def initialLevel : Level 0 where
  ν _ := 1 / 2
  μ _ _ := 0

theorem initialLevel_valid : initialLevel.Valid where
  positive _ := by norm_num [initialLevel]
  total := by simp [initialLevel, History]
  symmetric _ _ := rfl
  cone _ := by simp

/-- Induction constructs data together with the proofs needed to take the next step. -/
def validSequence : (n : ℕ) → {a : Level n // a.Valid}
  | 0 => ⟨initialLevel, initialLevel_valid⟩
  | n + 1 => ⟨(validSequence n).val.next (validSequence n).property,
      (validSequence n).val.next_valid (validSequence n).property⟩

def universal (n : ℕ) : Level n := (validSequence n).val

/-- `lem:universal-well-defined`, for the actual recursively constructed levels. -/
theorem universal_valid (n : ℕ) : (universal n).Valid := (validSequence n).property

def ν (n : ℕ) : History (n + 1) → ℝ := (universal n).ν
def μ (n : ℕ) : History (n + 1) → History (n + 1) → ℝ := (universal n).μ
def γ (n : ℕ) (s : History (n + 1)) : Row (n + 1) :=
  (universal n).gamma (universal_valid n) s

@[simp] theorem universal_zero : universal 0 = initialLevel := rfl
theorem universal_succ (n : ℕ) : universal (n + 1) = (universal n).next (universal_valid n) := rfl

theorem ν_positive (n : ℕ) (s : History (n + 1)) : 0 < ν n s := (universal_valid n).positive s
theorem ν_total (n : ℕ) : ∑ s, ν n s = 1 := (universal_valid n).total
theorem μ_symmetric (n : ℕ) (s t : History (n + 1)) : μ n s t = μ n t s :=
  (universal_valid n).symmetric s t

theorem weightedRow_mem (n : ℕ) (s : History (n + 1)) :
    WithLp.toLp 2 (fun t => ν n t * μ n s t) ∈ historyCone s := (universal_valid n).cone s

theorem γ_defining (n : ℕ) (s : History (n + 1)) :
    meanMap s (ν n) (γ n s) = WithLp.toLp 2 (fun t => ν n t * μ n s t) :=
  (universal n).gamma_defining (universal_valid n) s

theorem ν_recursion (n : ℕ) (s : History (n + 1)) (b : Bool) :
    ν (n + 1) (append s b) = ν n s * branchProbability s (ν n) (γ n s) b :=
  (universal n).next_ν_append (universal_valid n) s b

theorem μ_recursion (n : ℕ) (s t : History (n + 1)) (b c : Bool) :
    μ (n + 1) (append s b) (append t c) =
      branchMean s (ν n) (γ n s) b t / ν n t +
      branchMean t (ν n) (γ n t) c s / ν n s - μ n s t :=
  (universal n).next_μ_append (universal_valid n) s t b c

@[simp] theorem ν_zero (s : History 1) : ν 0 s = 1 / 2 := rfl
@[simp] theorem μ_zero (s t : History 1) : μ 0 s t = 0 := rfl
@[simp] theorem γ_zero (s : History 1) : γ 0 s = 0 := by
  have h := γ_defining 0 s
  rw [meanMap_one] at h
  exact h.trans (by ext t; simp)

end MajorityDynamics.Universal
