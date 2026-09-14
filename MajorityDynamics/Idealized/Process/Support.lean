import MajorityDynamics.Local.RowModel
import MajorityDynamics.Universal.Geometry
import Lean.Elab.Tactic.Omega

/-!
# Full affine support of every idealized row

The uniqueness step of Theorem 5.2 needs only a fixed lower bound on the
coordinate sizes.  A small explicit integer simplex already lies in each
strict child event: give coordinate `t` twice the number of requested signs
matching `t`, plus one.  Orthogonality of the binary characters makes every
signed margin exactly the number of histories.  Adding one to any coordinate
preserves all strict inequalities.  Thus the original mixed tie events have
full affine support, including the exact diagonal trial deletion.
-/

noncomputable section
open Set
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process
open Universal

variable {n k : ℕ}

private def simplexBase (w : Fin k → Bool) (t : History k) : ℕ :=
  1 + ∑ r : Fin k, if bits k t r = w r then 2 else 0

private theorem simplexBase_le (w : Fin k → Bool) (t : History k) :
    simplexBase w t ≤ 1 + 2 * k := by
  unfold simplexBase
  have h : (∑ r : Fin k, if bits k t r = w r then 2 else 0) ≤ ∑ _r : Fin k, 2 := by
    apply Finset.sum_le_sum
    intro r _
    split_ifs <;> omega
  simpa [mul_comm] using Nat.add_le_add_left h 1

private theorem simplexBase_cast (w : Fin k → Bool) (t : History k) :
    (simplexBase w t : ℝ) = (k : ℝ) + 1 +
      ∑ r : Fin k, sign (w r) * character r t := by
  have he (r : Fin k) :
      ((if bits k t r = w r then 2 else 0 : ℕ) : ℝ) =
        1 + sign (w r) * character r t := by
    cases ht : bits k t r <;> cases hw : w r <;> norm_num [character, ht]
  simp only [simplexBase, Nat.cast_add, Nat.cast_one, Nat.cast_sum, he,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  ring

private theorem simplexBase_margin (w : Fin k → Bool) (r : Fin k) :
    sign (w r) * (∑ t : History k, character r t * (simplexBase w t : ℝ)) =
      (Fintype.card (History k) : ℝ) := by
  have hzero : (∑ t : History k, character r t) = 0 := by
    simpa using sum_character_of_flip_invariant (fun _ : History k => (1 : ℝ))
      (fun _ => rfl) r
  have he : (∑ t : History k, character r t * (simplexBase w t : ℝ)) =
      sign (w r) * (Fintype.card (History k) : ℝ) := by
    calc
      _ = (∑ t : History k, character r t) * ((k : ℝ) + 1) +
          imbalance r (synthesize (fun q => sign (w q))) := by
        change _ = (∑ t : History k, character r t) * ((k : ℝ) + 1) +
          ∑ t : History k, character r t * ∑ q : Fin k, sign (w q) * character q t
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        rw [simplexBase_cast]
        ring
      _ = _ := by rw [hzero, zero_mul, zero_add, imbalance_synthesize, mul_comm]
  rw [he, ← mul_assoc, sign_sq, one_mul]

private def childPattern (s : History (n + 1)) (b : Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (fun r : Fin n => bits (n + 1) s r.succ) b

private def supportBase (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) : Binomial.Box (Local.trials sizes s) :=
  fun t => ⟨simplexBase (childPattern s b) t, by
    have h := simplexBase_le (childPattern s b) t
    have hs := hsize t
    simp only [Local.trials]
    split_ifs <;> omega⟩

private def supportNeighbor (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (i : History (n + 1)) :
    Binomial.Box (Local.trials sizes s) :=
  fun t => ⟨simplexBase (childPattern s b) t + if t = i then 1 else 0, by
    have h := simplexBase_le (childPattern s b) t
    have hs := hsize t
    simp only [Local.trials]
    split_ifs <;> omega⟩

private theorem supportBase_mem (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) :
    supportBase sizes s b hsize ∈ Local.childSupport sizes s b := by
  rw [Local.mem_childSupport]
  have hm (r : Fin (n + 1)) :
      0 < sign (childPattern s b r) *
        imbalance r (Local.rowVector (supportBase sizes s b hsize)) := by
    change 0 < sign (childPattern s b r) *
      ∑ t, character r t * (simplexBase (childPattern s b) t : ℝ)
    rw [simplexBase_margin]
    exact history_card_pos _
  constructor
  · intro r
    left
    simpa [childPattern] using hm r.castSucc
  · left
    simpa [childPattern] using hm (Fin.last n)

private theorem supportNeighbor_mem (sizes : Local.Sizes n)
    (s : History (n + 1)) (b : Bool) (hsize : ∀ t, 2 * n + 5 ≤ sizes t)
    (i : History (n + 1)) :
    supportNeighbor sizes s b hsize i ∈ Local.childSupport sizes s b := by
  rw [Local.mem_childSupport]
  have hm (r : Fin (n + 1)) :
      0 < sign (childPattern s b r) *
        imbalance r (Local.rowVector (supportNeighbor sizes s b hsize i)) := by
    change 0 < sign (childPattern s b r) *
      ∑ t, character r t *
        ((simplexBase (childPattern s b) t + if t = i then 1 else 0 : ℕ) : ℝ)
    have he : (∑ t : History (n + 1), character r t *
        ((simplexBase (childPattern s b) t + if t = i then 1 else 0 : ℕ) : ℝ)) =
        (∑ t, character r t * (simplexBase (childPattern s b) t : ℝ)) + character r i := by
      simp [Nat.cast_add, mul_add, Finset.sum_add_distrib]
    rw [he, mul_add, simplexBase_margin]
    have hcard : (2 : ℝ) ≤ Fintype.card (History (n + 1)) := by
      rw [history_card, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    have hsign : -(1 : ℝ) ≤ sign (childPattern s b r) * character r i := by
      cases h₁ : childPattern s b r <;> cases h₂ : bits (n + 1) i r <;>
        norm_num [character, h₁, h₂]
    linarith
  constructor
  · intro r
    left
    simpa [childPattern] using hm r.castSucc
  · left
    simpa [childPattern] using hm (Fin.last n)

/-- Even each child event contains an explicit affine coordinate simplex. -/
theorem childSupport_fullAffineSupport (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (s : History (n + 1)) (b : Bool) :
    Analysis.FiniteTilt.FullAffineSupport (Local.childSupport sizes s b) Binomial.vector := by
  classical
  intro u c hc
  have hbase := hc (supportBase sizes s b hsize) (supportBase_mem sizes s b hsize)
  funext i
  have hnext := hc (supportNeighbor sizes s b hsize i)
    (supportNeighbor_mem sizes s b hsize i)
  have he : (∑ t, u t * Binomial.vector (supportNeighbor sizes s b hsize i) t) =
      (∑ t, u t * Binomial.vector (supportBase sizes s b hsize) t) + u i := by
    simp [Binomial.vector, supportNeighbor, supportBase, Nat.cast_add, mul_add,
      Finset.sum_add_distrib]
  rw [he, hbase] at hnext
  change u i = 0
  linarith

theorem historySupport_fullAffineSupport (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (s : History (n + 1)) :
    Analysis.FiniteTilt.FullAffineSupport (Local.historySupport sizes s) Binomial.vector := by
  intro u c hc
  apply childSupport_fullAffineSupport sizes hsize s false u c
  intro a ha
  exact hc a (Local.childSupport_subset sizes s false ha)

theorem childSupport_nonempty (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (s : History (n + 1)) (b : Bool) :
    (Local.childSupport sizes s b).Nonempty :=
  ⟨supportBase sizes s b hsize, supportBase_mem sizes s b hsize⟩

theorem historySupport_nonempty (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (s : History (n + 1)) :
    (Local.historySupport sizes s).Nonempty :=
  (childSupport_nonempty sizes hsize s false).mono (Local.childSupport_subset sizes s false)

theorem history_eventMass_pos (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (s : History (n + 1))
    (q : History (n + 1) → Binomial.Probability) :
    0 < Binomial.eventMass (Local.trials sizes s) q (Local.historySupport sizes s) :=
  Binomial.eventMass_pos _ _ (historySupport_nonempty sizes hsize s)

theorem child_eventMass_pos (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (s : History (n + 1)) (b : Bool)
    (q : History (n + 1) → Binomial.Probability) :
    0 < Binomial.eventMass (Local.trials sizes s) q (Local.childSupport sizes s b) :=
  Binomial.eventMass_pos _ _ (childSupport_nonempty sizes hsize s b)

/-- The uniqueness hypothesis in the local-template API is now discharged. -/
theorem solving_tilt_unique (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (m : Local.EdgeCounts n)
    {q q' : Local.Tilt n} (hq : Local.Solves sizes m q) (hq' : Local.Solves sizes m q') : q = q' :=
  Local.solving_tilt_unique sizes (fun t => by have := hsize t; omega) m
    (historySupport_fullAffineSupport sizes hsize) hq hq'

end MajorityDynamics.Idealized.Process
