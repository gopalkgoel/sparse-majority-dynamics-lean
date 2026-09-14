import MajorityDynamics.Paper.MajorityStep
import Mathlib.Tactic.Positivity

/-!
# One-step contraction on a jumbled graph

A specialization of the deterministic argument in `lem:cklt-contraction` to
minimum degree `0.9 p N`. We use convenient sufficient thresholds: an initial
lead satisfying `p * lead ≥ 10 β` puts the minus set at most `N/5`, after which
each update contracts it by a factor `16 β² / (p N)²`.
No random-graph or external-paper axiom is used.
-/

noncomputable section
namespace MajorityDynamics.Paper

theorem minus_card_le {N : ℕ} (c : Coloring N) : (minusVertices c).card ≤ N := by
  have := plusCount_add_minus c
  omega

theorem next_minus_majority_edge_lower {N : ℕ} (G : Graph N) (c : Coloring N) :
    (orderedEdgeCount G (minusVertices (nextColoring G c)) Finset.univ : ℝ) / 2 ≤
      orderedEdgeCount G (minusVertices (nextColoring G c)) (minusVertices c) := by
  classical
  simp only [orderedEdgeCount_eq_sum, Nat.cast_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun v hv => half_degree_le_minus_degree G c v hv

/-- The jump to a small minority, using only jumbledness. -/
theorem jumbled_majority_jump {N : ℕ} (G : Graph N) (c : Coloring N)
    (p : unitInterval) (β : ℝ) (hβ : 0 < β) (hj : Jumbled G p β)
    (hlead : 10 * β ≤ (p : ℝ) * lead c) :
    ((minusVertices (nextColoring G c)).card : ℝ) ≤ (N : ℝ) / 5 := by
  let U := minusVertices (nextColoring G c)
  let W := minusVertices c
  let x : ℝ := U.card
  let m : ℝ := W.card
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hm : m ≤ (N : ℝ) := by
    dsimp [m, W]
    exact_mod_cast minus_card_le c
  have hhalf := next_minus_majority_edge_lower G c
  have hfull := (abs_le.mp (hj U Finset.univ)).1
  have hminus := (abs_le.mp (hj U W)).2
  simp only [Finset.card_univ, Fintype.card_fin] at hfull
  have hs : Real.sqrt (x * m) ≤ Real.sqrt (x * (N : ℝ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm hx)
  have hsβ := mul_le_mul_of_nonneg_left hs hβ.le
  have hsign := lead_eq_minus c
  have he : (p : ℝ) * x * lead c ≤ 3 * β * Real.sqrt (x * (N : ℝ)) := by
    rw [hsign]
    dsimp [x, m, U, W] at *
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hlead hx
  have hroot : 10 * x ≤ 3 * Real.sqrt (x * (N : ℝ)) := by
    apply (mul_le_mul_iff_right₀ hβ).mp
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 10 * x) hroot 2
  have hsquare := Real.sq_sqrt (mul_nonneg hx hN)
  by_cases hz : x = 0
  · change x ≤ _
    rw [hz]
    positivity
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have hcancel : 100 * x ≤ 9 * (N : ℝ) := by
      apply (mul_le_mul_iff_left₀ hxp).mp
      nlinarith
    change x ≤ _
    linarith

/-- A minority of size at most N/5 contracts by the stated factor. -/
theorem jumbled_majority_contract {N : ℕ} (G : Graph N) (c : Coloring N)
    (p : unitInterval) (β : ℝ) (hpN : 0 < (p : ℝ) * N)
    (hj : Jumbled G p β) (hd : minimumDegree G p)
    (hm : ((minusVertices c).card : ℝ) ≤ (N : ℝ) / 5) :
    ((minusVertices (nextColoring G c)).card : ℝ) ≤
      (16 * β ^ 2 / ((p : ℝ) * N) ^ 2) * (minusVertices c).card := by
  let U := minusVertices (nextColoring G c)
  let W := minusVertices c
  let x : ℝ := U.card
  let m : ℝ := W.card
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hmn : 0 ≤ m := Nat.cast_nonneg _
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hdegree : ∀ v, (9 / 10 : ℝ) * (p : ℝ) * N ≤ degreeInto G v Finset.univ := by
    intro v
    simpa using hd v
  have hlower := next_minus_edge_lower G c ((9 / 10 : ℝ) * (p : ℝ) * N) hdegree
  have hupper := (abs_le.mp (hj U W)).2
  have hmScaled := mul_le_mul_of_nonneg_left hm (mul_nonneg hp hx)
  have he : ((p : ℝ) * N / 4) * x ≤ β * Real.sqrt (x * m) := by
    dsimp [x, m, U, W] at *
    nlinarith
  have hs := pow_le_pow_left₀ (mul_nonneg (le_of_lt (div_pos hpN (by norm_num))) hx) he 2
  rw [mul_pow β, Real.sq_sqrt (mul_nonneg hx hmn)] at hs
  by_cases hz : x = 0
  · change x ≤ _
    rw [hz]
    positivity
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have hcancel : ((p : ℝ) * N) ^ 2 * x ≤ 16 * β ^ 2 * m := by
      apply (mul_le_mul_iff_left₀ hxp).mp
      nlinarith
    change x ≤ (16 * β ^ 2 / ((p : ℝ) * N) ^ 2) * m
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hpN)).mpr
    nlinarith

end MajorityDynamics.Paper
