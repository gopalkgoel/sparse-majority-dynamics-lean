import MajorityDynamics.Paper.Inputs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic counting for a majority update

The graph and update-rule facts used in the proof of `lem:cklt-contraction`
in `latest/main.tex` (source commit 4d8933a245e628a608569c4668e9e41c30c6f4bb).
These results use the concrete definitions of the paper scaffold and introduce
no mathematical axioms.
-/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Paper

def minusVertices {N : ℕ} (c : Coloring N) : Finset (Fin N) :=
  Finset.univ.filter fun v => c v = true

def degreeInto {N : ℕ} (G : Graph N) (v : Fin N) (W : Finset (Fin N)) : ℕ := by
  classical
  exact (W.filter fun w => G.Adj v w).card

theorem orderedEdgeCount_eq_sum {N : ℕ} (G : Graph N) (U W : Finset (Fin N)) :
    orderedEdgeCount G U W = ∑ v ∈ U, degreeInto G v W := by
  classical
  simp only [orderedEdgeCount, degreeInto, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

@[simp] theorem orderedEdgeCount_singleton {N : ℕ} (G : Graph N)
    (v : Fin N) (W : Finset (Fin N)) :
    orderedEdgeCount G {v} W = degreeInto G v W := by
  simp [orderedEdgeCount_eq_sum]

theorem plusCount_add_minus {N : ℕ} (c : Coloring N) :
    plusCount c + (minusVertices c).card = N := by
  classical
  simpa [plusCount, minusVertices] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v : Fin N => c v = false)

theorem lead_eq_minus {N : ℕ} (c : Coloring N) :
    lead c = (N : ℝ) - 2 * ((minusVertices c).card : ℝ) := by
  have h : (plusCount c : ℝ) + ((minusVertices c).card : ℝ) = N := by
    exact_mod_cast plusCount_add_minus c
  unfold lead
  linarith

theorem neighborSum_eq_degree {N : ℕ} (G : Graph N) (c : Coloring N) (v : Fin N) :
    neighborSum G c v = (degreeInto G v Finset.univ : ℤ) -
      2 * (degreeInto G v (minusVertices c) : ℤ) := by
  classical
  simp only [neighborSum, degreeInto, minusVertices, Finset.card_eq_sum_ones,
    Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : G.Adj v w <;> cases c w <;> simp [h, opinion]

/-- A next-day minus vertex has a nonpositive current neighbor sum, including ties. -/
theorem neighborSum_nonpos_of_next_minus {N : ℕ} (G : Graph N) (c : Coloring N)
    (v : Fin N) (hv : nextColoring G c v = true) : neighborSum G c v ≤ 0 := by
  by_contra h
  have hp : 0 < neighborSum G c v := lt_of_not_ge h
  simp [nextColoring, hp] at hv

/-- At least half the neighbors of a next-day minus vertex are currently minus. -/
theorem half_degree_le_minus_degree {N : ℕ} (G : Graph N) (c : Coloring N)
    (v : Fin N) (hv : v ∈ minusVertices (nextColoring G c)) :
    (degreeInto G v Finset.univ : ℝ) / 2 ≤ degreeInto G v (minusVertices c) := by
  have hm : nextColoring G c v = true := (Finset.mem_filter.mp hv).2
  have h := neighborSum_nonpos_of_next_minus G c v hm
  rw [neighborSum_eq_degree] at h
  have hr : (degreeInto G v Finset.univ : ℝ) -
      2 * (degreeInto G v (minusVertices c) : ℝ) ≤ 0 := by exact_mod_cast h
  linarith

/-- Aggregate version of the half-neighborhood bound. -/
theorem next_minus_edge_lower {N : ℕ} (G : Graph N) (c : Coloring N)
    (d : ℝ) (hdegree : ∀ v, d ≤ degreeInto G v Finset.univ) :
    d / 2 * ((minusVertices (nextColoring G c)).card : ℝ) ≤
      orderedEdgeCount G (minusVertices (nextColoring G c)) (minusVertices c) := by
  classical
  rw [orderedEdgeCount_eq_sum, Nat.cast_sum]
  calc
    _ = ∑ v ∈ minusVertices (nextColoring G c), d / 2 := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun v hv =>
      (div_le_div_of_nonneg_right (hdegree v) (by norm_num)).trans
        (half_degree_le_minus_degree G c v hv)

theorem minus_card_lt_one_iff {N : ℕ} (c : Coloring N) :
    ((minusVertices c).card : ℝ) < 1 ↔ ∀ v, c v = false := by
  constructor
  · intro h v
    have hz : (minusVertices c).card = 0 := by
      have : (minusVertices c).card < 1 := by exact_mod_cast h
      omega
    have he := Finset.card_eq_zero.mp hz
    cases hc : c v
    · rfl
    · have hm : v ∈ minusVertices c := by simp [minusVertices, hc]
      simp [he] at hm
  · intro h
    simp [minusVertices, h]

end MajorityDynamics.Paper
