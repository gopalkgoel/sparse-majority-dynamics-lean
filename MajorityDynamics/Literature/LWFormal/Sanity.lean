import MajorityDynamics.Literature.LWFormal.Statements

set_option autoImplicit true

/-! Finite sanity checks of the basic definitions. -/

namespace LW

example : N (n := 3) (fun _ => 2) = 1 := by decide
example : N (n := 3) (fun _ => 1) = 0 := by decide
example : N (![2, 1, 1] : Fin 3 → ℤ) = 1 := by decide
example : N (![0, 0, 0] : Fin 3 → ℤ) = 1 := by decide
example : N (![3, 0, 0] : Fin 3 → ℤ) = 0 := by decide
example : N (![-1, 1, 0] : Fin 3 → ℤ) = 0 := by decide
example : edgeGraphCount 3 2 = 3 := by decide
example : edgeGraphCount 3 3 = 1 := by decide
example : edgeGraphCount 3 4 = 0 := by decide

example : N (n := 4) (fun _ => 1) = 3 := by native_decide
example : N (n := 4) (fun _ => 2) = 3 := by native_decide
example : N (n := 4) (fun _ => 3) = 1 := by native_decide
example : N (![3, 1, 1, 1] : Fin 4 → ℤ) = 1 := by native_decide
example : edgeGraphCount 4 2 = 15 := by native_decide
example : N (n := 5) (fun _ => 2) = 12 := by native_decide
example : edgeGraphCount 5 3 = 120 := by native_decide

example : avgDeg ![2, 1, 1] = 4 / 3 := by
  simp [avgDeg, Fin.sum_univ_succ]
  norm_num

example : density (n := 3) (fun _ => 2) = 1 := by
  simp [density, avgDeg]
  norm_num

example : gamma2 (n := 3) (fun _ => 2) = 0 := by
  simp [gamma2, avgDeg]

example : probBinom 3 3 (fun _ => 2) = 1 := by
  simp [probBinom]

example : probGnm 3 3 (fun _ => 2) = 1 := by
  simp only [probGnm, prob]
  rw [show ((Gnm 3 3).filter (degSeq · = fun _ => 2)).card = 1 by decide,
      show (Gnm 3 3).card = 1 by decide]
  norm_num

example : probGnm 4 2 ![2, 1, 1, 0] = 1 / 15 := by
  simp only [probGnm, prob]
  rw [show ((Gnm 4 2).filter (degSeq · = ![2, 1, 1, 0])).card = 1 by native_decide,
      show (Gnm 4 2).card = 15 by native_decide]
  norm_num

example : (Gnm 5 3).card = 120 := by native_decide

/-- The triangle: every edge is present. -/
example : probEdge 3 3 (fun _ => 2) 0 1 = 1 := by
  simp only [probEdge, probGnm, prob]
  rw [show ((Gnm 3 3).filter fun E => degSeq E = (fun _ => 2) ∧ s(0, 1) ∈ E).card = 1 by decide,
    show ((Gnm 3 3).filter (degSeq · = fun _ => 2)).card = 1 by decide,
    show (Gnm 3 3).card = 1 by decide]
  norm_num

/-- Perfect matchings on 4 vertices: `P(01 ∈ G) = 1/3`. -/
example : probEdge 4 2 (fun _ => 1) 0 1 = 1 / 3 := by
  simp only [probEdge, probGnm, prob]
  rw [show ((Gnm 4 2).filter fun E => degSeq E = (fun _ => 1) ∧ s(0, 1) ∈ E).card = 1 by
      native_decide,
    show ((Gnm 4 2).filter (degSeq · = fun _ => 1)).card = 3 by native_decide,
    show (Gnm 4 2).card = 15 by native_decide]
  norm_num

/-- Regular sequences: `var = 0`, the bracket is `1`, and the main factor is `d/(n-1)`. -/
example : var (n := 3) (fun _ => 2) = 0 := by simp [var, avgDeg]
example : edgeBracket 3 3 (fun _ => 2) 0 1 = 1 := by
  simp [edgeBracket, edgeBracket0, var, avgDeg]; norm_num
example : edgeMain 3 3 (fun _ => 2) 0 1 = 1 := by simp [edgeMain]; norm_num

end LW
