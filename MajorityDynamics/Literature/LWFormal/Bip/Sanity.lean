import MajorityDynamics.Literature.LWFormal.Bip.Statement

set_option autoImplicit true

/-! Finite sanity checks of the bipartite definitions. -/

namespace LW.Bip

example : N (ℓ := 2) (n := 2) (fun _ => 1, fun _ => 1) = 2 := by decide
example : N (ℓ := 2) (n := 2) (![2, 0], ![1, 1]) = 1 := by decide
example : N (ℓ := 2) (n := 2) (![2, 0], ![2, 0]) = 0 := by decide
example : N (ℓ := 2) (n := 3) (fun _ => 2, ![2, 1, 1]) = 2 := by decide
example : N (ℓ := 3) (n := 3) (fun _ => 2, fun _ => 2) = 6 := by native_decide
example : (Gm 2 2 2).card = 6 := by decide
example : (Gm 3 3 3).card = 84 := by native_decide

example : probG 2 2 2 (fun _ => 1) (fun _ => 1) = 1 / 3 := by
  simp only [probG, prob]
  rw [show ((Gm 2 2 2).filter fun E => ldeg E = (fun _ => 1) ∧ rdeg E = fun _ => 1).card = 2 by
    decide, show (Gm 2 2 2).card = 6 by decide]
  norm_num

example : probB 2 2 2 (fun _ => 1) (fun _ => 1) = 4 / 9 := by
  simp [probB, show Nat.choose 4 2 = 6 by decide]; norm_num

example : probG 2 2 2 ![2, 0] ![1, 1] = 1 / 6 := by
  simp only [probG, prob]
  rw [show ((Gm 2 2 2).filter fun E => ldeg E = ![2, 0] ∧ rdeg E = ![1, 1]).card = 1 by
    decide, show (Gm 2 2 2).card = 6 by decide]
  norm_num

example : probB 2 2 2 ![2, 0] ![1, 1] = 1 / 9 := by
  simp [probB, Fin.prod_univ_succ, show Nat.choose 4 2 = 6 by decide]; norm_num

example : mean (![2, 1, 1] : Fin 3 → ℕ) = 4 / 3 := by
  simp [mean, Fin.sum_univ_succ]; norm_num

example : muN (ℓ := 2) (n := 3) (fun _ => 3) (fun _ => 2) = 1 := by
  simp [muN]; norm_num

example : muN (ℓ := 2) (n := 3) ![2, 1] ![1, 1, 1] = 1 / 2 := by
  simp [muN, Fin.sum_univ_succ]; norm_num

example : Htilde (ℓ := 2) (n := 2) (fun _ => 1) (fun _ => 1) = Real.exp (-(1 / 2)) := by
  simp [Htilde, var, mean, muN]

example : probEdge 2 2 2 (fun _ => 1) (fun _ => 1) 0 0 = 1 / 2 := by
  simp only [probEdge, probG, prob]
  rw [show ((Gm 2 2 2).filter fun E =>
      ldeg E = (fun _ => 1) ∧ rdeg E = (fun _ => 1) ∧ ((0 : Fin 2), (0 : Fin 2)) ∈ E).card = 1 by
    decide, show ((Gm 2 2 2).filter fun E => ldeg E = (fun _ => 1) ∧ rdeg E = fun _ => 1).card = 2 by
    decide, show (Gm 2 2 2).card = 6 by decide]
  norm_num

example : probEdge 2 3 4 (fun _ => 2) ![2, 1, 1] 0 0 = 1 := by
  simp only [probEdge, probG, prob]
  rw [show ((Gm 2 3 4).filter fun E =>
      ldeg E = (fun _ => 2) ∧ rdeg E = ![2, 1, 1] ∧ ((0 : Fin 2), (0 : Fin 3)) ∈ E).card = 2 by
    decide, show ((Gm 2 3 4).filter fun E => ldeg E = (fun _ => 2) ∧ rdeg E = ![2, 1, 1]).card = 2 by
    decide, show (Gm 2 3 4).card = 15 by decide]
  norm_num

example : probEdge 2 3 4 (fun _ => 2) ![2, 1, 1] 0 1 = 1 / 2 := by
  simp only [probEdge, probG, prob]
  rw [show ((Gm 2 3 4).filter fun E =>
      ldeg E = (fun _ => 2) ∧ rdeg E = ![2, 1, 1] ∧ ((0 : Fin 2), (1 : Fin 3)) ∈ E).card = 1 by
    decide, show ((Gm 2 3 4).filter fun E => ldeg E = (fun _ => 2) ∧ rdeg E = ![2, 1, 1]).card = 2 by
    decide, show (Gm 2 3 4).card = 15 by decide]
  norm_num

end LW.Bip
