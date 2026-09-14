import MajorityDynamics.Idealized.PerturbedEvolution.AdmissibilitySeparation

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal

set_option maxHeartbeats 800000 in
/-- Small earlier size imbalances and the correctly centered edge target
retain a fixed fraction of the universal strict cone margin. -/
theorem separation_of_centered_target {n N : ℕ} {p v ζ : ℝ}
    (hN : 0 < (N : ℝ)) (hp : 0 < p) (hv : 0 < v) (hζ : 0 < ζ)
    (η : History (n+1) → ℝ) (e : History (n+1) → History (n+1) → ℝ)
    (hsizes : ∀ s, v*N ≤ η s)
    (hbalance : ∀ r : Fin n, |∑ t, character r.castSucc t*η t| ≤
      (ζ/4)*(N : ℝ)/Real.sqrt (p*N))
    (htarget : ∀ s t, |(e s t/η s-p*η t)/Real.sqrt (p*N)-ν n t*μ n s t| ≤
      ζ/(4*(Fintype.card (History (n+1)) : ℝ)))
    (hsep : ∀ s (r : Fin n), ζ ≤ sign (bits (n+1) s r.succ)*
      ∑ t, character r.castSucc t*(ν n t*μ n s t)) :
    ∀ s (r : Fin n), (v*ζ/2)*Local.edgeScale N p ≤
      sign (bits (n+1) s r.succ)*∑ t, character r.castSucc t*e s t := by
  intro s r
  let S := Real.sqrt (p*N)
  have hS : 0 < S := Real.sqrt_pos.mpr (mul_pos hp hN)
  have hSsq : S^2 = p*N := Real.sq_sqrt (mul_pos hp hN).le
  have hη : 0 < η s := (mul_pos hv hN).trans_le (hsizes s)
  have hd : (0 : ℝ) < Fintype.card (History (n+1)) := Nat.cast_pos.mpr Fintype.card_pos
  let x := fun t => (e s t/η s-p*η t)/S
  have herr := PerturbedEvolution.signed_sum_error r.castSucc x
    (fun t => ν n t*μ n s t) (ζ/(4*(Fintype.card (History (n+1)) : ℝ))) (htarget s)
  have herr' : |(∑ t, character r.castSucc t*x t)-
      ∑ t, character r.castSucc t*(ν n t*μ n s t)| ≤ ζ/4 := by
    convert herr using 1
    field_simp
  have hb : |p/S*∑ t, character r.castSucc t*η t| ≤ ζ/4 := by
    rw [abs_mul,abs_of_pos (div_pos hp hS)]
    calc
      _ ≤ p/S*((ζ/4)*(N : ℝ)/S) :=
        mul_le_mul_of_nonneg_left (hbalance r) (div_pos hp hS).le
      _ = ζ/4 := by field_simp; nlinarith only [hSsq]
  have hidentity : (∑ t, character r.castSucc t*e s t)/(η s*S) =
      (∑ t, character r.castSucc t*x t)+p/S*∑ t, character r.castSucc t*η t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    dsimp [x]
    field_simp
    ring
  have hn : ζ/2 ≤ sign (bits (n+1) s r.succ)*
      ((∑ t, character r.castSucc t*e s t)/(η s*S)) := by
    rw [hidentity]
    have he := abs_le.mp herr'
    have hb' := abs_le.mp hb
    have hsp := hsep s r
    cases hbit : bits (n+1) s r.succ <;>
      simp only [hbit,sign_false,sign_true] at hsp ⊢ <;>
      linarith [he.1,he.2,hb'.1,hb'.2]
  have hm := (le_div_iff₀ (mul_pos hη hS)).mp
    (show ζ/2 ≤ (sign (bits (n+1) s r.succ)*
      ∑ t, character r.castSucc t*e s t)/(η s*S) by
        simpa only [mul_div_assoc] using hn)
  have hscale : Local.edgeScale N p = (N : ℝ)*S := by
    unfold Local.edgeScale
    apply (div_eq_iff hS.ne').mpr
    change (N : ℝ)^2*p = (N : ℝ)*S*S
    nlinarith only [hSsq]
  rw [hscale]
  have hs := mul_le_mul_of_nonneg_right (hsizes s) (mul_pos hζ hS).le
  nlinarith only [hm,hs]

end MajorityDynamics.Idealized.CriticalDay
