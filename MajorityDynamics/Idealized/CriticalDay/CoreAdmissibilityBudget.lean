import MajorityDynamics.Idealized.CriticalDay.AdmissibilitySeparation
import MajorityDynamics.Idealized.CriticalDay.AdmissibilityEdges

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal

/-- Terminal local admissibility from centered numerical geometry. It keeps
history conditioning and exact solving, but imposes no child-mass floor. -/
theorem core_admissible_of_centered_budget (n : ℕ) {v ζ M C : ℝ}
    (hv : 0 < v) (hζ : 0 < ζ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ s t, |ν n t*μ n s t| ≤ M)
    (hsep : ∀ s (r : Fin n), ζ ≤ sign (bits (n+1) s r.succ)*
      ∑ t, character r.castSucc t*(ν n t*μ n s t)) :
    ∃ K : ℝ, 1 ≤ K ∧ C ≤ K ∧
      ∀ (V : Type*) [Fintype V] (N : ℕ), Fintype.card V = N →
      ∀ p : ℝ, 0 < (N:ℝ) → 0 < p → (M+1)/v < Real.sqrt (p*N) →
      ∀ y : Local.CoarseData V n, y.reg = true →
      (∀ s, v*N ≤ (y.sizes s:ℝ)) →
      (∀ r : Fin n, |∑ t, character r.castSucc t*(y.sizes t:ℝ)| ≤
        (ζ/4)*(N:ℝ)/Real.sqrt (p*N)) →
      (∀ s t, |(y.realEdges s t/(y.sizes s:ℝ)-p*y.sizes t)/Real.sqrt (p*N)-
        ν n t*μ n s t| ≤ min 1 (ζ/(4*(Fintype.card (History (n+1)):ℝ)))) →
      ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
      (∀ s t, |(q s t:ℝ)-p| ≤ C*p/Real.sqrt (p*N)) →
      ∀ φ : ℝ, (∀ s, φ ≤ Binomial.eventMass (Local.trials y.sizes s) (q s)
        (Local.historySupport y.sizes s)) →
      Local.CoreAdmissible y q K φ p := by
  let K := 1+C+1/v+(M+1)+4/(v*ζ)+ζ/4
  have hv0 : 0 < 1/v := by positivity
  have hζ0 : 0 < 4/(v*ζ) := by positivity
  have hKv : 1/v ≤ K := by dsimp [K]; linarith
  have hKM : M+1 ≤ K := by dsimp [K]; linarith
  have hKζ : 4/(v*ζ) ≤ K := by dsimp [K]; linarith
  have hKC : C ≤ K := by dsimp [K]; linarith
  have hKbal : ζ/4 ≤ K := by dsimp [K]; linarith
  have hK1 : 1 ≤ K := by dsimp [K]; linarith
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hinv : K⁻¹ ≤ v := by
    rw [inv_eq_one_div,div_le_iff₀ hK]
    have hh := (div_le_iff₀ hv).mp hKv
    nlinarith only [hh]
  have hinvζ : K⁻¹ < v*ζ/2 := by
    have hh := (div_le_iff₀ (mul_pos hv hζ)).mp hKζ
    have hi : K⁻¹ ≤ v*ζ/4 := by
      rw [inv_eq_one_div,div_le_iff₀ hK]
      nlinarith only [hh]
    nlinarith [mul_pos hv hζ]
  refine ⟨K,hK1,hKC,?_⟩
  intro V inst N hcard p hN hp hlarge y hreg hsizes hbal hcenter q hsol htilt φ hcond
  have hS : 0 < Real.sqrt (p*N) := Real.sqrt_pos.mpr (mul_pos hp hN)
  have hEsc : 0 < Local.edgeScale N p := by unfold Local.edgeScale; positivity
  have he := admissible_edges_of_centered y hcard hN hp hv hM hsizes hbound
    (fun s t => (hcenter s t).trans (min_le_left _ _)) hlarge
  have hsp := separation_of_centered_target hN hp hv hζ
    (fun s => (y.sizes s:ℝ)) y.realEdges hsizes hbal
    (fun s t => (hcenter s t).trans (min_le_right _ _)) hsep
  refine ⟨hreg,?_,?_,?_,fun s t => (he s t).2,?_,?_,hcond,hsol⟩
  · intro s
    simpa only [hcard] using (mul_le_mul_of_nonneg_right hinv hN.le).trans (hsizes s)
  · intro r
    simpa only [hcard] using (hbal r).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKbal hN.le) hS.le)
  · intro s t
    simpa only [hcard] using (he s t).1.trans (mul_le_mul_of_nonneg_right hKM hEsc.le)
  · intro s r
    have hh := (mul_lt_mul_of_pos_right hinvζ hEsc).trans_le (hsp s r)
    simpa only [hcard] using Local.decision_of_strict_margin
      (bits (n+1) s r.castSucc) (bits (n+1) s r.succ) hh
  · intro s t
    simpa only [hcard] using (htilt s t).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC hp.le) hS.le)

end MajorityDynamics.Idealized.CriticalDay
