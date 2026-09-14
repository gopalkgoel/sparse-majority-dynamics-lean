import MajorityDynamics.GraphProcess.CoarseKernel.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MajorityDynamics.GraphProcess.LocalTransition
open FineState Local CoarseKernel
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The real-valued finite mixture formula for the actual coarse transition law. -/
theorem Kbar_real_apply (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y)
    (B : Set (CoarseData V (n+1))) :
    (Kbar p y).real B = ∑ σ : State V n,
      (Lambda p y).real {σ} * (FineKernel.K σ).real {τ | rho p τ ∈ B} := by
  let := Lambda_probability p y hp hp1 hy
  unfold Measure.real
  rw [Kbar_apply, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro σ _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- A two-stage failure bound, averaged over the actual full coarse fiber.
The second-stage estimate is needed only on fine states in that fiber satisfying `F`. -/
theorem Kbar_failure_le (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y)
    (F : State V n → Prop) (S : State V n → State V (n+1) → Prop)
    (L : CoarseData V (n+1) → Prop)
    (hcombine : ∀ σ, rho p σ = y → F σ → ∀ τ, S σ τ → L (rho p τ))
    (epsf epss : ℝ) (_hepsf : 0 ≤ epsf) (hepss : 0 ≤ epss)
    (hf : (Lambda p y).real {σ | ¬ F σ} ≤ epsf)
    (hs : ∀ σ, rho p σ = y → F σ →
      (FineKernel.K σ).real {τ | ¬ S σ τ} ≤ epss) :
    (Kbar p y).real {z | ¬ L z} ≤ epsf + epss := by
  let := Lambda_probability p y hp hp1 hy
  have hmass : (∑ σ : State V n, (Lambda p y).real {σ}) = 1 := by
    simp
  have hbad : (∑ σ : State V n, if F σ then 0 else (Lambda p y).real {σ}) =
      (Lambda p y).real {σ | ¬ F σ} := by
    classical
    simpa only [Finset.sum_filter, Finset.mem_univ, true_and, not_not, ite_not,
      Finset.coe_filter, Finset.coe_univ, Set.ofPred_mem_eq, Set.sep_univ] using
      sum_measureReal_singleton (μ := Lambda p y) (Finset.univ.filter (fun σ => ¬ F σ))
  rw [Kbar_real_apply p y hp hp1 hy]
  calc
    _ ≤ ∑ σ : State V n, ((if F σ then 0 else (Lambda p y).real {σ}) +
        (Lambda p y).real {σ} * epss) := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hρ : rho p σ = y
      · by_cases hF : F σ
        · simp only [if_pos hF, zero_add]
          apply mul_le_mul_of_nonneg_left _ (measureReal_nonneg)
          have hsub : {τ | rho p τ ∈ {z | ¬ L z}} ⊆ {τ | ¬ S σ τ} := by
            intro τ hτ hS
            exact hτ (hcombine σ hρ hF τ hS)
          exact (measureReal_mono hsub).trans (hs σ hρ hF)
        · simp only [if_neg hF]
          have hk : (FineKernel.K σ).real {τ | rho p τ ∈ {z | ¬ L z}} ≤ 1 :=
            measureReal_le_one
          have hw : 0 ≤ (Lambda p y).real {σ} := measureReal_nonneg
          nlinarith
      · have hw : (Lambda p y).real {σ} = 0 := by
          simp only [Measure.real, Lambda_singleton p y hp hp1 hy σ, if_neg hρ,
            ENNReal.toReal_zero]
        simp [hw]
    _ = (Lambda p y).real {σ | ¬ F σ} + epss := by
      rw [Finset.sum_add_distrib, hbad, ← Finset.sum_mul, hmass, one_mul]
    _ ≤ epsf + epss := by linarith

end MajorityDynamics.GraphProcess.LocalTransition
