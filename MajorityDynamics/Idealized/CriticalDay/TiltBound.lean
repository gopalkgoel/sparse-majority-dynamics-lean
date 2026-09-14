import MajorityDynamics.Idealized.LinearResponse.Tilt
import MajorityDynamics.Idealized.LinearResponse.Rates
import MajorityDynamics.Idealized.RowLimits.Basic

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse
open Binomial.Approximation (Density)

theorem row_tilt_bound (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ T : ℝ), 1/2 < θ → θ < 1 → 1 < T →
      ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ σ : History (n+1) → Row (n+1), (∀ s t, |σ s t| ≤ R) →
      ∀ s t, |(RowLimits.rowTilt N p (σ s) t : ℝ)-(p:ℝ)| ≤
        C*(p:ℝ)/Real.sqrt ((p:ℝ)*N) := by
  classical
  let f : History (n+1) → ℝ := fun t => 2*Real.exp (R/ν n t)/ν n t*R
  have hf : ∀ t, 0 ≤ f t := by
    intro t
    dsimp [f]
    exact mul_nonneg (div_nonneg (by positivity) (ν_positive n t).le) hR
  let C := 1+∑ t, f t
  have hC : 0 < C := by
    have : 0 ≤ ∑ t, f t := Finset.sum_nonneg (fun t _ => hf t)
    dsimp [C]
    linarith
  have hCt : ∀ t, f t ≤ C := by
    intro t
    have := Finset.single_le_sum (fun t _ => hf t) (Finset.mem_univ t)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro θ T hθlo hθhi hT
  filter_upwards [eventually_basic θ T hθlo hθhi hT] with N hbasic
  intro p hp σ hσ s t
  have hbase := hbasic.2.2 p hp
  have hb := logitTilt_sub_p_le N p (ν n t) (σ s t) R (ν_positive n t) hR
    (by linarith [hbase.2.2]) hbase.1 (hσ s t)
  have hmul := mul_le_mul_of_nonneg_right (hCt t)
    (div_nonneg p.property.1.le (Real.sqrt_nonneg ((p:ℝ)*N)))
  change |(logitTilt N p (σ s t) (ν n t):ℝ)-(p:ℝ)| ≤ _
  have heq : (2*Real.exp (R/ν n t)/ν n t)*((p:ℝ)/Real.sqrt ((p:ℝ)*N))*R =
      f t*((p:ℝ)/Real.sqrt ((p:ℝ)*N)) := by dsimp [f]; ring
  rw [heq] at hb
  exact hb.trans (by simpa only [mul_div_assoc] using hmul)

end MajorityDynamics.Idealized.CriticalDay
