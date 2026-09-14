import MajorityDynamics.GraphProcess.FaithfulTrajectory.Lead
import MajorityDynamics.Idealized.PerturbedEvolution.Main
import MajorityDynamics.GraphProcess.CoarseKernel.Main

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution Universal

def responseLead (n : ℕ) : ℝ := ∑ s, character (Fin.last n) s*ε n s

theorem responseLead_pos (n : ℕ) : 0 < responseLead n := ε_lead_positive n

/-- Faithfulness produces the exact deterministic lead inequality before
absorbing the finite number of history errors. -/
theorem faithful_actual_lead {N n : ℕ} {p U δ τ : ℝ} {a : Process.Data}
    (G : Paper.Graph N) (c : Paper.Coloring N)
    (hsym : Process.StateSymmetric (a.state n))
    (hf : Faithful N p U δ τ a (CoarseKernel.rho p (FineState.actualState G c n))) :
    τ*sizeScale N p n*responseLead n -
      (Fintype.card (Universal.History (n+1)):ℝ)*(U*sizeScale N p n*(N:ℝ)^(-δ)) ≤
        Paper.lead (Paper.coloringOnDay G c (n+1)) := by
  rw [← signed_actual_partition G c]
  apply lead_of_size_errors _ (fun s => ((a.state n).sizes s:ℝ))
    (τ*sizeScale N p n) (U*sizeScale N p n*(N:ℝ)^(-δ))
  · intro s
    exact_mod_cast hsym.sizes s
  · exact hf.2.sizes

/-- The positive universal response dominates all faithful size errors with
its original factor one half. -/
theorem faithful_actual_lead_half {N n : ℕ} {p T U δ τ : ℝ} {a : Process.Data}
    (hT : 0 < T) (hτ : T⁻¹ ≤ τ)
    (hsmall : (Fintype.card (Universal.History (n+1)):ℝ)*U*(N:ℝ)^(-δ) ≤
      responseLead n/(2*T))
    (G : Paper.Graph N) (c : Paper.Coloring N)
    (hsym : Process.StateSymmetric (a.state n))
    (hf : Faithful N p U δ τ a (CoarseKernel.rho p (FineState.actualState G c n))) :
    (responseLead n/(2*T))*sizeScale N p n ≤
      Paper.lead (Paper.coloringOnDay G c (n+1)) := by
  have hS := responseLead_pos n
  have hscale : 0 ≤ sizeScale N p n := by unfold sizeScale; positivity
  have ht := mul_le_mul_of_nonneg_right hτ hS.le
  have he := mul_le_mul_of_nonneg_right hsmall hscale
  have heq : T⁻¹*responseLead n = 2*(responseLead n/(2*T)) := by field_simp
  rw [heq] at ht
  have ht' := mul_le_mul_of_nonneg_right ht hscale
  have hraw := faithful_actual_lead G c hsym hf
  nlinarith only [he,ht',hraw]

end MajorityDynamics.GraphProcess.FaithfulTrajectory
