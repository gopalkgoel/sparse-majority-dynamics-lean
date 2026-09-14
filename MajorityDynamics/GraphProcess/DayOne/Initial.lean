import MajorityDynamics.GraphProcess.DayOne.Deterministic
import MajorityDynamics.GraphProcess.DayOne.Floors
import MajorityDynamics.GraphProcess.DayOne.Rates

noncomputable section
set_option maxHeartbeats 800000
namespace MajorityDynamics.GraphProcess.DayOne
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedEvolution
open History
variable {V : Type*} [Fintype V]

/-- Deterministic initialization on the literal graph concentration event. -/
theorem initial_faithful {N : ℕ} {p : Binomial.Probability} {T τ δ : ℝ}
    {a : Process.Data} (ha : a.state 0 = Process.initialState N p)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T)
    (G : SimpleGraph V) (c : V → Bool) (hcard : Fintype.card V = N)
    (hplus : (Finset.univ.filter fun v => c v = false).card = N/2 + ⌊τ*Real.sqrt N⌋₊)
    (hr : CoarseKernel.Regular p (actualHistory G c 1) (degreeArray (actualHistory G c 1) G))
    (he : ∀ s t, |(edgeTotals (actualHistory G c 1) (degreeArray (actualHistory G c 1) G) s t : ℝ)-
      (p : ℝ)*(Local.partSizes (actualHistory G c 1) s : ℝ)*
      ((Local.partSizes (actualHistory G c 1) t : ℝ)-(if s=t then 1 else 0))| ≤
      2*(N : ℝ)*Real.sqrt (p : ℝ)*Real.log N)
    (hsabs : 2 ≤ Real.sqrt N*(N : ℝ)^(-δ))
    (heabs : 2*(N : ℝ)*Real.sqrt (p : ℝ)*Real.log N +
      (20*(T+1)^2)*(N : ℝ)*(p : ℝ) ≤
      betaScale N p 0*(N : ℝ)^(-δ)*(N : ℝ)^2*(p : ℝ)) :
    Faithful N p 1 δ τ a (CoarseKernel.actualCoarse p G c 0) := by
  refine faithful_of_initial_errors ha hN hT hτ0 hτT
    (CoarseKernel.actualCoarse p G c 0) ?_ ?_ ?_ ?_ hsabs heabs
  · exact (CoarseKernel.flag_true _ _ _).mpr hr
  · intro s
    change Local.partSizes (actualHistory G c 1) s ≤ N
    exact (initial_sizes_le_card G c s).trans_eq hcard
  · exact initial_sizes_floor_error G c hcard hτ0 hplus
  · exact he

end MajorityDynamics.GraphProcess.DayOne
