import MajorityDynamics.Analysis.Perturbation.Assembly
import MajorityDynamics.Analysis.Perturbation.CompactGeometry
import MajorityDynamics.Analysis.Perturbation.LocalCorrection
import MajorityDynamics.Analysis.Perturbation.Cones
import MajorityDynamics.Analysis.ConditionalGaussian.Main

/-!
# Appendix D.3, proved modulo the explicit Brouwer input

Source: `latest/main.tex`, `thm:perturbed-bijection`, including its compact-cone
application. The conditional assembly discharges every internal geometric and
analytic contract. The closed targets use only the named external Brouwer
axiom in addition to the standard foundations. The final specialization uses
the concrete conditional-mean bijection already proved in D.2.
-/

noncomputable section

namespace MajorityDynamics.Analysis.Perturbation

/-- The full perturbation theorem, with the external theorem supplied explicitly. -/
theorem perturbation_of_brouwer (hb : Literature.BrouwerClosedBall) :
    PerturbationTheorem := by
  intro d _hd B f K hK hKB C₀ hC₀
  exact perturbationAt_of_control (localPerturbation_of_brouwer hb) f K C₀ hC₀
    (compactControl f hK hKB)
    (fun _ hy => norm_inv_add_one_le_inverseRadius f hK hKB hy)

/-- D.3 with no remaining internal assumptions; Brouwer is the accepted external input. -/
theorem perturbation : PerturbationTheorem :=
  perturbation_of_brouwer Literature.brouwer_closedBall

/-- The paper's compact-cone application, including empty targets and zero rows. -/
theorem cone_perturbation : ConePerturbationTheorem :=
  conePerturbation_of_perturbation perturbation

/-- Apply D.3 to the actual Gaussian conditional-mean map proved in D.2. -/
theorem gaussian_cone_perturbation : GaussianConePerturbationTheorem := by
  intro d r hd hr M hM S hS T hT C₀ hC₀
  obtain ⟨_, _, _, f, hf⟩ := ConditionalGaussian.cone_bijection d r hd hr M hM S hS
  exact ⟨f, hf, cone_perturbation d r hd hr M hM f T hT C₀ hC₀⟩

/-- Both exact targets in the paper's D.3 statement. -/
theorem main : PerturbationTheorem ∧ ConePerturbationTheorem :=
  ⟨perturbation, cone_perturbation⟩

end MajorityDynamics.Analysis.Perturbation
