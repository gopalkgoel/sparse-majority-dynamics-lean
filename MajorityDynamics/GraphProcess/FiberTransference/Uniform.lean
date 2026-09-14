import MajorityDynamics.GraphProcess.FiberTransference.Real
import MajorityDynamics.GraphProcess.FiberTransference.Transfer

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

theorem transfer_of_comparison {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ)
    (hcomparison : ∀ CΓ : ℝ, 0 < CΓ →
      EnumerationComparison.StrongComparisonTheorem.{u} θ T CΓ n) :
    TransferTheorem.{u} θ T φ n := by
  have hden : DenominatorTheorem.{u} θ T n :=
    denominator_of_comparison n hθlo hθhi hT (hcomparison 1 zero_lt_one)
  obtain ⟨CΓ,hCΓ,hg⟩ := gamma_of_denominator n hθlo hθhi hT hφ hden
  obtain ⟨Ng,hg⟩ := hg 1 zero_lt_one
  obtain ⟨Cc,_hCc,Nc,hc⟩ := hcomparison CΓ (zero_lt_one.trans_le hCΓ)
  obtain ⟨Na,ha⟩ := AdmissibleFiber.uniform_admissible_unit n hθlo hθhi hT
  refine ⟨2*(Real.exp Cc)^2,by positivity,max Ng (max Nc Na),?_⟩
  intro N hN V inst hcard p hlo hhi y q had E
  have hsizes : ∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ) := fun s => by
    simpa only [← hcard, div_eq_mul_inv, mul_comm] using had.sizes s
  have hcounts : ∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N) := fun s t => by
    simpa only [← hcard, Local.CoarseData.realEdges, Local.edgeScale,
      mul_div_assoc,mul_assoc] using had.edge_scale s t
  obtain ⟨hrow,hgamma⟩ := hg N (by omega) V hcard p hlo hhi y q had
  exact actual_transfer p y q (ha N (by omega) V hcard p hlo hhi y q φ had).2.2
    hrow hgamma (hc N (by omega) V hcard p hlo hhi y hsizes hcounts q) E

end MajorityDynamics.GraphProcess.FiberTransference
