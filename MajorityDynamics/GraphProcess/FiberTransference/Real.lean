import MajorityDynamics.GraphProcess.FiberTransference.Basic

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

theorem transfer_real_of_transfer {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (h : TransferTheorem.{u} θ T φ n) : TransferRealTheorem.{u} θ T φ n := by
  obtain ⟨C,hC,Nt,ht⟩ := h
  obtain ⟨Na,ha⟩ := AdmissibleFiber.uniform_admissible n hθlo hθhi hT
  refine ⟨C,hC,max Nt Na,?_⟩
  intro N hN V inst hcard p hlo hhi
  obtain ⟨hp,_⟩ := ha N (by omega) V hcard p hlo hhi
  exact ⟨hp,fun y q had E => ht N (by omega) V hcard ⟨p,hp.1.le,hp.2.le⟩
    hlo hhi y q had E⟩

/-- A positive-event version of B.3, with the original shared B.4 constant. -/
theorem gamma_lower_of_gamma {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (h : GammaTheorem.{u} θ T φ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      1-Real.exp (-(N : ℝ)) ≤
        (cond (GraphicalArray.law y.part y.edge)
          (GraphicalArray.historyRegular p y.part)).real
          {d | RowArray.Gamma y.part y.edge C p d} := by
  obtain ⟨C,hC,hg⟩ := h
  obtain ⟨Ng,hg⟩ := hg 1 zero_lt_one
  obtain ⟨Na,ha⟩ := AdmissibleFiber.uniform_admissible_unit n hθlo hθhi hT
  refine ⟨C,hC,max Ng Na,?_⟩
  intro N hN V inst hcard p hlo hhi y q had
  have hlaws := (ha N (by omega) V hcard p hlo hhi y q φ had).2.2
  let := hlaws.graphical_probability
  exact RowGamma.good_mass_lower _ _ (Set.to_countable _).measurableSet
    (hg N (by omega) V hcard p hlo hhi y q had).2

end MajorityDynamics.GraphProcess.FiberTransference
