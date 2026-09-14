import MajorityDynamics.GraphProcess.FiberTransference.Denominator
import MajorityDynamics.GraphProcess.RowGamma.Shared

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

/-- B.3 and B.4 use one constant selected before every polynomial exponent. -/
def GammaTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T*(N : ℝ)^(-θ) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
    RowGamma.Conclusion y q C p A N ∧
    (cond (GraphicalArray.law y.part y.edge)
      (GraphicalArray.historyRegular p y.part)).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ Real.exp (-(N : ℝ))

theorem gamma_of_denominator {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ)
    (hden : DenominatorTheorem.{u} θ T n) : GammaTheorem.{u} θ T φ n := by
  obtain ⟨D,hD,Nd,hd⟩ := hden
  obtain ⟨C,hC,hshared⟩ := RowGamma.uniform_shared_constant (K := D+1) n
    hθlo hθhi hT hφ (by positivity)
  refine ⟨C,hC,?_⟩
  intro A hA
  obtain ⟨Ns,hs⟩ := hshared A hA
  refine ⟨max Nd Ns,?_⟩
  intro N hN V inst hcard p hlo hhi y q had
  obtain ⟨hp,hrow,_,hnum⟩ := hs N (by omega) V hcard p hlo hhi y q had
  refine ⟨hrow,?_⟩
  have hdenom := hd N (by omega) V hcard p hlo hhi y q φ had
  have heq : (RowArray.exactTotals y.part y.edge ∩ GraphicalArray.historyRegular p y.part) ∩
      {d | ¬ RowArray.Gamma y.part y.edge C p d} =
    {d | ¬ RowArray.Gamma y.part y.edge C p d ∧ d ∈ RowArray.history y.part ∧
      RowArray.Regular p d ∧ d ∈ RowArray.exactTotals y.part y.edge} := by
    ext d
    simp only [GraphicalArray.historyRegular,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  rw [graphical_history_cond p y hp.1 hp.2,
    RowExactTotals.conditioned_real_eq_div _ _ _ (Set.to_countable _).measurableSet, heq]
  have hpos := (Real.exp_pos _).trans_le hdenom
  calc
    _ ≤ Real.exp (-(D+1)*N) / Real.exp (-D*N) :=
      div_le_div₀ (by positivity) hnum (Real.exp_pos _) hdenom
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

end MajorityDynamics.GraphProcess.FiberTransference
