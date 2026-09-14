import MajorityDynamics.GraphProcess.FiberTransference.Uniform
import MajorityDynamics.GraphProcess.FiberTransference.SparseDenominator
import MajorityDynamics.GraphProcess.RowGamma.Sparse

/-! Closed history-conditioned graph-to-row transfer on the sparse range.
No comparison, denominator, or Gamma hypothesis remains at the endpoints. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

def SparseGammaTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 0 < A → ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T * (N : ℝ)^(-(1/2 : ℝ)) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
    RowGamma.Conclusion y q C p A N ∧
    (cond (GraphicalArray.law y.part y.edge)
      (GraphicalArray.historyRegular p y.part)).real
        {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ Real.exp (-(N : ℝ))

theorem uniform_gamma_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    SparseGammaTheorem.{u} θ T φ n := by
  obtain ⟨D,hD,Nd,hd⟩ := uniform_denominator_sparse n hθlo hθhi hT
  obtain ⟨C,hC,hshared⟩ := RowGamma.uniform_shared_constant_sparse (K := D+1) n
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


def SparseTransferTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
    (p : ℝ) < T * (N : ℝ)^(-(1/2 : ℝ)) →
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
    ∀ E : Set (RowArray.Ambient y.part),
    (CoarseKernel.Lambda p y).real {σ | σ.deg ∉ RowArray.values '' E} ≤
      Real.exp (-(N : ℝ)) + C *
        (cond (RowConcentration.conditionedLaw y q)
          (RowArray.exactTotals y.part y.edge)).real Eᶜ

/-- Literal real-density form; interior density is an output of the original
window, so this adds no hypothesis to the manuscript. -/
def SparseTransferRealTheorem (θ T φ : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
    ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
    ∃ hp : 0 < p ∧ p < 1,
    ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
    ∀ E : Set (RowArray.Ambient y.part),
    (CoarseKernel.Lambda ⟨p,hp.1.le,hp.2.le⟩ y).real {σ | σ.deg ∉ RowArray.values '' E} ≤
      Real.exp (-(N : ℝ)) + C *
        (cond (RowConcentration.conditionedLaw y q)
          (RowArray.exactTotals y.part y.edge)).real Eᶜ


theorem uniform_transfer_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    SparseTransferTheorem.{u} θ T φ n := by
  obtain ⟨CΓ,hCΓ,hg⟩ := uniform_gamma_sparse n hθlo hθhi hT hφ
  obtain ⟨Ng,hg⟩ := hg 1 zero_lt_one
  obtain ⟨Cc,_hCc,Nc,hc⟩ := EnumerationComparison.uniform_band_strong_comparison
    (η := 1/2) (CΓ := CΓ) n (by norm_num) hθlo.le hθhi hT
    (zero_lt_one.trans_le hCΓ)
  obtain ⟨Na,ha⟩ := AdmissibleFiber.uniform_admissible_unit_sparse n hθlo hθhi hT
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


theorem transfer_real_of_transfer_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (h : SparseTransferTheorem.{u} θ T φ n) : SparseTransferRealTheorem.{u} θ T φ n := by
  obtain ⟨C,hC,Nt,ht⟩ := h
  obtain ⟨Na,ha⟩ := AdmissibleFiber.uniform_admissible_sparse n hθlo hθhi hT
  refine ⟨C,hC,max Nt Na,?_⟩
  intro N hN V inst hcard p hlo hhi
  obtain ⟨hp,_⟩ := ha N (by omega) V hcard p hlo hhi
  exact ⟨hp,fun y q had E => ht N (by omega) V hcard ⟨p,hp.1.le,hp.2.le⟩
    hlo hhi y q had E⟩

/-- A positive-event version of B.3, with the original shared B.4 constant. -/
theorem gamma_lower_of_gamma_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (h : SparseGammaTheorem.{u} θ T φ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      1-Real.exp (-(N : ℝ)) ≤
        (cond (GraphicalArray.law y.part y.edge)
          (GraphicalArray.historyRegular p y.part)).real
          {d | RowArray.Gamma y.part y.edge C p d} := by
  obtain ⟨C,hC,hg⟩ := h
  obtain ⟨Ng,hg⟩ := hg 1 zero_lt_one
  obtain ⟨Na,ha⟩ := AdmissibleFiber.uniform_admissible_unit_sparse n hθlo hθhi hT
  refine ⟨C,hC,max Ng Na,?_⟩
  intro N hN V inst hcard p hlo hhi y q had
  have hlaws := (ha N (by omega) V hcard p hlo hhi y q φ had).2.2
  let := hlaws.graphical_probability
  exact RowGamma.good_mass_lower _ _ (Set.to_countable _).measurableSet
    (hg N (by omega) V hcard p hlo hhi y q had).2


/-- Closed real-density transfer on the uniform sparse range. -/
theorem uniform_transfer_real_sparse {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    SparseTransferRealTheorem.{u} θ T φ n :=
  transfer_real_of_transfer_sparse n hθlo hθhi hT
    (uniform_transfer_sparse n hθlo hθhi hT hφ)

end MajorityDynamics.GraphProcess.FiberTransference

