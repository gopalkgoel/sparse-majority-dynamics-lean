import MajorityDynamics.GraphProcess.FiberTransference.Laws
import MajorityDynamics.GraphProcess.EnumerationComparison.Basic
import MajorityDynamics.GraphProcess.GoodArrayProbability.Main
import MajorityDynamics.GraphProcess.BlockCountProbability.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

def DenominatorTheorem (θ T : ℝ) (n : ℕ) : Prop :=
    ∃ D : ℝ, 0 < D ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.CoreAdmissible y q T φ p →
      Real.exp (-D*N) ≤ (graphArrayLaw p y).real
        (RowArray.exactTotals y.part y.edge ∩ GraphicalArray.historyRegular p y.part)

/-- Internal assembly interface: the only staged input is the full proved B.2
comparison at Gamma constant one. It is discharged in the public endpoint. -/
theorem denominator_of_comparison {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hcomparison : EnumerationComparison.StrongComparisonTheorem.{u} θ T 1 n) :
    ∃ D : ℝ, 0 < D ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.CoreAdmissible y q T φ p →
      Real.exp (-D*N) ≤ (graphArrayLaw p y).real
        (RowArray.exactTotals y.part y.edge ∩ GraphicalArray.historyRegular p y.part) := by
  obtain ⟨Cc,hCc,Nc,hc⟩ := hcomparison
  obtain ⟨Cg,hCg,Ng,hg⟩ := GoodArrayProbability.uniform_probability n hθlo hθhi hT
  obtain ⟨Cb,hCb,Nb,hb⟩ := BlockCountProbability.count_event_lower n hθlo hθhi hT
  obtain ⟨Ni,hi⟩ := GoodArrays.uniform_inclusion n hθlo hθhi hT
  obtain ⟨Na,ha⟩ := AdmissibleFiber.uniform_admissible_unit n hθlo hθhi hT
  refine ⟨Cb+Cg+Cc,by positivity,max 1 (max Nc (max Ng (max Nb (max Ni Na)))),?_⟩
  intro N hN V inst hcard p hlo hhi y q φ had
  let := GraphicalArray.law_probability y
  have hsizes : ∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ) := fun s => by
    simpa only [← hcard, div_eq_mul_inv, mul_comm] using had.sizes s
  have hcounts : ∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N) := fun s t => by
    simpa only [← hcard, Local.CoarseData.realEdges, Local.edgeScale,
      mul_div_assoc,mul_assoc] using had.edge_scale s t
  have htilt : ∀ s t, |(q s t : ℝ)-(p : ℝ)| ≤ T*(p : ℝ)/Real.sqrt ((p : ℝ)*N) :=
    fun s t => by simpa only [← hcard, mul_div_assoc] using had.tilt s t
  have hin := hi N (by omega) V hcard p hlo hhi y hsizes hcounts had.separation
  have hgood := (hg N (by omega) V hcard p hlo hhi y q hsizes hcounts htilt).2.1
  have hcomp := hc N (by omega) V hcard p hlo hhi y hsizes hcounts q
    (GoodArrays.E0 y T p) (fun d hd => ⟨(hin d hd).1,(hin d hd).2.2.1,(hin d hd).2.2.2.1⟩)
  have hblock := hb N (by omega) V hcard p hlo hhi y hsizes hcounts
  have hp := (ha N (by omega) V hcard p hlo hhi y q φ had).1
  let μ := graphArrayLaw p y
  let M := RowArray.exactTotals y.part y.edge
  let H := GraphicalArray.historyRegular p y.part
  have hμM : 0 < μ.real M := (Real.exp_pos _).trans_le (by simpa [μ,M,count_mass] using hblock)
  have hl : Real.exp (-Cc) * Real.exp (-Cg*N) ≤
      (GraphicalArray.law y.part y.edge).real H := by
    apply (mul_le_mul_of_nonneg_left hgood (Real.exp_pos _).le).trans
    apply hcomp.1.trans
    exact measureReal_mono (fun d hd => ⟨(hin d hd).2.1,(hin d hd).2.2.1⟩)
      (measure_ne_top _ _)
  rw [graphical_as_cond p y hp.1 hp.2,
    RowExactTotals.conditioned_real_eq_div _ _ _ (Set.to_countable _).measurableSet] at hl
  have hl' : (Real.exp (-Cc) * Real.exp (-Cg*N))*μ.real M ≤ μ.real (M ∩ H) :=
    (le_div_iff₀ hμM).mp hl
  have hb' : Real.exp (-Cb*N) ≤ μ.real M := by simpa [μ,M,count_mass] using hblock
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    Real.exp (-(Cb+Cg+Cc)*N) ≤ Real.exp (-Cc-Cg*N-Cb*N) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (Real.exp (-Cc)*Real.exp (-Cg*N))*Real.exp (-Cb*N) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    _ ≤ (Real.exp (-Cc)*Real.exp (-Cg*N))*μ.real M :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ ≤ _ := hl'

end MajorityDynamics.GraphProcess.FiberTransference
