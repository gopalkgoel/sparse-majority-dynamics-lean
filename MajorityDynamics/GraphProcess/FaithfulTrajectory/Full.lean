import MajorityDynamics.GraphProcess.FaithfulTrajectory.Seed
import MajorityDynamics.GraphProcess.FaithfulTrajectory.CriticalStep

noncomputable section
open MeasureTheory Set
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution FineState CoarseKernel

/-- Joint 5.8 event: the whole faithful prefix, and the extra signed-gain day
when its last faithful day is critical. -/
def FullPrefix (θ T U δ ζ : ℝ) (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Paper.Coloring N),
      Paper.densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → Paper.initialBias N τ c →
      Paper.graphLaw N p {G |
        (∃ j ≤ n, ¬ Faithful N p U δ τ (referenceDataReal θ U N p) (rho p (actualState G c j))) ∨
        ((n:ℝ)+1 = 1/(1-θ) ∧ ¬CriticalGain N (ζ/2) (rho p (actualState G c (n+1))))}
        ≤ ENNReal.ofReal ε

/-- Both parts of the faithful-trajectory theorem, with exactly the edge-day
contract as its sole remaining intermediate input. -/
theorem full_prefix_of_critical (hcritical : CriticalDay.CriticalDayTheorem.{0})
    {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (n : ℕ) (hn : (n:ℝ) < 1/(1-θ)) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ ζ : ℝ, 0 < ζ ∧ FullPrefix θ T U δ ζ n := by
  obtain ⟨U,hTU,δ,hδ,hprefix⟩ := faithful_prefix hθlo hθhi hT n hn
  by_cases hk : (n:ℝ)+1 = 1/(1-θ)
  · obtain ⟨ξ,hξ,hgain⟩ := critical_from_uniform hcritical hθlo hθhi hT hTU hδ n hk hprefix.last
    refine ⟨U,hTU,δ,hδ,2*ξ,by positivity,?_⟩
    intro ε hε
    have he : 0 < ε/2 := by positivity
    obtain ⟨N₁,h₁⟩ := hprefix (ε/2) he
    obtain ⟨N₂,h₂⟩ := hgain (ε/2) he
    refine ⟨max N₁ N₂,?_⟩
    intro N hN p τ c hd hlo hhi hc
    have hA := h₁ N (by omega) p τ c hd hlo hhi hc
    have hB := h₂ N (by omega) p τ c hd hlo hhi hc
    have heq : 2*ξ/2 = ξ := by ring
    simp only [heq,hk,true_and]
    exact (measure_union_le _ _).trans ((add_le_add hA hB).trans_eq
      (by rw [← ENNReal.ofReal_add he.le he.le]; congr 1; ring))
  · refine ⟨U,hTU,δ,hδ,1,zero_lt_one,?_⟩
    simpa only [FullPrefix, UniformFaithfulPrefix, hk, false_and, or_false] using hprefix

/-- The complete finite horizon Kθ=ceil(1/(1−θ)), with the paper's initial
coloring at level zero and an extra level only in the integer case. -/
theorem trajectory_of_critical (hcritical : CriticalDay.CriticalDayTheorem.{0})
    {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ ζ : ℝ, 0 < ζ ∧
      FullPrefix θ T U δ ζ (⌈1/(1-θ)⌉₊-1) := by
  have hx : 0 < 1/(1-θ) := by positivity
  have hk : 1 ≤ ⌈1/(1-θ)⌉₊ := Nat.ceil_pos.mpr hx
  have hceil := Nat.ceil_lt_add_one hx.le
  have hn : ((⌈1/(1-θ)⌉₊-1:ℕ):ℝ) < 1/(1-θ) := by
    have hcast : (((⌈1/(1-θ)⌉₊-1)+1:ℕ):ℝ) = (⌈1/(1-θ)⌉₊:ℝ) :=
      congrArg (fun k : ℕ => (k:ℝ)) (Nat.sub_add_cancel hk)
    push_cast at hcast
    linarith
  exact full_prefix_of_critical hcritical hθlo hθhi hT _ hn

end MajorityDynamics.GraphProcess.FaithfulTrajectory
