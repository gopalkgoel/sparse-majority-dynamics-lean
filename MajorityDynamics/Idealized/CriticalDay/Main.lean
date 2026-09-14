import MajorityDynamics.Idealized.CriticalDay.AnalyticAssembly
import MajorityDynamics.Idealized.CriticalDay.Admissibility
import MajorityDynamics.Idealized.CriticalDay.TiltBound

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt PerturbedEvolution
universe u

/-- The full original-input Theorem 5.5. All nonlinear solving, row limits,
shift gain, affine support and local-admissibility inputs are discharged.
The gain is fixed before the faithfulness exponent. -/
theorem critical_day : CriticalDayTheorem.{u} := by
  intro θ hθlo hθhi n hk T hT
  let ell := processExponent θ T
  obtain ⟨ζ,hζ,hmain⟩ := analytic_assembly θ T hθlo hθhi hT n ell hk
  refine ⟨ζ,hζ,?_⟩
  intro δ hδ
  obtain ⟨R,δ₁,φ,hR,hδ₁,hφ,hφhi,hrows⟩ := hmain δ hδ
  obtain ⟨C,hC,htilt⟩ := row_tilt_bound n R hR.le
  obtain ⟨T₁,hTT₁,_,_,hadm⟩ := admissibility_spec θ T δ hθlo hθhi hT hδ n ell hk C hC.le
  refine ⟨T₁,hTT₁,δ₁,hδ₁,φ,hφ,hφhi,?_⟩
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧
      ∀ p : ℝ, T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∃ hp : 0 < p ∧ p < 1,
        Process.Specification N ⟨p,hp⟩ (responseHorizon θ) ell (referenceDataReal θ T N p) ∧
        ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
        ∀ (V : Type u) [Fintype V], Fintype.card V = N →
        ∀ y : Local.CoarseData V n,
          Faithful N p T δ τ (referenceDataReal θ T N p) y →
          Conclusion N ⟨p,hp⟩ y T₁ δ₁ φ ζ := by
    filter_upwards [hrows,hadm,htilt θ T hθlo hθhi hT,
      faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
      eventually_ge_atTop 1,eventually_ge_atTop (processThreshold θ T)]
      with N hrow had htil hgeo hN hNth
    refine ⟨hN,?_⟩
    intro p hlo hhi
    obtain ⟨hp,ha,_⟩ := referenceData_agree hθlo hθhi hT hNth hlo hhi
    have ha' : Process.Specification N ⟨p,hp⟩ (responseHorizon θ) ell (referenceDataReal θ T N p) := by
      rw [referenceDataReal_eq hp]
      exact ha
    refine ⟨hp,ha',?_⟩
    intro τ hτlo hτhi V inst hcard y hf
    obtain ⟨σ,hσ,hq,happrox,hprob,hsplit,hgain⟩ :=
      hrow ⟨p,hp⟩ ⟨hlo,hhi⟩ _ ha' τ hτlo hτhi y.integerSizes y.edge hf.2
    have hsize := (hgeo ⟨p,hp⟩ ⟨hlo,hhi⟩ _ ha' τ hτlo hτhi y.integerSizes y.edge hf.2).2.2.1
    let q : Local.Tilt n := fun s => RowLimits.rowTilt N ⟨p,hp⟩ (σ s)
    have hq' : Local.Solves y.sizes y.realEdges q := by simpa only [naturalSizes_coarse,realEdges_coarse] using hq
    have hsize' : ∀ s, 2*n+5 ≤ y.sizes s := by simpa only [naturalSizes_coarse] using hsize
    have hunique (q' : Local.Tilt n) (hq'' : Local.Solves y.sizes y.realEdges q') : q' = q :=
      Process.solving_tilt_unique y.sizes hsize' y.realEdges hq'' hq'
    refine ⟨⟨q,hq',hunique⟩,?_,?_,?_⟩
    · intro q' hq''
      rw [hunique q' hq'']
      apply had ⟨p,hp⟩ ⟨hlo,hhi⟩ _ ha' τ hτlo hτhi V y hcard hf.1 hf.2 q hq'
      · exact htil ⟨p,hp⟩ ⟨hlo,hhi⟩ σ hσ
      · rw [← naturalSizes_coarse y]
        exact hprob
      · rw [← naturalSizes_coarse y]
        exact hsplit
    · intro q' hq''
      rw [hunique q' hq'']
      exact happrox
    · intro q' hq''
      rw [hunique q' hq'']
      simpa only [naturalSizes_coarse] using hgain
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hev
  exact ⟨N₀,(hN₀ N₀ le_rfl).1,fun N hN => (hN₀ N hN).2⟩

end MajorityDynamics.Idealized.CriticalDay
