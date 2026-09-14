import MajorityDynamics.GraphProcess.FaithfulTrajectory.Induction

noncomputable section
open MeasureTheory Set
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution FineState CoarseKernel

/-- The joint faithful-trajectory event through universal level n. -/
def UniformFaithfulPrefix (θ T U δ : ℝ) (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (p : unitInterval) (τ : ℝ) (c : Paper.Coloring N),
      Paper.densityRange θ T N p → T⁻¹ ≤ τ → τ ≤ T → Paper.initialBias N τ c →
      Paper.graphLaw N p {G | ∃ j ≤ n, ¬ Faithful N p U δ τ (referenceDataReal θ U N p)
        (rho p (actualState G c j))} ≤ ENNReal.ofReal ε

theorem UniformFaithfulPrefix.last {θ T U δ : ℝ} {n : ℕ}
    (h : UniformFaithfulPrefix θ T U δ n) : UniformFaithful θ T U δ n := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := h ε hε
  refine ⟨N₀,?_⟩
  intro N hN p τ c hd hlo hhi hc
  apply le_trans (measure_mono ?_) (h₀ N hN p τ c hd hlo hhi hc)
  exact fun _ hG => ⟨n,le_rfl,hG⟩

/-- Monotonicity is applied to all earlier levels using the exact common
reference prefix, before the finite union with the new day's failure. -/
theorem extend_uniform_prefix {θ T U δ : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hTU : T ≤ U) (hδ : 0 < δ) (n : ℕ)
    (hk : (n:ℝ)+1 < 1/(1-θ)) (hprev : UniformFaithfulPrefix θ T U δ n) :
    ∃ U' : ℝ, U ≤ U' ∧ ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      UniformFaithfulPrefix θ T U' δ' (n+1) := by
  obtain ⟨U',hUU,δ',hδ',hδle,hnext⟩ :=
    extend_uniform_faithful hθlo hθhi hT hTU hδ n hk hprev.last
  have hTU' := hTU.trans hUU
  have hU := hT.trans_le hTU
  have hU' := hT.trans_le hTU'
  have hT0 : 0 < T := by linarith
  refine ⟨U',hUU,δ',hδ',hδle,?_⟩
  intro ε hε
  have he : 0 < ε/2 := by positivity
  obtain ⟨N₁,h₁⟩ := hprev (ε/2) he
  obtain ⟨N₂,h₂⟩ := hnext (ε/2) he
  refine ⟨max N₁ (max N₂ (max 1 (max (processThreshold θ U) (processThreshold θ U')))),?_⟩
  intro N hN p τ c hd hlo hhi hc
  have hdU := density_widen hT0 hTU hd.1 hd.2
  have hdU' := density_widen hT0 hTU' hd.1 hd.2
  have href := references_agree hθlo hθhi hU hU' (by omega) (by omega)
    hdU.1 hdU.2 hdU'.1 hdU'.2
  have hmono (G : Paper.Graph N) (j : ℕ) (hj : j ≤ n)
      (hf : Faithful N p U δ τ (referenceDataReal θ U N p) (rho p (actualState G c j))) :
      Faithful N p U' δ' τ (referenceDataReal θ U' N p) (rho p (actualState G c j)) := by
    have hf' := faithful_mono (by omega) p.2.1 (by linarith) hUU hδle hf
    exact (FaithfulStep.faithful_reference_iff (href.1 j
      (by have h := level_succ_lt_horizon hk; omega)) _).mp hf'
  let A : Set (Paper.Graph N) := {G | ∃ j ≤ n, ¬ Faithful N p U δ τ
    (referenceDataReal θ U N p) (rho p (actualState G c j))}
  let B : Set (Paper.Graph N) := {G | ¬ Faithful N p U' δ' τ
    (referenceDataReal θ U' N p) (rho p (actualState G c (n+1)))}
  have hsub : {G | ∃ j ≤ n+1, ¬ Faithful N p U' δ' τ
      (referenceDataReal θ U' N p) (rho p (actualState G c j))} ⊆ A ∪ B := by
    rintro G ⟨j,hj,hf⟩
    by_cases heq : j = n+1
    · subst j
      exact Or.inr hf
    · have hj' : j ≤ n := by omega
      exact Or.inl ⟨j,hj',fun h => hf (hmono G j hj' h)⟩
  calc
    _ ≤ Paper.graphLaw N p (A ∪ B) := measure_mono hsub
    _ ≤ Paper.graphLaw N p A + Paper.graphLaw N p B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) :=
      add_le_add (h₁ N (by omega) p τ c hd hlo hhi hc) (h₂ N (by omega) p τ c hd hlo hhi hc)
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add he.le he.le]; congr 1; ring

theorem finite_prefix_of_seed {θ T δ₀ : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ₀ : 0 < δ₀) (hseed : UniformFaithful θ T T δ₀ 0)
    (n : ℕ) (hn : (n:ℝ) < 1/(1-θ)) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ UniformFaithfulPrefix θ T U δ n := by
  induction n with
  | zero =>
    refine ⟨T,le_rfl,δ₀,hδ₀,?_⟩
    simpa only [UniformFaithfulPrefix, UniformFaithful, Nat.le_zero, exists_eq_left] using hseed
  | succ n ih =>
    obtain ⟨U,hTU,δ,hδ,hprev⟩ := ih (by push_cast at hn; linarith)
    obtain ⟨U',hUU,δ',hδ',_,hnext⟩ := extend_uniform_prefix hθlo hθhi hT hTU hδ n
      (by simpa only [Nat.cast_add,Nat.cast_one] using hn) hprev
    exact ⟨U',hTU.trans hUU,δ',hδ',hnext⟩

end MajorityDynamics.GraphProcess.FaithfulTrajectory
