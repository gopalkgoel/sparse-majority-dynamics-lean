import MajorityDynamics.GraphProcess.FaithfulTrajectory.SparseStep
import MajorityDynamics.GraphProcess.FaithfulTrajectory.Parameters
import MajorityDynamics.GraphProcess.DayOne.SparseMain

noncomputable section
open MeasureTheory Set
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Idealized Idealized.LinearResponse Idealized.PerturbedEvolution CoarseKernel FineState
open Binomial.Approximation (SparseRange)

/-- Simultaneous faithfulness at every level whose preceding responses obey
the fixed cutoff. This statement does not choose a stopping exponent. -/
def UniformSparsePrefix (θ T U δ : ℝ) (ell D n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ p : Binomial.Probability, SparseRange θ T N p →
    ∀ a : Process.Data, Process.Specification N p D ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T → ∀ c : Fin N → Bool,
    (Finset.univ.filter fun v => c v = false).card = N/2 + ⌊τ*Real.sqrt N⌋₊ →
    SimpleGraph.binomialRandom (Fin N) (Binomial.closedProbability p)
      {G | ∃ j ≤ n, (∀ i < j, ResponseSmall θ N p i) ∧
        ¬Faithful N p U δ τ a (actualCoarse p G c j)} ≤ ENNReal.ofReal ε

theorem sparse_prefix_seed {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (ell D : ℕ) : UniformSparsePrefix θ T T ((1-θ)/4) ell D 0 := by
  intro ε hε
  obtain ⟨N₀,hN₀,hseed⟩ := DayOne.day_one_sparse θ T hθlo hθhi hT ε hε
  refine ⟨N₀,?_⟩
  intro N hN p hp a ha τ hτ hτT c hc
  have hs := (hseed N hN p hp a ha.initial τ hτ hτT (Fin N)
    (Fintype.card_fin N) c hc).1
  rw [← ofReal_measureReal (μ := SimpleGraph.binomialRandom (Fin N) (Binomial.closedProbability p))]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans (measureReal_mono ?_) hs
  rintro G ⟨j,hj,_,hbad⟩ hgood
  have hj0 : j = 0 := by omega
  subst j
  exact hbad (faithful_mono (hN₀.trans hN) p.property.1.le zero_le_one hT.le le_rfl hgood)

theorem extend_sparse_prefix {θ T U δ : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hTU : T ≤ U) (hδ : 0 < δ)
    (n ell D : ℕ) (hell : 1 ≤ ell) (hDlt : n+1 < D)
    (hprev : UniformSparsePrefix θ T U δ ell D n) :
    ∃ U' : ℝ, U ≤ U' ∧ ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      UniformSparsePrefix θ T U' δ' ell D (n+1) := by
  have hU : 1 < U := hT.trans_le hTU
  have hT0 : 0 < T := by linarith
  obtain ⟨U',hUU,δ',hδ',hδle,hstep⟩ :=
    uniform_faithful_step_sparse hθlo hθhi hU hδ n ell D hell hDlt
  refine ⟨U',hUU,δ',hδ',hδle,?_⟩
  intro ε hε
  have he : 0 < ε/3 := by positivity
  obtain ⟨N₁,h₁⟩ := hprev (ε/3) he
  obtain ⟨N₂,hN₂,h₂⟩ := hstep (ε/3) he
  refine ⟨max N₁ N₂,?_⟩
  intro N hN p hp a ha τ hτ hτT c hc
  have hN1 : 1 ≤ N := hN₂.trans (by omega)
  have hpU := Idealized.RowLimits.sparseRange_enlarge hT0 hTU hp
  have hτU : U⁻¹ ≤ τ := (inv_anti₀ hT0 hTU).trans hτ
  let μ := SimpleGraph.binomialRandom (Fin N) (Binomial.closedProbability p)
  let A : Set (SimpleGraph (Fin N)) := {G | ∃ j ≤ n,
    (∀ i < j, ResponseSmall θ N p i) ∧ ¬Faithful N p U δ τ a (actualCoarse p G c j)}
  let B : Set (SimpleGraph (Fin N)) := {G | (∀ i < n+1, ResponseSmall θ N p i) ∧
    ¬Faithful N p U' δ' τ a (actualCoarse p G c (n+1))}
  have hA : μ A ≤ ENNReal.ofReal (ε/3) := h₁ N (by omega) p hp a ha τ hτ hτT c hc
  have hB : μ B ≤ ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3) := by
    by_cases hsmall : ∀ i < n+1, ResponseSmall θ N p i
    · have hb := actual_one_step n (Binomial.closedProbability p) c p.property.1 p.property.2
        {y | Faithful N p U δ τ a y} {z | Faithful N p U' δ' τ a z}
        (ENNReal.ofReal (ε/3)) (fun y hy _ =>
          h₂ N (by omega) p hpU (hsmall n (by omega)) a ha τ hτU
            (hτT.trans hTU) (Fin N) (Fintype.card_fin N) y hy)
      have hpast : μ {G | ¬Faithful N p U δ τ a (actualCoarse p G c n)} ≤
          ENNReal.ofReal (ε/3) := by
        apply le_trans (measure_mono ?_) hA
        intro G hg
        exact ⟨n,le_rfl,fun i hi => hsmall i (by omega),hg⟩
      have hsub : B ⊆ {G | ¬Faithful N p U' δ' τ a (actualCoarse p G c (n+1))} :=
        fun _ h => h.2
      exact (measure_mono hsub).trans (hb.trans (add_le_add hpast le_rfl))
    · have hEmpty : B = ∅ := by
        ext G
        constructor
        · intro hg
          exact (hsmall hg.1).elim
        · intro hg
          exact hg.elim
      rw [hEmpty,measure_empty]
      exact bot_le
  have hsub : {G | ∃ j ≤ n+1, (∀ i < j, ResponseSmall θ N p i) ∧
      ¬Faithful N p U' δ' τ a (actualCoarse p G c j)} ⊆ A ∪ B := by
    rintro G ⟨j,hj,hsmall,hbad⟩
    by_cases hjlast : j = n+1
    · subst j
      exact Or.inr ⟨hsmall,hbad⟩
    · exact Or.inl ⟨j,by omega,hsmall,fun hgood =>
        hbad (faithful_mono hN1 p.property.1.le (by linarith) hUU hδle hgood)⟩
  calc
    _ ≤ μ (A ∪ B) := measure_mono hsub
    _ ≤ μ A + μ B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε/3)+(ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3)) := add_le_add hA hB
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add he.le he.le, ← ENNReal.ofReal_add he.le (by positivity)]
      congr 1
      ring

/-- A fixed finite number of rate losses still leaves a positive rate,
chosen before the density and before any stopping exponent. -/
theorem uniform_sparse_prefix {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (ell D : ℕ) (hell : 1 ≤ ell) (H : ℕ) (hHD : H < D) :
    ∃ U : ℝ, T ≤ U ∧ ∃ δ : ℝ, 0 < δ ∧ UniformSparsePrefix θ T U δ ell D H := by
  induction H with
  | zero => exact ⟨T,le_rfl,(1-θ)/4,by linarith,sparse_prefix_seed hθlo hθhi hT ell D⟩
  | succ H ih =>
    obtain ⟨U,hTU,δ,hδ,hprev⟩ := ih (by omega)
    obtain ⟨U',hUU,δ',hδ',_,hnext⟩ := extend_sparse_prefix hθlo hθhi hT hTU hδ
      H ell D hell hHD hprev
    exact ⟨U',hTU.trans hUU,δ',hδ',hnext⟩

end MajorityDynamics.GraphProcess.FaithfulTrajectory
