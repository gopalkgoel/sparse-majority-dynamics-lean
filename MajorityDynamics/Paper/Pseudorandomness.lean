import MajorityDynamics.Paper.RandomGraphDegree
import MajorityDynamics.Paper.PseudorandomnessAsymptotics
import MajorityDynamics.Literature.Jumbledness

/-!
# Discharging the pseudorandomness stage

This proves the exact `lem:cklt-jumbled` target from the two named cited inputs.
The degree calculation, union bounds, density specialization, uniform limits,
and absolute-constant quantifier order are all proved here or in the two
internal helper modules. No provisional paper axiom is imported.
-/

noncomputable section
open Set MeasureTheory Filter Topology

namespace MajorityDynamics.Paper

theorem minimumDegree_highProbability_of_chernoff
    (hChernoff : Literature.BernoulliLowerTail)
    (θ T : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : unitInterval,
      densityRange θ T N p → graphLaw N p {G | minimumDegree G p}ᶜ ≤ ENNReal.ofReal ε := by
  have hsmall := (degreeFailureEnvelope_tendsto θ T hθ hT).eventually
    (eventually_lt_nhds hε)
  have hregime := density_eventually_jumbled_regime θ T hθ0 hθ hT
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (20 : ℕ), hsmall, hregime] with N hN hsmallN hregimeN
  intro p hdensity
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact (minimumDegree_failure_bound_of_chernoff hChernoff N hN p
    (hregimeN p hdensity).1).trans
      (ENNReal.ofReal_le_ofReal ((degree_failure_le_envelope θ T p hN0 hdensity).trans hsmallN.le))

/-- The internal assembly, with the precise external propositions explicit. -/
theorem pseudorandomness_of_inputs (hJumbled : Literature.RandomGraphJumbledness)
    (hChernoff : Literature.BernoulliLowerTail) : Pseudorandomness := by
  obtain ⟨CJ, hCJ, hJ⟩ := hJumbled
  refine ⟨CJ, hCJ, ?_⟩
  intro θ T hθlower hθ hT ε hε
  have hθ0 : 0 < θ := by linarith
  have hT0 : 0 < T := by linarith
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨ND, hD⟩ := minimumDegree_highProbability_of_chernoff hChernoff θ T
    hθ0 hθ hT0 (ε / 2) hhalf
  obtain ⟨NJ, hJ⟩ := hJ (ε / 2) hhalf
  obtain ⟨NR, hR⟩ := eventually_atTop.mp (density_eventually_jumbled_regime θ T hθ0 hθ hT0)
  refine ⟨max ND (max NJ NR), ?_⟩
  intro N hN p hdensity
  have hND : ND ≤ N := (le_max_left _ _).trans hN
  have hNJ : NJ ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hNR : NR ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  have hregime := hR N hNR p hdensity
  have hdegree := hD N hND p hdensity
  have hjumbled := hJ N hNJ p hregime.2.1 hregime.2.2
  have he : (pseudorandomEvent p CJ)ᶜ = {G : Graph N | minimumDegree G p}ᶜ ∪
      {G | Jumbled G p (CJ * Real.sqrt ((p : ℝ) * N))}ᶜ := by
    classical
    ext G
    simp only [pseudorandomEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [he]
  refine (measure_union_le _ _).trans ((add_le_add hdegree hjumbled).trans ?_)
  rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

/-- `lem:cklt-jumbled`, conditional only on the accepted cited inequalities. -/
theorem pseudorandomness : Pseudorandomness :=
  pseudorandomness_of_inputs Literature.random_graph_jumbledness Literature.bernoulli_lower_tail

/-- The degree conclusion uses only the generic Chernoff input. -/
theorem minimumDegree_highProbability (θ T : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1)
    (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : unitInterval,
      densityRange θ T N p → graphLaw N p {G | minimumDegree G p}ᶜ ≤ ENNReal.ofReal ε :=
  minimumDegree_highProbability_of_chernoff Literature.bernoulli_lower_tail θ T hθ0 hθ hT ε hε

end MajorityDynamics.Paper
