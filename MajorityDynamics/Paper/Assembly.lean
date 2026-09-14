import MajorityDynamics.Paper.Pseudorandomness
import MajorityDynamics.Paper.CleanupAsymptotics

/-!
# The main theorem from an explicit proof frontier

The probability bookkeeping is proved here: expansion and pseudorandomness each
fail with probability at most ε/2, and deterministic cleanup succeeds on their
intersection. Cleanup is now proved. `main_of_expansion_and_pseudorandomness`
exposes the two remaining stages as hypotheses. No pending axioms are imported
by this module; a clean axiom list for an implication does not establish its hypotheses.
-/

open MeasureTheory

namespace MajorityDynamics.Paper

/-- The original three-stage assembly, kept as a reusable conditional reduction. -/
theorem main_of_inputs (expansion : ExpansionPhase) (pseudo : Pseudorandomness)
    (cleanup : DeterministicCleanup) : MainTheorem := by
  intro θ T hθlow hθhigh hT ε hε
  obtain ⟨CJ, hCJ, hpseudo⟩ := pseudo
  obtain ⟨nE, hE⟩ := expansion θ T hθlow hθhigh hT (ε / 2) (half_pos hε)
  obtain ⟨nP, hP⟩ := hpseudo θ T hθlow hθhigh hT (ε / 2) (half_pos hε)
  obtain ⟨nD, hD⟩ := cleanup θ T CJ hθlow hθhigh hT hCJ
  refine ⟨max nE (max nP nD), ?_⟩
  intro N hN p τ c hdensity hτlow hτhigh hinitial
  have hnE : nE ≤ N := (le_max_left _ _).trans hN
  have hnP : nP ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hnD : nD ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hsubset : (successEvent θ c)ᶜ ⊆
      (expansionEvent θ p c)ᶜ ∪ (pseudorandomEvent p CJ)ᶜ := by
    intro G hfail
    by_cases hexp : G ∈ expansionEvent θ p c
    · by_cases hps : G ∈ pseudorandomEvent p CJ
      · exact False.elim (hfail (hD N hnD p G c hdensity hps hexp))
      · exact Or.inr hps
    · exact Or.inl hexp
  calc
    graphLaw N p (successEvent θ c)ᶜ ≤
        graphLaw N p ((expansionEvent θ p c)ᶜ ∪ (pseudorandomEvent p CJ)ᶜ) :=
      measure_mono hsubset
    _ ≤ graphLaw N p (expansionEvent θ p c)ᶜ +
        graphLaw N p (pseudorandomEvent p CJ)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hE N hnE p τ c hdensity hτlow hτhigh hinitial)
        (hP N hnP p hdensity)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (le_of_lt (half_pos hε)) (le_of_lt (half_pos hε))]
      congr 1
      exact add_halves ε

/-- The current conditional main theorem: cleanup has been discharged. Expansion
still contains internal paper arguments, not only external literature inputs. -/
theorem main_of_expansion_and_pseudorandomness
    (expansion : ExpansionPhase) (pseudo : Pseudorandomness) : MainTheorem :=
  main_of_inputs expansion pseudo deterministic_cleanup

/-- Only expansion remains internal; pseudorandomness uses the named literature inputs. -/
theorem main_of_expansion (expansion : ExpansionPhase) : MainTheorem :=
  main_of_expansion_and_pseudorandomness expansion pseudorandomness

end MajorityDynamics.Paper
