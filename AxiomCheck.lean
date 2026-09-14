import MajorityDynamics.Paper.Expansion.Checks
import MajorityDynamics.GraphProcess.FaithfulTrajectory.Checks
import MajorityDynamics.GraphProcess.DayOne.ProbabilityChecks
import MajorityDynamics.GraphProcess.DayOne.Checks
import MajorityDynamics.GraphProcess.FaithfulStep.Checks
import MajorityDynamics.Idealized.CriticalDay.Checks
import MajorityDynamics.GraphProcess.LocalTheorem.Checks
import MajorityDynamics.GraphProcess.KernelSplitting.Checks
import MajorityDynamics.GraphProcess.FiberTransference.Checks
import MajorityDynamics.GraphProcess.EnumerationComparison.Checks
import MajorityDynamics.Probability.NeighborhoodTail.Checks
import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Checks
import MajorityDynamics.Probability.NeighborhoodBulk.Checks
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks
import MajorityDynamics.Probability.HypergeometricTiltTail.Checks
import MajorityDynamics.GraphProcess.KernelInputs.Checks
import MajorityDynamics.GraphProcess.LocalTransition.Checks
import MajorityDynamics.GraphProcess.AdmissibleFiber.Checks
import MajorityDynamics.GraphProcess.RowGamma.Checks
import MajorityDynamics.GraphProcess.GammaNumerator.Checks
import MajorityDynamics.GraphProcess.RowExactTotals.Checks
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Checks
import MajorityDynamics.Probability.ConditionedBinomialFourier.Checks
import MajorityDynamics.GraphProcess.RowConcentration.Checks
import MajorityDynamics.GraphProcess.BlockCountProbability.Checks
import MajorityDynamics.GraphProcess.GoodArrayProbability.Checks
import MajorityDynamics.GraphProcess.GoodArrays.Checks
import MajorityDynamics.GraphProcess.EnumerationBounds.Checks
import MajorityDynamics.GraphProcess.BlockPairLaws.Checks
import MajorityDynamics.GraphProcess.AutomaticGraphicality.Checks
import MajorityDynamics.GraphProcess.NonLumpability.Checks
import MajorityDynamics.GraphProcess.GraphicalArray.Checks
import MajorityDynamics.GraphProcess.CoarseKernel.Checks
import MajorityDynamics.GraphProcess.RowArray.Checks
import MajorityDynamics.GraphProcess.BlockDecomposition.Checks
import MajorityDynamics.GraphProcess.FineState.Checks
import MajorityDynamics.GraphProcess.History.Checks
import MajorityDynamics.Idealized.PerturbedEvolution.Checks
import MajorityDynamics.Idealized.PerturbedTilt.Checks
import MajorityDynamics.Probability.RandomOpinionsReduction.Checks
import MajorityDynamics.Probability.FixedDegreeSampling.Checks
import MajorityDynamics.Combinatorics.SufficientGraphicality.Checks
import MajorityDynamics
import MajorityDynamics.Idealized.LinearResponse.Checks
import MajorityDynamics.Probability.DegreeConcentration.Checks
import MajorityDynamics.Combinatorics.ZeroSumCounting.Checks
import MajorityDynamics.Probability.FixedSizeExponential.Checks
import MajorityDynamics.Combinatorics.DegreeRatios.Checks
import MajorityDynamics.Probability.UnconditionedExactTotals.Checks
import MajorityDynamics.GraphProcess.FineKernel.Checks
import MajorityDynamics.Probability.ConditionedBinomialBox.Checks

/-! Reproducible dependency checks for the completed manuscript analysis.
`#guard_msgs` makes a changed axiom list a build failure, including indirect
use of `sorryAx`, an unlisted mathematical axiom, or `native_decide`.
The D.1/D.2 targets below remain foundational-only. D.3 is now foundational-only
as well, using the attributed checked Brouwer proof in the literature tree.
-/

/-- info: 'MajorityDynamics.strong_bijection_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.strong_bijection_lipschitz

/-! The exact closed Appendix D.2 and cone statements are checked as well as
their transitive axioms. Proving a helper under unresolved analytic hypotheses
cannot satisfy these target checks. The separate A.5 specialization has its
own audit and does not depend on the log-partition calculus. -/

example : MajorityDynamics.Analysis.ConditionalGaussian.CoreTheorem :=
  MajorityDynamics.Analysis.ConditionalGaussian.core

example : MajorityDynamics.Analysis.ConditionalGaussian.ConeTheorem :=
  MajorityDynamics.Analysis.ConditionalGaussian.cone_bijection

example : MajorityDynamics.Analysis.ConditionalGaussian.CoreTheorem ∧
    MajorityDynamics.Analysis.ConditionalGaussian.ConeTheorem :=
  MajorityDynamics.Analysis.ConditionalGaussian.main

/-- info: 'MajorityDynamics.Analysis.ConditionalGaussian.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.ConditionalGaussian.core

/-- info: 'MajorityDynamics.Analysis.ConditionalGaussian.cone_bijection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.ConditionalGaussian.cone_bijection

/-- info: 'MajorityDynamics.Analysis.ConditionalGaussian.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.ConditionalGaussian.main

/-- info: 'MajorityDynamics.Analysis.ConditionalGaussian.open_conditioning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.ConditionalGaussian.open_conditioning

/-! D.3: exact closed target types and the complete accepted external frontier.
The generic reduction has no external axiom dependency; the closed targets
instantiate it with the separately stated, cited and proved Brouwer theorem. -/

example : MajorityDynamics.Literature.BrouwerClosedBall →
    MajorityDynamics.Analysis.Perturbation.PerturbationTheorem :=
  MajorityDynamics.Analysis.Perturbation.perturbation_of_brouwer

example : MajorityDynamics.Analysis.Perturbation.PerturbationTheorem :=
  MajorityDynamics.Analysis.Perturbation.perturbation

example : MajorityDynamics.Analysis.Perturbation.ConePerturbationTheorem :=
  MajorityDynamics.Analysis.Perturbation.cone_perturbation

example : MajorityDynamics.Analysis.Perturbation.GaussianConePerturbationTheorem :=
  MajorityDynamics.Analysis.Perturbation.gaussian_cone_perturbation

example : MajorityDynamics.Analysis.Perturbation.PerturbationTheorem ∧
    MajorityDynamics.Analysis.Perturbation.ConePerturbationTheorem :=
  MajorityDynamics.Analysis.Perturbation.main

/-- info: 'MajorityDynamics.Analysis.Perturbation.perturbation_of_brouwer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.perturbation_of_brouwer

/-- info: 'MajorityDynamics.Analysis.Perturbation.perturbation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.perturbation

/-- info: 'MajorityDynamics.Analysis.Perturbation.cone_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.cone_perturbation

/-- info: 'MajorityDynamics.Analysis.Perturbation.gaussian_cone_perturbation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.gaussian_cone_perturbation

/-- info: 'MajorityDynamics.Analysis.Perturbation.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.main

/-! Statement-fidelity bridges: the exact attained radius, empty-set convention,
and zero-row coordinate cube are proved without the Brouwer input. -/

/-- info: 'MajorityDynamics.Analysis.Perturbation.inverseRadius_eq_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.inverseRadius_eq_max

/-- info: 'MajorityDynamics.Analysis.Perturbation.inverseRadius_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.inverseRadius_empty

/-- info: 'MajorityDynamics.Analysis.Perturbation.compactCone_zero_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.Perturbation.compactCone_zero_rows

/-! §4: actual Gaussian recursion, well-definedness, bit-flip symmetry, and
centered conditional covariance. These remain foundational-only despite the
root also importing the separately audited D.3 Brouwer specialization. -/

example : MajorityDynamics.Universal.UniversalRecursionTheorem :=
  MajorityDynamics.Universal.main

example : ∀ n, (MajorityDynamics.Universal.universal n).Valid :=
  MajorityDynamics.Universal.universal_valid

example : ∀ n, (MajorityDynamics.Universal.universal n).FlipInvariant :=
  MajorityDynamics.Universal.universal_flipInvariant

open MajorityDynamics.Universal in
example : ∀ (n : ℕ) (s : History (n + 1)) (ν : History (n + 1) → ℝ),
    (∀ t, 0 < ν t) →
      ∃ f : MajorityDynamics.StrongBijection (historyCone s), f.toFun = meanMap s ν :=
  @conditionalMean_bijection

open MajorityDynamics.Universal in
example : ∀ (n : ℕ) (s : History (n + 1)), (conditionalCovariance n s).PosDef :=
  universal_conditional_covariance_posDef

open MajorityDynamics.Universal in
example : ∀ (n : ℕ) (s : History (n + 1)) (b : Bool),
    ν (n + 1) (append s b) = ν n s * (historyLaw n s).real (childEvent s b) :=
  ν_recursion_events

open MajorityDynamics.Universal MeasureTheory in
example : ∀ (n : ℕ) (s t : History (n + 1)) (b c : Bool),
    μ (n + 1) (append s b) (append t c) =
      (∫ x, x t ∂childLaw n s b) / ν n t +
      (∫ x, x s ∂childLaw n t c) / ν n s - μ n s t :=
  μ_recursion_events

/-- info: 'MajorityDynamics.Universal.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.main

/-- info: 'MajorityDynamics.Universal.conditionalMean_bijection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.conditionalMean_bijection

/-- info: 'MajorityDynamics.Universal.universal_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.universal_valid

/-- info: 'MajorityDynamics.Universal.universal_flipInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.universal_flipInvariant

/-- info: 'MajorityDynamics.Universal.universal_conditional_covariance_posDef' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.universal_conditional_covariance_posDef

/-- info: 'MajorityDynamics.Universal.historyEvent_ae_eq_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.historyEvent_ae_eq_cone

/-- info: 'MajorityDynamics.Universal.childEvent_ae_eq_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.childEvent_ae_eq_cone

/-- info: 'MajorityDynamics.Universal.rowLaw_independent_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.rowLaw_independent_coordinates

/-- info: 'MajorityDynamics.Universal.ν_recursion_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.ν_recursion_events

/-- info: 'MajorityDynamics.Universal.μ_recursion_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.μ_recursion_events

/-- info: 'MajorityDynamics.Universal.conditionalCovariance_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.conditionalCovariance_entry

/-- info: 'MajorityDynamics.Universal.rowLaw_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.rowLaw_coordinate

/-- info: 'MajorityDynamics.Universal.arrayLaw_independent_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.arrayLaw_independent_rows

/-- info: 'MajorityDynamics.Universal.arrayLaw_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.arrayLaw_coordinate

/-! Complete §4: these exact closed types reject a proof that merely assumes
the Gaussian split result, coherence, or actual-recursion properties. Every
internal Gaussian and algebraic input is supplied by the final declarations. -/

example : MajorityDynamics.Analysis.GaussianSplit.StandardSplitTheorem :=
  MajorityDynamics.Analysis.GaussianSplit.standard_positive_split

example : MajorityDynamics.Analysis.GaussianSplit.AffineSplitTheorem :=
  MajorityDynamics.Analysis.GaussianSplit.affine_positive_split

example : MajorityDynamics.Universal.Section4Theorem :=
  MajorityDynamics.Universal.section4

example : MajorityDynamics.Universal.SignIdentitiesTheorem :=
  MajorityDynamics.Universal.sign_identities

open MajorityDynamics.Universal in
example : ∀ n (s : History (n + 1)),
    0 < ε (n + 1) (append s false) ∧ ε (n + 1) (append s true) < 0 :=
  coherence

open MajorityDynamics.Universal in
example : ∀ n (s : History (n + 1)),
    ∃! b : History (n + 1) → ℝ,
      ∀ t, ∑ u, b u * conditionalCovariance n s u t = ε n t :=
  β_existsUnique

open MajorityDynamics.Universal in
example : ∀ n, UniversalNondegeneracy n (φStar n) (ζStar n) :=
  universal_nondegeneracy

open MajorityDynamics.Universal in
example : ∀ n, ∃ φ ζ, UniversalNondegeneracy n φ ζ :=
  universal_nondegeneracy_exists

/-- info: 'MajorityDynamics.Analysis.GaussianSplit.standard_positive_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.GaussianSplit.standard_positive_split

/-- info: 'MajorityDynamics.Analysis.GaussianSplit.affine_positive_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.GaussianSplit.affine_positive_split

/-- info: 'MajorityDynamics.Universal.section4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.section4

/-- info: 'MajorityDynamics.Universal.coherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.coherence

/-- info: 'MajorityDynamics.Universal.sign_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.sign_identities

/-- info: 'MajorityDynamics.Universal.universal_nondegeneracy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.universal_nondegeneracy

/-- info: 'MajorityDynamics.Universal.universal_nondegeneracy_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.universal_nondegeneracy_exists

/-- info: 'MajorityDynamics.Universal.β_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.β_existsUnique

/-- info: 'MajorityDynamics.Universal.B_covariance_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.B_covariance_coordinate

/-- info: 'MajorityDynamics.Universal.ε_recursion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.ε_recursion

/-- info: 'MajorityDynamics.Universal.ε_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.ε_flip

/-- info: 'MajorityDynamics.Universal.β_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.β_flip

/-- info: 'MajorityDynamics.Universal.ε_lead_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.ε_lead_positive

/-- info: 'MajorityDynamics.Universal.arrayLaw_all_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.arrayLaw_all_coordinates

/-- info: 'MajorityDynamics.Universal.dayArrayLaw_independent_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Universal.dayArrayLaw_independent_coordinates

/-! Package 1 for §5 / Appendix E: actual binomial laws, the exact local
    template, logit tilts, and the closed E.1 theorem are foundational-only. -/

example : MajorityDynamics.Binomial.TiltUniquenessTheorem :=
  MajorityDynamics.Binomial.tilt_uniqueness

/-- info: 'MajorityDynamics.Binomial.tilt_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.tilt_uniqueness

/-- info: 'MajorityDynamics.Binomial.conditionalMean_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.conditionalMean_injective

/-- info: 'MajorityDynamics.Binomial.independent_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.independent_coordinates

/-- info: 'MajorityDynamics.Binomial.coordinate_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.coordinate_law

/-- info: 'MajorityDynamics.Binomial.conditionalMean_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.conditionalMean_eq_integral

/-- info: 'MajorityDynamics.Binomial.conditionalLaw_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.conditionalLaw_filter

/-- info: 'MajorityDynamics.Local.rowCondition_eq_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Local.rowCondition_eq_actual

/-- info: 'MajorityDynamics.Local.solving_tilt_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Local.solving_tilt_unique

/-- info: 'MajorityDynamics.Local.templateSizes_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Local.templateSizes_children

/-- info: 'MajorityDynamics.Local.templateHalfEdges_children_of_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Local.templateHalfEdges_children_of_solves

/-- info: 'MajorityDynamics.Local.templateEdges_children_of_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Local.templateEdges_children_of_solves

/-- info: 'MajorityDynamics.Local.templateEdges_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Local.templateEdges_symmetric

/-- info: 'MajorityDynamics.Idealized.logitTilt_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Idealized.logitTilt_formula

/-- info: 'MajorityDynamics.Idealized.logOdds_logitTilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Idealized.logOdds_logitTilt

/-- info: 'MajorityDynamics.Analysis.FiniteTilt.parameter_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.FiniteTilt.parameter_eq_zero


/-! A.2 components only: the full AppendixA2Theorem remains unproved. -/

/-- info: 'MajorityDynamics.Analysis.FiniteTiltEstimate.quotient_remainder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.FiniteTiltEstimate.quotient_remainder

/-- info: 'MajorityDynamics.Analysis.FiniteTiltEstimate.exponential_remainder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.FiniteTiltEstimate.exponential_remainder

/-- info: 'MajorityDynamics.Analysis.FiniteTiltEstimate.relative_weight_remainder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.FiniteTiltEstimate.relative_weight_remainder

/-- info: 'MajorityDynamics.Binomial.expectation_reweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.expectation_reweight

/-- info: 'MajorityDynamics.Binomial.finite_tilt_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.finite_tilt_expansion

/-- info: 'MajorityDynamics.Binomial.Approximation.log_stirling_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.Approximation.log_stirling_error

/-- info: 'MajorityDynamics.Binomial.Approximation.log_factorial_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.Approximation.log_factorial_error

/-- info: 'MajorityDynamics.Binomial.Approximation.log_pointMass_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.Approximation.log_pointMass_error

/-- info: 'MajorityDynamics.Binomial.Approximation.pointMass_relative_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Binomial.Approximation.pointMass_relative_error

/-- info: 'MajorityDynamics.Analysis.log_one_add_linear_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.log_one_add_linear_error

/-- info: 'MajorityDynamics.Analysis.log_one_add_quadratic_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Analysis.log_one_add_quadratic_error

example {m k : ℕ} (hk : 0 < k) (hkm : k < m)
    (q : MajorityDynamics.Binomial.Probability) :
    |Real.log (MajorityDynamics.Binomial.Approximation.pointMass m k q) -
      MajorityDynamics.Binomial.Approximation.binomialLogMain m k q| ≤
        1 / (12 * m) + 1 / (12 * k) + 1 / (12 * (m - k : ℕ)) :=
  MajorityDynamics.Binomial.Approximation.log_pointMass_error hk hkm q

example {ι : Type*} [Fintype ι] (η : ι → ℕ)
    (q₀ q₁ : ι → MajorityDynamics.Binomial.Probability) (c : ι → ℝ)
    (S : Finset (MajorityDynamics.Binomial.Box η)) (hS : S.Nonempty)
    (f : MajorityDynamics.Binomial.Box η → ℝ) (H b : ℝ)
    (hH : 0 ≤ H) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 4)
    (hf : ∀ a ∈ S, |f a| ≤ H)
    (hz : ∀ a ∈ S, |MajorityDynamics.Binomial.centeredLogTilt η q₀ q₁ c a| ≤ b) :
    |MajorityDynamics.Binomial.expectation η q₁ S f -
      (MajorityDynamics.Binomial.expectation η q₀ S f +
        MajorityDynamics.Binomial.expectation η q₀ S
          (fun a => MajorityDynamics.Binomial.centeredLogTilt η q₀ q₁ c a * f a) -
        MajorityDynamics.Binomial.expectation η q₀ S
          (MajorityDynamics.Binomial.centeredLogTilt η q₀ q₁ c) *
        MajorityDynamics.Binomial.expectation η q₀ S f)| ≤ 12 * H * b ^ 2 :=
  MajorityDynamics.Binomial.finite_tilt_expansion η q₀ q₁ c S hS f H b hH hb hbsmall hf hz

/-! Closed A.2 point theorem and further truncation/comparison components. -/

example : MajorityDynamics.Binomial.Approximation.PointEstimateTheorem :=
  MajorityDynamics.Binomial.Approximation.point_estimate

/-- info: 'MajorityDynamics.Binomial.Approximation.point_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.point_estimate

/-- info: 'MajorityDynamics.Binomial.Approximation.first_window_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.first_window_estimate

/-- info: 'MajorityDynamics.Binomial.Approximation.gaussian_window_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.gaussian_window_estimate

/-- info: 'MajorityDynamics.Binomial.Approximation.changing_trials_log_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.changing_trials_log_error

/-- info: 'MajorityDynamics.Analysis.log_tail_eventually_le_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.log_tail_eventually_le_power

/-- info: 'MajorityDynamics.Binomial.two_sided_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.two_sided_tail

/-- info: 'MajorityDynamics.Binomial.centered_tail_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.centered_tail_scaled


/-! Shared-window expansion and actual-law transfer: no new internal assumptions. -/

/-- info: 'MajorityDynamics.Analysis.FiniteTiltEstimate.normalized_log_tilt_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.FiniteTiltEstimate.normalized_log_tilt_expansion

/-- info: 'MajorityDynamics.Analysis.covariance_expansion_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.covariance_expansion_transfer

/-- info: 'MajorityDynamics.Binomial.integral_truncation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.integral_truncation_le

/-- info: 'MajorityDynamics.Binomial.Approximation.product_changing_trials_log_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.product_changing_trials_log_error

/-- info: 'MajorityDynamics.Binomial.Approximation.window_tilt_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.window_tilt_expansion

/-- info: 'MajorityDynamics.Binomial.Approximation.expansion_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.expansion_transfer

/-- info: 'MajorityDynamics.Binomial.rectangle_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.rectangle_mass_pos

/-- info: 'MajorityDynamics.Binomial.Approximation.tilted_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.tilted_window

/-- info: 'MajorityDynamics.Binomial.Approximation.trial_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.trial_geometry

/-- info: 'MajorityDynamics.Binomial.Approximation.likelihoodErrorBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.likelihoodErrorBound_le

/-- info: 'MajorityDynamics.Binomial.Approximation.rectangle_tail_of_trial_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.rectangle_tail_of_trial_geometry

example : MajorityDynamics.Binomial.Approximation.TiltedExpansionTheorem :=
  MajorityDynamics.Binomial.Approximation.tilted_expansion

/-- info: 'MajorityDynamics.Binomial.Approximation.tilted_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.tilted_expansion

/-! Gaussian comparison components and closed A.2 endpoints. -/

/-- info: 'MajorityDynamics.Binomial.Approximation.finite_gaussian_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.finite_gaussian_comparison

/-- info: 'MajorityDynamics.Binomial.Approximation.finite_cell_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.finite_cell_comparison

/-- info: 'MajorityDynamics.Binomial.Approximation.inequality_event_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.inequality_event_mismatch

/-- info: 'MajorityDynamics.Analysis.gaussian_cell_mass_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.gaussian_cell_mass_error

/-- info: 'MajorityDynamics.Analysis.gaussian_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.gaussian_tail

/-- info: 'MajorityDynamics.Analysis.gaussian_linear_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.gaussian_linear_strip

/-- info: 'MajorityDynamics.Analysis.prod_monomial_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.prod_monomial_error

/-- info: 'MajorityDynamics.Binomial.Approximation.gaussian_window_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.gaussian_window_comparison

/-- info: 'MajorityDynamics.Binomial.Approximation.gaussian_second_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.gaussian_second_moment_le

/-- info: 'MajorityDynamics.Binomial.Approximation.gaussian_scalar_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.gaussian_scalar_geometry

example : MajorityDynamics.Binomial.Approximation.GaussianComparisonTheorem := MajorityDynamics.Binomial.Approximation.gaussian_comparison

/-- info: 'MajorityDynamics.Binomial.Approximation.gaussian_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.gaussian_comparison

example : MajorityDynamics.Binomial.Approximation.AppendixA2Theorem := MajorityDynamics.Binomial.Approximation.appendix_a2

/-- info: 'MajorityDynamics.Binomial.Approximation.appendix_a2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.appendix_a2

/-! Appendix E.2: the full compact-regularity target, without internal inputs.
The conditional-law bridges ensure the normalized formulas mean the actual
conditional expectations and centered covariance from the manuscript. -/

example : MajorityDynamics.Analysis.GaussianRegularity.GaussianRegularityTheorem :=
  MajorityDynamics.Analysis.GaussianRegularity.gaussian_regularity

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.gaussian_regularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.gaussian_regularity

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.locallyLipschitzOn_weighted_law_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.locallyLipschitzOn_weighted_law_integral

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.setIntegral_law_eq_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.setIntegral_law_eq_density

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.conditionalFirst_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.conditionalFirst_eq_integral

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.conditionalSecond_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.conditionalSecond_eq_integral

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.conditionalCovariance_eq_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.conditionalCovariance_eq_covariance


/-! Appendix E.3: closed uniform row limits and the literal integer-size,
real-exponent statement. No internal hypotheses survive these endpoints. -/
example : MajorityDynamics.Idealized.RowLimits.RowLimitsTheorem :=
  MajorityDynamics.Idealized.RowLimits.row_limits
example : MajorityDynamics.Idealized.RowLimits.RowLimitsRealTheorem :=
  MajorityDynamics.Idealized.RowLimits.row_limits_real

/-- info: 'MajorityDynamics.Idealized.RowLimits.row_limits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.row_limits

/-- info: 'MajorityDynamics.Idealized.RowLimits.row_limits_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.row_limits_real

/-- info: 'MajorityDynamics.Idealized.RowLimits.smooth_quantities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.smooth_quantities

/-- info: 'MajorityDynamics.Idealized.RowLimits.rowLimitsReal_of_rowLimits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.rowLimitsReal_of_rowLimits

/-! Theorem 5.2: complete finite-horizon idealized existence and uniqueness.
The cited scalar binomial Chernoff and Brouwer inputs are now proved, so the
closed targets below use only the standard foundations. -/
example : MajorityDynamics.Idealized.Process.OneStepTheorem :=
  MajorityDynamics.Idealized.Process.one_step
example : MajorityDynamics.Idealized.Process.IdealizedProcessTheorem :=
  MajorityDynamics.Idealized.Process.idealized_process
example : MajorityDynamics.Idealized.Process.IdealizedProcessRealTheorem :=
  MajorityDynamics.Idealized.Process.idealized_process_real

/-- info: 'MajorityDynamics.Idealized.Process.one_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.Process.one_step

/-- info: 'MajorityDynamics.Idealized.Process.idealized_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.Process.idealized_process

/-- info: 'MajorityDynamics.Idealized.Process.idealized_process_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.Process.idealized_process_real
