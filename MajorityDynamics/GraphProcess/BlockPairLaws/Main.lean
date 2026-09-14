import MajorityDynamics.GraphProcess.BlockPairLaws.Comparison

/-! Exact finite factorization step of Appendix B.2. This does not assert the
subsequent weak/strong asymptotic enumeration comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Both literal identities in eq:enum-factor on the actual original array.
No graphicality, history, regularity, tilt symmetry or asymptotic hypothesis. -/
theorem enum_factor (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) :
    (GraphicalArray.law y.part y.edge {d} =
      (∏ s, internalGraphLaw y.part y.edge s {internalVector y.part d s}) *
        ∏ p, crossGraphLaw y.part y.edge p {crossVector y.part d p}) ∧
    (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge) {d} =
      (∏ s, internalBinomialLaw y.part y.edge s {internalVector y.part d s}) *
        ∏ p, crossBinomialLaw y.part y.edge p {crossVector y.part d p}) :=
  ⟨graphical_atom y d, binomial_atom y q d⟩

end MajorityDynamics.GraphProcess.BlockPairLaws
