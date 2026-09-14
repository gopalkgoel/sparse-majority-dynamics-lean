import MajorityDynamics.GraphProcess.EnumerationComparison.Product
import MajorityDynamics.GraphProcess.EnumerationComparison.Corrections

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Universal BlockDecomposition EnumerationBounds BlockPairLaws
open Literature.DegreeEnumeration
variable {V : Type*} [Fintype V] {n : ℕ}

theorem graphical_atom_real (y : Local.CoarseData V n) (d : RowArray.Ambient y.part) :
    (GraphicalArray.law y.part y.edge).real {d} =
      (∏ s, (internalGraphLaw y.part y.edge s).real {internalVector y.part d s}) *
        ∏ r, (crossGraphLaw y.part y.edge r).real {crossVector y.part d r} := by
  simp only [measureReal_def, graphical_atom, ENNReal.toReal_mul, ENNReal.toReal_prod]

theorem binomial_atom_real (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) :
    (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d} =
      (∏ s, (internalBinomialLaw y.part y.edge s).real {internalVector y.part d s}) *
        ∏ r, (crossBinomialLaw y.part y.edge r).real {crossVector y.part d r} := by
  simp only [measureReal_def, binomial_atom, ENNReal.toReal_mul, ENNReal.toReal_prod]

theorem factor_shift (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part)
    (hi : ∀ s, RelativeApproximation (1/2)
      ((internalGraphLaw y.part y.edge s).real {internalVector y.part d s})
      ((internalBinomialLaw y.part y.edge s).real {internalVector y.part d s} *
        Real.exp (internalCorrection y d s)))
    (hc : ∀ r, RelativeApproximation (1/2)
      ((crossGraphLaw y.part y.edge r).real {crossVector y.part d r})
      ((crossBinomialLaw y.part y.edge r).real {crossVector y.part d r} *
        Real.exp (crossCorrection y d r.val.1 r.val.2))) :
    ShiftBounds (correction y d) (correctionCount n)
      ((GraphicalArray.law y.part y.edge).real {d})
      ((cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d}) := by
  have h₁ := shift_prod Finset.univ (internalCorrection y d) (fun _ => 1)
    (fun s => (internalGraphLaw y.part y.edge s).real {internalVector y.part d s})
    (fun s => (internalBinomialLaw y.part y.edge s).real {internalVector y.part d s})
    (fun _ _ => measureReal_nonneg) (fun s _ => relative_half_shift measureReal_nonneg (hi s))
  have h₂ := shift_prod Finset.univ
    (fun r : Pair (History (n+1)) => crossCorrection y d r.val.1 r.val.2) (fun _ => 1)
    (fun r => (crossGraphLaw y.part y.edge r).real {crossVector y.part d r})
    (fun r => (crossBinomialLaw y.part y.edge r).real {crossVector y.part d r})
    (fun _ _ => measureReal_nonneg) (fun r _ => relative_half_shift measureReal_nonneg (hc r))
  have hh := h₁.mul h₂ (Finset.prod_nonneg fun _ _ => measureReal_nonneg)
    (Finset.prod_nonneg fun _ _ => measureReal_nonneg)
  rw [graphical_atom_real, binomial_atom_real]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    correction, correctionCount] using hh

end MajorityDynamics.GraphProcess.EnumerationComparison
