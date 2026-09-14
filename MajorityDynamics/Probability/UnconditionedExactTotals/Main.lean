import MajorityDynamics.Probability.UnconditionedExactTotals.Atom
import MajorityDynamics.Probability.UnconditionedExactTotals.Windows

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.UnconditionedExactTotals
open FixedSizeExponential

def comparisonConstant (T : ℝ) : ℝ := Real.sqrt (2 * T ^ 2)

def lowerConstant (d : ℕ) (T : ℝ) : ℝ := (centralAtomConstant / comparisonConstant T) ^ d

theorem toNat_real {a : ℤ} (ha : 0 ≤ a) : (a.toNat : ℝ) = a := by
  exact_mod_cast Int.toNat_of_nonneg ha

/-- B.5 with `r=0`, for every dimension and all integer sizes and real tilts
in the literal windows. Only the integer-mean condition is assumed. -/
theorem unconditioned_exact_totals : UnconditionedExactTotalsTheorem := by
  intro θ hθlo hθhi d _hd T hT
  have hT0 : 0 < T := by linarith
  have hK : 0 < comparisonConstant T := Real.sqrt_pos.mpr (by positivity)
  have hC : 0 < lowerConstant d T := pow_pos (div_pos centralAtomConstant_pos hK) d
  obtain ⟨n₀, hn₀⟩ := eventually_windows hθlo hθhi hT
  refine ⟨lowerConstant d T, hC, n₀, ?_⟩
  intro n hn p hp η hηw m hmw q hqw z hz
  obtain ⟨hn0, hp0, hp1, hsizes, htilts⟩ := hn₀ n hn p hp
  have hm : 1 ≤ m := hsizes m hmw
  have hη : ∀ t, 1 ≤ η t := fun t => hsizes (η t) (hηw t)
  have hq : ∀ t, 0 < q t ∧ q t < 1 ∧ q t < 2 * p := fun t => htilts (q t) (hqw t)
  have hb := center_bounds hT0 hn0 hp0 hm hmw hη hηw hq hz
  have hm0 : 0 ≤ m := by omega
  have he0 (t : Fin d) : 0 ≤ η t := by have := hη t; omega
  have hz0 (t : Fin d) : 0 ≤ z t := (hb t).1.le
  have hmc : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
  have hec (t : Fin d) : ((η t).toNat : ℤ) = η t := Int.toNat_of_nonneg (he0 t)
  have hzc (t : Fin d) : ((z t).toNat : ℤ) = z t := Int.toNat_of_nonneg (hz0 t)
  refine ⟨hp0, by linarith, hm, hmc, ?_, ?_⟩
  · intro t
    exact ⟨(hq t).1, (hq t).2.1, hη t, hec t, (hb t).1, (hb t).2.1, hzc t⟩
  · have hs0 (t : Fin d) : 0 < (z t).toNat := by
      have : (0 : ℤ) < ((z t).toNat : ℤ) := by rw [hzc]; exact (hb t).1
      exact_mod_cast this
    have hsN (t : Fin d) : (z t).toNat < m.toNat * (η t).toNat := by
      have : ((z t).toNat : ℤ) < (m.toNat : ℤ) * ((η t).toNat : ℤ) := by
        rw [hzc, hmc, hec]
        exact (hb t).2.1
      exact_mod_cast this
    have hmean (t : Fin d) : ((z t).toNat : ℝ) =
        ((m.toNat * (η t).toNat : ℕ) : ℝ) * q t := by
      rw [Nat.cast_mul, toNat_real hm0, toNat_real (he0 t), toNat_real (hz0 t)]
      exact hz t
    have hupper (t : Fin d) : ((z t).toNat : ℝ) ≤
        comparisonConstant T ^ 2 * ((n : ℝ) ^ 2 * p) := by
      rw [toNat_real (hz0 t), comparisonConstant, Real.sq_sqrt (by positivity)]
      exact (hb t).2.2
    have hbound := finite_atom_lower hK (by positivity : 0 < (n : ℝ) ^ 2 * p)
      (fun t => ⟨(hq t).1, (hq t).2.1⟩) hs0 hsN hmean hupper
    simpa only [lowerConstant, hzc] using hbound

end MajorityDynamics.Probability.UnconditionedExactTotals
