import MajorityDynamics.GraphProcess.RowGamma.Results
import MajorityDynamics.GraphProcess.RowGamma.Numerics

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Pure actual-conditioning assembly: polynomial total loss and a factor two
for kappa preserve every requested power without changing Gamma's constant. -/
theorem conclusion_of_bounds (y : Local.CoarseData V n) (q : Local.Tilt n)
    {C p A : ℝ} {N : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hp1 : p ≤ 1)
    (hμ : IsProbabilityMeasure (RowConcentration.conditionedLaw y q))
    (hhistory : 0 < (RowArray.law y.part q).real (RowArray.history y.part))
    (htotals : ((N : ℝ)^2*p)^(-(RowExactTotals.totalExponent n : ℝ)) ≤
      (RowConcentration.conditionedLaw y q).real (RowArray.exactTotals y.part y.edge))
    (hgamma : (RowConcentration.conditionedLaw y q).real
      {d | ¬ RowArray.Gamma y.part (RowArray.totals d) C p d} ≤
        (N : ℝ)^(-(max A 1+1+2*(RowExactTotals.totalExponent n : ℝ))))
    (hregular : (cond (RowConcentration.conditionedLaw y q)
      (RowArray.exactTotals y.part y.edge)).real {d | ¬ RowArray.Regular p d} ≤
        (N : ℝ)^(-(max A 1+1))) : Conclusion y q C p A N := by
  let μ := RowConcentration.conditionedLaw y q
  let E := RowArray.exactTotals y.part y.edge
  let ν := cond μ E
  let R : Set (RowArray.Ambient y.part) := {d | RowArray.Regular p d}
  let G : Set (RowArray.Ambient y.part) := {d | RowArray.Gamma y.part y.edge C p d}
  let := hμ
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hbase : 0 < (N : ℝ)^2*p := by positivity
  have hEpos : 0 < μ.real E :=
    (Real.rpow_pos_of_pos hbase _).trans_le htotals
  have hν : IsProbabilityMeasure ν :=
    RowExactTotals.conditioned_probability_of_real_lower μ E hEpos le_rfl
  let := hν
  change ν.real Rᶜ ≤ (N : ℝ)^(-(max A 1+1)) at hregular
  have hνgamma : ν.real Gᶜ ≤ (N : ℝ)^(-(max A 1+1)) := by
    change (cond μ E).real {d | ¬ RowArray.Gamma y.part y.edge C p d} ≤ _
    rw [conditioned_gamma_eq y C p μ]
    exact RowExactTotals.conditioned_failure_power μ E _ (Set.to_countable _).measurableSet
      hNp hp hp1 (Nat.cast_nonneg _) htotals hgamma
  have hpow1 : (N : ℝ)^(-(max A 1+1)) ≤ (N : ℝ)^(-(1:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_max_right A 1])
  have hRlower : (1:ℝ)/2 ≤ ν.real R := by
    have hh := good_mass_lower ν R (Set.to_countable _).measurableSet (hregular.trans hpow1)
    exact (Numerics.half_lower hN).trans hh
  have hτ : IsProbabilityMeasure (cond ν R) :=
    RowExactTotals.conditioned_probability_of_real_lower ν R (by norm_num) hRlower
  have hB : (N : ℝ)^(-max A 1) ≤ (N : ℝ)^(-A) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (le_max_left A 1))
  have hτgamma : (cond ν R).real Gᶜ ≤ (N : ℝ)^(-max A 1) := by
    calc
      _ ≤ 2*ν.real Gᶜ := conditioned_failure_two ν R Gᶜ (Set.to_countable _).measurableSet hRlower
      _ ≤ 2*(N : ℝ)^(-(max A 1+1)) := mul_le_mul_of_nonneg_left hνgamma (by norm_num)
      _ ≤ _ := Numerics.absorb_two hN (max A 1)
  have hjoint : ν.real (G ∩ R)ᶜ ≤ (N : ℝ)^(-max A 1) := by
    calc
      _ ≤ ν.real Gᶜ + ν.real Rᶜ := gamma_regular_failure_le y C p ν
      _ ≤ 2*(N : ℝ)^(-(max A 1+1)) := by linarith
      _ ≤ _ := Numerics.absorb_two hN (max A 1)
  have hjointlower : (1:ℝ)/2 ≤ ν.real (G ∩ R) := by
    have hB1 : (N : ℝ)^(-max A 1) ≤ (N : ℝ)^(-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (le_max_right A 1))
    exact (Numerics.half_lower hN).trans
      (good_mass_lower ν (G ∩ R) (Set.to_countable _).measurableSet (hjoint.trans hB1))
  refine ⟨hμ,hhistory,htotals,hEpos,hν,hRlower,hτ,triple_conditioning y q p,?_,?_,
    hτgamma.trans hB,hjoint.trans hB,hjointlower⟩
  · exact hgamma.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by
      have he : 0 ≤ (RowExactTotals.totalExponent n : ℝ) := Nat.cast_nonneg _
      linarith [le_max_left A 1]))
  · exact hνgamma.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_max_left A 1]))

end MajorityDynamics.GraphProcess.RowGamma
