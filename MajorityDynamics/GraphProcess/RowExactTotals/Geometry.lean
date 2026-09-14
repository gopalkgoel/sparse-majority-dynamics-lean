import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Main
import MajorityDynamics.GraphProcess.RowArray.Conditioning
import MajorityDynamics.GraphProcess.EnumerationBounds.Numerics
import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics
import MajorityDynamics.Idealized.RowLimits.EventsBounds
import MajorityDynamics.Local.Admissibility

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal
open Idealized.RowLimits
open Probability.ConditionedBinomialFourier

variable {V : Type*} [Fintype V] {n : ℕ}

/-- The CLT event is exactly the original history conditioning, including ties. -/
theorem rowCondition_eq_clt (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s : History (n+1)) :
    Local.rowCondition sizes q s = cond (Binomial.law (Local.trials sizes s) (q s))
      (Binomial.inequalityEvent (fun j i => (historyIntegerMatrix s j i : ℝ))
        (historyStrict s)) := by
  rw [RowArray.rowCondition_eq_cond]
  congr 1
  ext a
  exact (history_inequalityEvent s a).symm

/-- The signed history matrix inherits the original LA imbalance bound. -/
theorem admissible_history_balance (y : Local.CoarseData V n) (q : Local.Tilt n)
    {T φ p : ℝ} (ha : Local.CoreAdmissible y q T φ p) (s : History (n+1)) (j : Fin n) :
    |∑ t, historyMatrix s j t * (y.sizes t : ℝ)| ≤
      T*(Fintype.card V : ℝ)/Real.sqrt (p*Fintype.card V) := by
  have hs : |sign (bits (n+1) s j.succ)| = 1 := by
    cases bits (n+1) s j.succ <;> norm_num
  simpa only [historyMatrix, mul_assoc, ← Finset.mul_sum, abs_mul, hs, one_mul]
    using ha.imbalances j

/-- Original local admissibility, with the exact diagonal deletion, supplies
all trial, tilt, balance and copy-count windows for CLT constant `2*T`. -/
theorem admissible_clt_geometry (y : Local.CoarseData V n) (q : Local.Tilt n)
    {T φ p : ℝ} (hT : 1 < T) (ha : Local.CoreAdmissible y q T φ p)
    (hN : 2*T ≤ (Fintype.card V : ℝ)) (hp : 0 < p) (hp1 : p ≤ 1)
    (s : History (n+1)) :
    (∀ t, (Fintype.card V : ℝ)/(2*T) ≤ (Local.trials y.sizes s t : ℝ)) ∧
    (∀ t, (Local.trials y.sizes s t : ℝ) ≤ (2*T)*Fintype.card V) ∧
    (∀ t, |(q s t : ℝ)-p| ≤ (2*T)*p/Real.sqrt (p*Fintype.card V)) ∧
    (∀ j, |∑ t, (historyIntegerMatrix s j t : ℝ)*(Local.trials y.sizes s t : ℝ)| ≤
      (2*T)*Fintype.card V/Real.sqrt (p*Fintype.card V)) ∧
    (Fintype.card V : ℝ)/(2*T) ≤ (y.sizes s : ℝ) ∧
    (y.sizes s : ℝ) ≤ (2*T)*Fintype.card V := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < (Fintype.card V : ℝ) := by linarith
  have hsizes (t : History (n+1)) : (Fintype.card V : ℝ)/T ≤ (y.sizes t : ℝ) := by
    simpa only [div_eq_mul_inv, mul_comm] using ha.sizes t
  have hz (t : History (n+1)) := EnumerationBounds.size_estimates hT hN (hsizes t)
  have hspos (t : History (n+1)) : 0 < y.sizes t := by
    exact_mod_cast (show (0:ℝ) < y.sizes t by linarith [(hz t).1])
  have hsupper (t : History (n+1)) : (y.sizes t : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast y.sizes_le_card t
  have hupper : (Fintype.card V : ℝ) ≤ (2*T)*Fintype.card V := by nlinarith
  have hsqrt : 0 < Real.sqrt (p*Fintype.card V) := Real.sqrt_pos.mpr (mul_pos hp hN0)
  have hroot : Real.sqrt (p*Fintype.card V) ≤ (Fintype.card V : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hN0.le, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hp1 hN0.le]
  have hquot : 1 ≤ T*Fintype.card V/Real.sqrt (p*Fintype.card V) := by
    apply (le_div_iff₀ hsqrt).mpr
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, (hsupper s).trans hupper⟩
  · intro t
    rw [trials_cast y.sizes s t (hspos t)]
    split_ifs <;> linarith [(hz t).2]
  · intro t
    have ht : Local.trials y.sizes s t ≤ y.sizes t := Nat.sub_le _ _
    exact (show (Local.trials y.sizes s t : ℝ) ≤ y.sizes t by exact_mod_cast ht).trans
      ((hsupper t).trans hupper)
  · intro t
    exact (ha.tilt s t).trans (div_le_div_of_nonneg_right
      (by nlinarith : T*p ≤ (2*T)*p) hsqrt.le)
  · intro j
    simp_rw [historyIntegerMatrix_cast]
    have hb := matrix_trials_bound y.sizes s hspos (historyMatrix s) j
      (abs_historyMatrix s j s).le (admissible_history_balance y q ha s j)
    calc
      _ ≤ T*Fintype.card V/Real.sqrt (p*Fintype.card V)+1 := hb
      _ ≤ (2*T)*Fintype.card V/Real.sqrt (p*Fintype.card V) := by
        rw [show (2*T)* (Fintype.card V : ℝ)/Real.sqrt (p*Fintype.card V) =
          2*(T*Fintype.card V/Real.sqrt (p*Fintype.card V)) by ring]
        linarith
  · linarith [(hz s).2]

universe u
/-- The actual iid sum for each original history block has the CLT atom lower
bound. The constant and threshold precede all varying locally admissible data. -/
theorem uniform_block_local_clt (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (n : ℕ) (T : ℝ) (hT : 1 < T) (φ : ℝ) (s : History (n+1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V],
      Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      IsProbabilityMeasure (Local.rowCondition y.sizes q s) ∧
      IsProbabilityMeasure (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)) ∧
      c*((N : ℝ)^2*p)^(-(Fintype.card (History (n+1)) : ℝ)/2) ≤
        (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)).real
          {x | ∀ t, (∑ j, (x j t : ℤ)) = y.edge s t} := by
  have hT0 : 0 < T := by linarith
  have h2T : 1 < 2*T := by linarith
  obtain ⟨c,hc,N₁,h₁⟩ := Probability.ConditionedBinomialLocalCLT.uniform_local_clt
    θ hθlo hθhi (Fintype.card (Fin (n+1) → Bool)) (by exact Fintype.card_pos)
    n (historyIntegerMatrix s) (historyIntegerMatrix_orthogonal s) (historyStrict s) (2*T) h2T
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 2*T) (by positivity)
  refine ⟨c,hc,max N₁ N₂,?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hr := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hpLo : (2*T)⁻¹*(N : ℝ)^(-θ) < p := by
    exact (mul_le_mul_of_nonneg_right (inv_anti₀ hT0 (by linarith))
      (Real.rpow_nonneg hr.1.le _)).trans_lt hlo
  have hpHi : p < (2*T)*(N : ℝ)^(-θ) := by
    exact hhi.trans_le (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr.1.le _))
  have hg := admissible_clt_geometry y q hT ha (by simpa [hcard] using hr.2.2.1)
    hr.2.1 hr.2.2.2.2 s
  rw [hcard] at hg
  obtain ⟨hρ,hcopy,hprob⟩ := h₁ N ((le_max_left _ _).trans hN) p hpLo hpHi
    (Local.trials y.sizes s) (q s) (y.sizes s) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1
    hg.2.2.2.2.1 hg.2.2.2.2.2
  rw [← rowCondition_eq_clt] at hρ hcopy hprob
  refine ⟨hρ,hcopy,?_⟩
  have hz (t : History (n+1)) : (y.edge s t : ℝ) =
      (y.sizes s : ℝ)*mean (Local.rowCondition y.sizes q s) t := by
    simpa only [Local.CoarseData.realEdges, Local.rowMean_eq_integral, mean] using
      (ha.solves s t).symm
  simpa only [History, Fintype.card_fin] using hprob (y.edge s) hz

end MajorityDynamics.GraphProcess.RowExactTotals
