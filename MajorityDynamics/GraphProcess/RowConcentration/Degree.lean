import MajorityDynamics.GraphProcess.RowConcentration.Regime
import MajorityDynamics.GraphProcess.RowConcentration.Expectations
import MajorityDynamics.Probability.DegreeConcentration.Moment

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal

/-- The literal binomial coordinate tail after allowing for its mean bias. -/
theorem shifted_binomial_tail (m : ℕ) (q : unitInterval) {x L a : ℝ}
    (hx : 0 < x) (hL : 0 < L) (hm : (m:ℝ)*q ≤ 2*x)
    (hbias : |a-(m:ℝ)*q| ≤ Real.sqrt x*L/2)
    (hscale : Real.sqrt x*L ≤ x) :
    (binomial m q).real {k : ℕ | Real.sqrt x*L < |(k:ℝ)-a|} ≤
      2*Real.exp (-(3:ℝ)/80*L^2) := by
  have hs := Real.sqrt_pos.mpr hx
  have hu : 0 < Real.sqrt x*L/2 := by positivity
  have hb := Probability.DegreeConcentration.binomial_two_sided_tail m q (2*x)
    (Real.sqrt x*L/2) (by positivity) hm hu (by nlinarith)
  have hsub : {k : ℕ | Real.sqrt x*L < |(k:ℝ)-a|} ⊆
      {k : ℕ | Real.sqrt x*L/2 < |(k:ℝ)-(m:ℝ)*q|} := by
    intro k hk
    have ht := abs_sub_le (k:ℝ) ((m:ℝ)*q) a
    rw [abs_sub_comm ((m:ℝ)*q) a] at ht
    change Real.sqrt x*L < |(k:ℝ)-a| at hk
    change Real.sqrt x*L/2 < |(k:ℝ)-(m:ℝ)*q|
    linarith
  refine (measureReal_mono hsub).trans (hb.trans_eq ?_)
  congr 2
  rw [div_pow, mul_pow, Real.sq_sqrt hx.le]
  field_simp [hx.ne']
  ring

variable {V : Type*} [Fintype V] {n : ℕ}

theorem coordinate_tail (y : Local.CoarseData V n) (q : Local.Tilt n)
    {p φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hN : 0 < (Fintype.card V : ℝ)) (hp : 0 < p)
    (hlog : 1 ≤ Real.log (Fintype.card V : ℝ))
    (hscale : Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V : ℝ))^((2:ℝ)/3) ≤ p*Fintype.card V)
    (hmean : ∀ s t, (Local.trials y.sizes s t : ℝ)*(q s t : ℝ) ≤ 2*p*Fintype.card V ∧
      |p*(y.sizes t : ℝ)-(Local.trials y.sizes s t : ℝ)*(q s t : ℝ)| ≤
        Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V : ℝ))^((2:ℝ)/3)/2)
    (v : V) (t : History (n+1)) :
    (conditionedLaw y q).real {d | Real.sqrt (p*Fintype.card V)*
      (Real.log (Fintype.card V : ℝ))^((2:ℝ)/3) <
        |(RowArray.values d v t : ℝ)-p*y.sizes t|} ≤
      (2/φ)*Real.exp (-(3:ℝ)/80*(Real.log (Fintype.card V : ℝ))^((4:ℝ)/3)) := by
  let E : Set ℕ := {k | Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V : ℝ))^((2:ℝ)/3) <
    |(k:ℝ)-p*y.sizes t|}
  have hcond := conditioned_row_event_le y q hφ hc v {a | a t ∈ E}
  rw [raw_row_coordinate] at hcond
  have hraw := shifted_binomial_tail (Local.trials y.sizes (y.part v) t)
    (Binomial.closedProbability (q (y.part v) t)) (mul_pos hp hN)
    (Real.rpow_pos_of_pos (by linarith : 0 < Real.log (Fintype.card V : ℝ)) _)
    (by simpa [mul_assoc, Binomial.closedProbability] using (hmean (y.part v) t).1)
    (hmean (y.part v) t).2 hscale
  have heq : ((Real.log (Fintype.card V : ℝ))^((2:ℝ)/3))^2 =
      (Real.log (Fintype.card V : ℝ))^((4:ℝ)/3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log (Fintype.card V : ℝ))]
    congr 1
    norm_num
  rw [heq] at hraw
  have hout := hcond.trans (div_le_div_of_nonneg_right hraw hφ.le)
  have hevent : {d : RowArray.Ambient y.part | Real.sqrt (p*Fintype.card V)*
      (Real.log (Fintype.card V : ℝ))^((2:ℝ)/3) <
        |(RowArray.values d v t : ℝ)-p*y.sizes t|} =
      {d | RowArray.naturalRows d v ∈ {a | a t ∈ E}} := by
    ext d
    simp only [E, mem_ofPred_eq, RowArray.values, RowArray.naturalRows, Binomial.point, Int.cast_natCast]
  rw [hevent]
  exact hout.trans_eq (by ring)

/-- The complete finite R1 union bound under original history conditioning. -/
theorem degree_tail (y : Local.CoarseData V n) (q : Local.Tilt n)
    {p φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (hN : 0 < (Fintype.card V : ℝ)) (hp : 0 < p)
    (hlog : 1 ≤ Real.log (Fintype.card V : ℝ))
    (hscale : Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V : ℝ))^((2:ℝ)/3) ≤ p*Fintype.card V)
    (hmean : ∀ s t, (Local.trials y.sizes s t : ℝ)*(q s t : ℝ) ≤ 2*p*Fintype.card V ∧
      |p*(y.sizes t : ℝ)-(Local.trials y.sizes s t : ℝ)*(q s t : ℝ)| ≤
        Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V : ℝ))^((2:ℝ)/3)/2) :
    (conditionedLaw y q).real {d | ¬ R1 y p d} ≤
      ((2:ℝ)^(n+1)*2/φ)*(Fintype.card V : ℝ)*
        Real.exp (-(3:ℝ)/80*(Real.log (Fintype.card V : ℝ))^((4:ℝ)/3)) := by
  have : IsProbabilityMeasure (conditionedLaw y q) := conditioned_probability y q hφ hc
  let E (i : V × History (n+1)) : Set (RowArray.Ambient y.part) :=
    {d | Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V : ℝ))^((2:ℝ)/3) <
      |(RowArray.values d i.1 i.2 : ℝ)-p*y.sizes i.2|}
  have heq : {d | ¬ R1 y p d} = ⋃ i, E i := by
    ext d
    simp only [R1, mem_ofPred_eq, not_forall, not_le, mem_iUnion, E]
    exact ⟨fun ⟨v,t,ht⟩ => ⟨(v,t),ht⟩, fun ⟨⟨v,t⟩,ht⟩ => ⟨v,t,ht⟩⟩
  rw [heq]
  refine (measureReal_iUnion_fintype_le E).trans ?_
  calc
    ∑ i, (conditionedLaw y q).real (E i) ≤
      ∑ _i : V × History (n+1), (2/φ)*Real.exp
        (-(3:ℝ)/80*(Real.log (Fintype.card V : ℝ))^((4:ℝ)/3)) := by
      apply Finset.sum_le_sum
      intro i _
      exact coordinate_tail y q hφ hc hN hp hlog hscale hmean i.1 i.2
    _ = _ := by simp [Fintype.card_prod]; ring

universe u
/-- Full uniform R1 concentration, with no edge-count or admissibility premise. -/
theorem uniform_degree_tail {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      Conditioning y q φ →
      (conditionedLaw y q).real {d | ¬ R1 y p d} ≤ (N:ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := uniform_degree_regime n hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_log_tail
    (C := (2:ℝ)^(n+1)*2/φ) (c := 3/80) (r := 4/3) (b := 1) (A := A)
    (by positivity) (by norm_num) (by norm_num)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes htilt hc
  have hr := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hsizes htilt
  have ht := h₂ N ((le_max_right _ _).trans hN)
  rw [Real.rpow_one] at ht
  subst N
  exact (degree_tail y q hφ hc hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2).trans (by simpa only [neg_div] using ht)

end MajorityDynamics.GraphProcess.RowConcentration

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.shifted_binomial_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.shifted_binomial_tail

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.coordinate_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.coordinate_tail

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.degree_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.degree_tail

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.uniform_degree_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.uniform_degree_tail
