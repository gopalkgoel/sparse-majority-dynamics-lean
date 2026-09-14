import MajorityDynamics.GraphProcess.DayOne.Probability
import MajorityDynamics.GraphProcess.FaithfulStep.Rates
import MajorityDynamics.GraphProcess.DayOne.Decay

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.DayOne
open Universal History
variable {V : Type*} [Fintype V]

def Good (π : V → History 1) (p : ℝ) (N : ℕ) (G : SimpleGraph V) : Prop :=
  CoarseKernel.Regular p π (degreeArray π G) ∧
    ∀ s t, |(edgeTotals π (degreeArray π G) s t:ℝ) -
      p*(Local.partSizes π s:ℝ)*((Local.partSizes π t:ℝ)-(if s=t then 1 else 0))| ≤
        2*(N:ℝ)*Real.sqrt p*Real.log (N:ℝ)

theorem concentration (π : V → History 1) (p : unitInterval) (N : ℕ)
    (hcard : Fintype.card V=N) (hN : 0 < (N:ℝ)) (hp : 0 < (p:ℝ))
    (hlog : 0 < Real.log (N:ℝ))
    (hreg : Real.sqrt ((p:ℝ)*N)*Real.log (N:ℝ) ≤ ((p:ℝ)*N)^((4:ℝ)/7))
    (hdeg : Real.sqrt ((p:ℝ)*N)*Real.log (N:ℝ) ≤ (p:ℝ)*N)
    (hbias : (p:ℝ) ≤ Real.sqrt ((p:ℝ)*N)*Real.log (N:ℝ)/2)
    (hedge : Real.sqrt ((N:ℝ)^2*p)*Real.log (N:ℝ) ≤ (N:ℝ)^2*p) :
    (SimpleGraph.binomialRandom V p).real {G | ¬Good π p N G} ≤
      (4*(N:ℝ)+8)*Real.exp (-(3:ℝ)/80*(Real.log (N:ℝ))^2) := by
  let D := fun (v:V) (t:History 1) => {G : SimpleGraph V |
    Real.sqrt ((p:ℝ)*N)*Real.log (N:ℝ) <
      |(degreeArray π G v t:ℝ)-(p:ℝ)*Local.partSizes π t|}
  let E := fun (s t:History 1) => {G : SimpleGraph V |
    2*Real.sqrt ((N:ℝ)^2*p)*Real.log (N:ℝ) <
      |(edgeTotals π (degreeArray π G) s t:ℝ)-
        (p:ℝ)*Local.partSizes π s*((Local.partSizes π t:ℝ)-(if s=t then 1 else 0))|}
  let b : ℝ := 2*Real.exp (-(3:ℝ)/80*(Real.log (N:ℝ))^2)
  have hsqrt : Real.sqrt ((N:ℝ)^2*p) = (N:ℝ)*Real.sqrt p := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN.le]
  have hD : ∀ v t, (SimpleGraph.binomialRandom V p).real (D v t) ≤ b := by
    intro v t
    apply degree_tail π v t p (mul_pos hp hN) hlog _ hbias hdeg
    have hs : (Local.partSizes π t:ℝ) ≤ N := by
      rw [← hcard]
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset (s := (Finset.univ : Finset V)) (p := fun v => π v=t)))
    have hh := mul_le_mul_of_nonneg_right hs hp.le
    nlinarith only [hh, mul_pos hp hN]
  have hE : ∀ s t, (SimpleGraph.binomialRandom V p).real (E s t) ≤ b := by
    intro s t
    exact edge_tail π s t p (mul_pos (sq_pos_of_pos hN) hp) hlog
      (by rw [hcard]) hedge
  have hsub : {G | ¬Good π p N G} ⊆ (⋃ v, ⋃ t, D v t) ∪ (⋃ s, ⋃ t, E s t) := by
    intro G hG
    by_contra h
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, D, E, Set.mem_ofPred_eq] at h
    apply hG
    constructor
    · intro v t
      have hh := le_of_not_gt (h.1 v t)
      exact hh.trans (by simpa only [hcard] using hreg)
    · intro s t
      have hh := le_of_not_gt (h.2 s t)
      simpa only [hsqrt, mul_assoc] using hh
  have hdb : (SimpleGraph.binomialRandom V p).real (⋃ v, ⋃ t, D v t) ≤
      (N:ℝ)*2*b := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    calc
      _ ≤ ∑ v:V, ∑ t:History 1, b := by
        apply Finset.sum_le_sum
        intro v _
        exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun t _ => hD v t))
      _ = _ := by simp [hcard]; ring
  have heb : (SimpleGraph.binomialRandom V p).real (⋃ s, ⋃ t, E s t) ≤ 4*b := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    calc
      _ ≤ ∑ s:History 1, ∑ t:History 1, b := by
        apply Finset.sum_le_sum
        intro s _
        exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun t _ => hE s t))
      _ = _ := by simp; ring
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    ((add_le_add hdb heb).trans_eq (by dsimp [b]; ring)))

universe u
open Idealized.LinearResponse Binomial.Approximation
/-- Uniformity includes every fixed initial partition, without balance assumptions. -/
theorem eventually_concentration {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ π : V → History 1,
      (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
        {G | ¬Good π (p:ℝ) N G} ≤
        (4*(N:ℝ)+8)*Real.exp (-(3:ℝ)/80*(Real.log (N:ℝ))^2) := by
  filter_upwards [eventually_basic θ T hθlo hθhi hT,
    FaithfulStep.eventually_day_one_scales hθlo hθhi hT] with N hb hs
  intro p hp V _ hcard π
  have hN : 0 < (N:ℝ) := by exact_mod_cast hb.1
  exact concentration π (Binomial.closedProbability p) N hcard hN p.property.1
    (by linarith [hb.2.1]) (hs p hp).1 (hs p hp).2.1 (hs p hp).2.2.1 (hs p hp).2.2.2

/-- A single vanishing failure envelope for every density and partition. -/
theorem uniform_concentration {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ π : V → History 1,
      (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
        {G | ¬Good π (p:ℝ) N G} ≤ (N:ℝ)^(-(1:ℝ)) := by
  filter_upwards [eventually_concentration hθlo hθhi hT,
    eventually_failure_decay] with N hp hd
  intro p hpd V _ hcard π
  exact (hp p hpd V hcard π).trans (by simpa only [neg_div] using hd)

end MajorityDynamics.GraphProcess.DayOne
