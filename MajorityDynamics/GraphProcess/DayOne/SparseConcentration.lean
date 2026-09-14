import MajorityDynamics.GraphProcess.DayOne.Concentration
import MajorityDynamics.GraphProcess.FaithfulStep.SparseRates

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace MajorityDynamics.GraphProcess.DayOne
open Universal History Idealized.LinearResponse Binomial.Approximation
universe u
theorem eventually_concentration_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ π : V → History 1,
      (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
        {G | ¬Good π (p:ℝ) N G} ≤
        (4*(N:ℝ)+8)*Real.exp (-(3:ℝ)/80*(Real.log (N:ℝ))^2) := by
  filter_upwards [eventually_basic_sparse θ T hθlo hθhi hT,
    FaithfulStep.eventually_day_one_scales_sparse hθlo hθhi hT] with N hb hs
  intro p hp V _ hcard π
  have hN : 0 < (N:ℝ) := by exact_mod_cast hb.1
  exact concentration π (Binomial.closedProbability p) N hcard hN p.property.1
    (by linarith [hb.2.1]) (hs p hp).1 (hs p hp).2.1 (hs p hp).2.2.1 (hs p hp).2.2.2

theorem uniform_concentration_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ π : V → History 1,
      (SimpleGraph.binomialRandom V (Binomial.closedProbability p)).real
        {G | ¬Good π (p:ℝ) N G} ≤ (N:ℝ)^(-(1:ℝ)) := by
  filter_upwards [eventually_concentration_sparse hθlo hθhi hT,
    eventually_failure_decay] with N hp hd
  intro p hpd V _ hcard π
  exact (hp p hpd V hcard π).trans (by simpa only [neg_div] using hd)

end MajorityDynamics.GraphProcess.DayOne

