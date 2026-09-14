import MajorityDynamics.Binomial.GaussianUniformInputs
import MajorityDynamics.Binomial.GaussianAggregateError
import MajorityDynamics.Binomial.GaussianEnvelope

/-! # Appendix A.2: the full uniform polynomial Gaussian comparison -/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation

set_option maxHeartbeats 1200000 in
/-- The original Gaussian comparison, with uniform constants, actual product
laws, and literal mixed inequalities. Only scalar Chernoff is imported. -/
theorem gaussian_comparison : GaussianComparisonTheorem := by
  intro θ T hθlo hθhi hT d hd r M hM strict c e
  let D := ∑ i, e i
  let B := 2 * T * ∑ j, ∑ i, |(M j i : ℝ)|
  let K := monomialMomentConstant T c e
  let Cfin := |c| * 2 ^ D * (128 * d * T ^ 2 + 256 * d * T + (D : ℝ) + 2 * B)
  let A := 4 * |c| * T ^ D * d + Real.sqrt K * T ^ D * Real.sqrt (2 * d) +
    2 * |c| * 2 ^ D * d + 1
  have hT0 : 0 < T := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := monomialMomentConstant_nonneg T c e hT0.le
  have hCfin : 0 ≤ Cfin := by dsimp [Cfin]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨Cfin + 2, by positivity, ?_⟩
  have hevent := (eventually_gaussian_window θ T d hθlo hθhi hT0).and
    (polynomial_log_tail A (2 * (32 * T + 4)) (2 * D + 1) hA (by positivity))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hevent
  refine ⟨n₀, ?_⟩
  intro n hn p hp η hη _hbalance α hα
  obtain ⟨⟨hnpos, hlog, hscales⟩, htailpoly⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  let s := scale n p
  let l := Real.log (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos p.property.1 hn0)
  have hsquare : s ^ 2 = (p : ℝ) * n := Real.sq_sqrt (mul_nonneg p.property.1.le hn0.le)
  have hl1 : 1 ≤ l := by dsimp [l]; nlinarith
  have hηlo : ∀ i, (n : ℝ) / T ≤ η i := by
    intro i
    simpa only [div_eq_mul_inv, mul_comm] using (hη i).1.le
  have hw := gaussian_uniform_inputs p η α T n s l hd hT.le hn0 hs hlog hsquare
    (hscales p hp).2.2 (hscales p hp).2.1 (hscales p hp).1 hηlo
    (fun i => (hη i).2.le) (fun i => (hα i).le)
  have hsn : s ≤ n := by
    apply (Real.sqrt_le_left hn0.le).mpr
    have hh := mul_le_mul_of_nonneg_right p.property.2.le hn0.le
    nlinarith
  have hls : l ≤ s := by
    have hlarge := (hscales p hp).1
    have hconst : 1 ≤ 1024 * ((d : ℝ) + 1) * (T + 1) ^ 2 := by nlinarith [sq_nonneg T]
    have hl3 : l ≤ l ^ 3 := by nlinarith [mul_nonneg (sq_nonneg l) (show 0 ≤ l - 1 by linarith)]
    have hh := mul_le_mul_of_nonneg_right hconst (show 0 ≤ l ^ 3 by positivity)
    exact hl3.trans (by simpa only [one_mul] using hh.trans hlarge)
  have hs1 : 1 ≤ s := hl1.trans hls
  have hln : l ≤ n := hls.trans hsn
  have hwindow := gaussian_window_comparison M strict p η α c e (s * l) (T * n)
    (8 * T * l / s) (by linarith [hw.hL]) (by positivity) hw.hη hw.hηR
    hw.hcomp hw.hsucc hw.hpointSmall (by positivity) hw.epsSmall hw.cellSmall hw.hcell
  dsimp only at hwindow
  have hboundary := gaussian_boundary_le M p η α T s hT.le hs hw.hvarlo hM.1
  have hmoment := gaussian_second_moment_le p η α c e T (T * s) hT0.le
    (by positivity) (fun i => (hα i).le) hw.hsqrt
  have hfinite := finite_gaussian_error |c| d T s l B
    (gaussianWindowError p η (fun _ => s * l)) (8 * T * l / s)
    ((gaussianLaw p η α).real (gaussianBoundary M p η)) D
    (abs_nonneg _) hd0 hT0.le hs1 hl1 hB hw.hpointBound le_rfl hboundary
  have ht := gaussian_tail_envelope l (32 * T + 4) (by positivity)
  have htbin := hw.htailBin
  have htgauss := hw.htailGauss
  rw [ht.2.2] at htbin htgauss
  have htail := tail_gaussian_error |c| d T n s l K
    ((law η (gaussianTilt p η α)).real (rectangle (fun i => (p : ℝ) * η i) (fun _ => s * l))ᶜ)
    ((gaussianLaw p η α).real (gaussianCellWindow p η (s * l))ᶜ)
    (∫ x, monomial c e x ^ 2 ∂gaussianLaw p η α)
    (Real.exp (-(l ^ 2) / (2 * (32 * T + 4)))) D
    (abs_nonneg _) hd0 hT0.le hn1 hs1 hsn hl1 hln hK ht.1 ht.2.1 htbin htgauss hmoment
  have htail' := htail.trans htailpoly
  have henv := gaussian_envelope s l n D d hs1 hl1 hsn
  have henvfin := mul_le_mul_of_nonneg_left henv.1 hCfin
  rw [← mul_assoc] at henvfin
  have hfinite' := hfinite.trans henvfin
  have hsum : (∑ i, (e i : ℝ)) = (D : ℝ) := by simp [D]
  rw [hsum] at hwindow
  change _ ≤ Cfin * (s ^ D / s) * l ^ (D + 3) at hfinite
  have henv0 : 0 ≤ s ^ ((D : ℝ) - 1) * l ^ (3 + D + d) := by positivity
  change _ ≤ (Cfin + 2) * s ^ ((D : ℝ) - 1) * l ^ (3 + D + d)
  dsimp only [D] at hfinite' htail' henv henv0 ⊢
  nlinarith only [hwindow, hfinite', htail', henv.2, henv0]

end MajorityDynamics.Binomial.Approximation
