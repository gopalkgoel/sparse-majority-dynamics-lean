import MajorityDynamics.Binomial.GaussianComparisonNoBalance
import MajorityDynamics.Binomial.SparseRange

/-!
# Gaussian comparison on a one-sided sparse range

This is the A.2 Gaussian endpoint with constants uniform for every
`T⁻¹ N⁻θ < p < T N⁻¹/²`.  There is no balance restriction on the translated
inequalities.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators

namespace MajorityDynamics.Binomial.Approximation

def GaussianComparisonSparseTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → ∀ d : ℕ, 0 < d →
  ∀ r : ℕ, ∀ M : Fin r → Fin d → ℤ, OrthogonalRows M →
  ∀ strict : Fin r → Bool, ∀ c : ℝ, ∀ e : Fin d → ℕ,
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : Probability,
  SparseRange θ T N p → ∀ η : Fin d → ℕ, Sizes T N η →
  ∀ α : Fin d → ℝ, (∀ i, |α i| < T) →
  |(∫ a in inequalityEvent (fun j i => (M j i : ℝ)) strict,
      monomial c e (centered p η a) ∂law η (gaussianTilt p η α)) -
    (∫ x in gaussianEvent M p η, monomial c e x ∂gaussianLaw p η α)| ≤
      C * (scale N p) ^ (((∑ i, e i : ℕ) : ℝ) - 1) *
        (Real.log N) ^ (3 + (∑ i, e i) + d)

set_option maxHeartbeats 1200000 in
theorem gaussian_comparison_sparse : GaussianComparisonSparseTheorem := by
  intro θ T _hθlo hθhi hT d hd r M hM strict c e
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
  have hevent := (eventually_sparseRange_window θ T d hθhi hT0).and
    (polynomial_log_tail A (2 * (32 * T + 4)) (2 * D + 1) hA (by positivity))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨N₀, ?_⟩
  intro N hN p hp η hη α hα
  obtain ⟨⟨hNpos, hlog, hscales⟩, htailpoly⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  let s := scale N p
  let l := Real.log (N : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos p.property.1 hN0)
  have hsquare : s ^ 2 = (p : ℝ) * N :=
    Real.sq_sqrt (mul_nonneg p.property.1.le hN0.le)
  have hl1 : 1 ≤ l := by dsimp [l]; nlinarith
  have hηlo : ∀ i, (N : ℝ) / T ≤ η i := by
    intro i
    simpa only [div_eq_mul_inv, mul_comm] using (hη i).1.le
  have hw := gaussian_uniform_inputs p η α T N s l hd hT.le hN0 hs hlog hsquare
    (hscales p hp).2.2.1 (hscales p hp).2.1 (hscales p hp).1 hηlo
    (fun i => (hη i).2.le) (fun i => (hα i).le)
  have hsN : s ≤ N := by
    apply (Real.sqrt_le_left hN0.le).mpr
    have hh := mul_le_mul_of_nonneg_right p.property.2.le hN0.le
    nlinarith
  have hls : l ≤ s := by
    have hlarge := (hscales p hp).1
    have hconst : 1 ≤ 1024 * ((d : ℝ) + 1) * (T + 1) ^ 2 := by
      nlinarith [sq_nonneg T]
    have hl3 : l ≤ l ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg l) (show 0 ≤ l - 1 by linarith)]
    have hh := mul_le_mul_of_nonneg_right hconst (show 0 ≤ l ^ 3 by positivity)
    exact hl3.trans (by simpa only [one_mul] using hh.trans hlarge)
  have hs1 : 1 ≤ s := hl1.trans hls
  have hlN : l ≤ N := hls.trans hsN
  have hwindow := gaussian_window_comparison M strict p η α c e (s * l) (T * N)
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
  have htail := tail_gaussian_error |c| d T N s l K
    ((law η (gaussianTilt p η α)).real
      (rectangle (fun i => (p : ℝ) * η i) (fun _ => s * l))ᶜ)
    ((gaussianLaw p η α).real (gaussianCellWindow p η (s * l))ᶜ)
    (∫ x, monomial c e x ^ 2 ∂gaussianLaw p η α)
    (Real.exp (-(l ^ 2) / (2 * (32 * T + 4)))) D
    (abs_nonneg _) hd0 hT0.le hN1 hs1 hsN hl1 hlN hK ht.1 ht.2.1 htbin htgauss hmoment
  have htail' := htail.trans htailpoly
  have henv := gaussian_envelope s l N D d hs1 hl1 hsN
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
