import MajorityDynamics.Analysis.Perturbation.Basic
import Mathlib.Tactic.Ring

/-!
# Uniform constants for the perturbation theorem

Source: `thm:perturbed-bijection`. This reduction exposes the local argument,
compact control and prescribed-radius bound; `Main.lean` supplies their proofs.
The constants are chosen before the error, perturbation and target point.
-/

noncomputable section

open Set

namespace MajorityDynamics.Analysis.Perturbation

variable {d : ℕ} {B : Set (Space d)}

/-- The paper's uniform choice ε₀ = min(r/C₀, 1/(LC₀)), C = LC₀. -/
theorem perturbationAt_of_control (hl : LocalPerturbationTheorem)
    (f : StrongBijection B) (K : Set (Space d)) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hc : CompactControl f K)
    (hR : ∀ y ∈ K, ‖f.invFun y‖ + 1 ≤ inverseRadius f K) :
    PerturbationAt f K C₀ := by
  obtain ⟨V, r, L, _hVc, hKV, hVB, hr, hL, hnear, hLip⟩ := hc
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hLC : 0 < L * C₀ := mul_pos hLp hC₀
  refine ⟨min (r / C₀) (1 / (L * C₀)),
    lt_min (div_pos hr hC₀) (div_pos zero_lt_one hLC),
    L * C₀, hLC, ?_⟩
  intro ε hε hεsmall g hg hclose y hy
  have hεr : ε * C₀ < r :=
    (lt_div_iff₀ hC₀).mp (hεsmall.trans_le (min_le_left _ _))
  have hεL : ε * (L * C₀) < 1 :=
    (lt_div_iff₀ hLC).mp (hεsmall.trans_le (min_le_right _ _))
  have hδr : C₀ * ε < r := by simpa [mul_comm] using hεr
  have hLδ : L * (C₀ * ε) ≤ 1 := by
    calc
      L * (C₀ * ε) = ε * (L * C₀) := by ring
      _ ≤ 1 := hεL.le
  obtain ⟨x, hx, hbound⟩ := hl d B f V y r L (inverseRadius f K) (C₀ * ε)
    hVB (hKV hy) hr hLp.le (mul_pos hC₀ hε).le (hnear y hy) hLip
    (hR y hy) hδr hLδ g hg hclose
  exact ⟨x, hx, by simpa [mul_assoc] using hbound⟩

end MajorityDynamics.Analysis.Perturbation
