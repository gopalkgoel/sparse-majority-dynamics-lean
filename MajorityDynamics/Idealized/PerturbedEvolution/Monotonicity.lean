import MajorityDynamics.Idealized.PerturbedEvolution.Basic

/-! Combining uniform comparison constants without changing the reference process. -/
noncomputable section
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt

theorem error_mono {N : ℕ} {C D a d e : ℝ} (hN : 1 ≤ N)
    (hC : 0 ≤ C) (hCD : C ≤ D) (ha : 0 ≤ a) (hed : e ≤ d) :
    C * a * (N : ℝ) ^ (-d) ≤ D * a * (N : ℝ) ^ (-e) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hCD ha)
    (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hed))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (hC.trans hCD) ha)

theorem tiltConclusion_mono {n N : ℕ} {p : Binomial.Probability} {a : Process.Data}
    {η : History (n + 1) → ℤ} {e : History (n + 1) → History (n + 1) → ℤ}
    {τ C D d f : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hCD : C ≤ D) (hfd : f ≤ d)
    (h : TiltConclusion N p a n η e τ C d) : TiltConclusion N p a n η e τ D f := by
  refine ⟨h.sizes_pos, h.sizes_cast, h.trials_cast, h.reference_residual_pos,
    h.residual_pos, h.exists_unique, ?_⟩
  intro q hq
  obtain ⟨hm, hd, hr, he⟩ := h.approximation q hq
  refine ⟨hm, hd, hr, fun s t => (he s t).trans ?_⟩
  exact error_mono hN hC hCD (by unfold betaScale; positivity) hfd

theorem templateConclusion_mono {n N : ℕ} {p : ℝ} {a : Process.Data}
    {sizes : Local.Sizes n} {e : Local.EdgeCounts n} {q : Local.Tilt n}
    {τ C D d f : ℝ} (hN : 1 ≤ N) (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hCD : C ≤ D) (hfd : f ≤ d)
    (h : TemplateConclusion N p a sizes e q τ C d) :
    TemplateConclusion N p a sizes e q τ D f := by
  refine ⟨fun u => (h.sizes u).trans ?_, fun u v => (h.edges u v).trans ?_⟩
  · exact error_mono hN hC hCD (sizeScale_nonneg _ _ _) hfd
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (error_mono hN hC hCD (by unfold betaScale; positivity) hfd) (sq_nonneg _)) hp

end MajorityDynamics.Idealized.PerturbedEvolution
