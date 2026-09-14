import MajorityDynamics.GraphProcess.FiberTransference.Uniform
import MajorityDynamics.GraphProcess.EnumerationComparison.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
universe u

/-- The exponential graphical history/count/kappa denominator, from original
local admissibility. Its constant is independent of the later Gamma choice. -/
theorem uniform_denominator {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    DenominatorTheorem.{u} θ T n :=
  denominator_of_comparison n hθlo hθhi hT
    (EnumerationComparison.uniform_strong_comparison n hθlo hθhi hT zero_lt_one)

/-- Full B.3 together with B.4 for the same Gamma constant. No statistical
premise survives: B.2, graphical positivity and both tails are proved inputs. -/
theorem uniform_gamma {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    GammaTheorem.{u} θ T φ n :=
  gamma_of_denominator n hθlo hθhi hT hφ (uniform_denominator n hθlo hθhi hT)

/-- The manuscript's positive-probability formulation of B.3. -/
theorem uniform_gamma_lower {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      1-Real.exp (-(N : ℝ)) ≤
        (cond (GraphicalArray.law y.part y.edge)
          (GraphicalArray.historyRegular p y.part)).real
          {d | RowArray.Gamma y.part y.edge C p d} :=
  gamma_lower_of_gamma n hθlo hθhi hT (uniform_gamma n hθlo hθhi hT hφ)

/-- Proposition 3.8: uniform event-wise actual-fiber transference, under only
the original admissibility and density window. -/
theorem uniform_transfer {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    TransferTheorem.{u} θ T φ n :=
  transfer_of_comparison n hθlo hθhi hT hφ
    (fun _ hΓ => EnumerationComparison.uniform_strong_comparison n hθlo hθhi hT hΓ)

theorem uniform_transfer_real {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    TransferRealTheorem.{u} θ T φ n :=
  transfer_real_of_transfer n hθlo hθhi hT (uniform_transfer n hθlo hθhi hT hφ)

end MajorityDynamics.GraphProcess.FiberTransference
