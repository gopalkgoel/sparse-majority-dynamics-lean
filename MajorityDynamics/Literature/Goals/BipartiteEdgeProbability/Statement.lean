import MajorityDynamics.Literature.EdgeProbabilities.Basic

/-!
# Two cited single-edge asymptotic imports

LW17: Liebenau–Wormald, arXiv:1702.08373v3, Theorem 1.6 under Theorem 1.4.
LW20: Liebenau–Wormald, arXiv:2006.15797v1, Theorem 1.5 under Theorem 1.1,
restricted to the bipartite case (`delta_di = 0`).

The growth assumptions are genuine little-o conditions along arbitrary size/total
sequences. The O constant may depend on those sequences. The eventual index precedes
all degree vectors and queried vertices. Restriction to realizable families is a
weaker use of the cited results and ensures that the displayed actual laws are
probability laws. All finite-window and residual applications are proved elsewhere.
-/
noncomputable section
open MeasureTheory Filter
open scoped Classical Topology
namespace MajorityDynamics.Literature.EdgeProbabilities
open MajorityDynamics.Probability.FixedDegreeSampling
universe u v

def BipartiteEdgeProbabilityTheorem : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
    ∀ ell n m : ℕ → ℕ,
      Tendsto n atTop atTop → Tendsto ell atTop atTop →
      (∀ᶠ k in atTop, bipartiteDensity (ell k) (n k) (m k) < μ₀) →
      Asymptotics.IsLittleO atTop
        (fun k => ((ell k : ℝ) + n k) ^ (5 - 5 * α))
        (fun k => (ell k : ℝ) * n k * (m k : ℝ) ^ (3 - 5 * α)) →
      (∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
        (fun k => (ell k : ℝ) * (Real.log (n k)) ^ K +
          (n k : ℝ) * (Real.log (ell k)) ^ K)
        (fun k => (m k : ℝ))) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop, ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
        (a : L → ℕ) (b : R → ℕ), BipartiteConditions (ell k) (n k) (m k) α a b →
          ∀ i : L, ∀ j : R,
            |(bipartiteFixedDegreeLaw a b).real {E | (i, j) ∈ E} -
              bipartiteApproximation (ell k) (n k) (m k) a b i j| ≤
                bipartitePrefactor (m k) (a i) (b j) *
                  (C * bipartiteErrorScale (ell k) (n k) (m k) α)

end MajorityDynamics.Literature.EdgeProbabilities
