import MajorityDynamics.Literature.EdgeProbabilities.Basic

/-!
# Corrected graph-edge asymptotic theorem

LW17: the corrected full expansion underlying Theorem 1.6, under Theorem 1.4.
The printed square-root error is false on this degree domain. The proved input
uses its valid O(D/n²) corollary; the full expansion is retained in LWFormal.
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

def GraphEdgeProbabilityTheorem : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
    ∀ n m : ℕ → ℕ,
      Tendsto n atTop atTop →
      (∀ᶠ k in atTop, graphDensity (n k) (m k) ≤ μ₀) →
      (∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
        (fun k => (Real.log (n k)) ^ K / (n k : ℝ))
        (fun k => graphDensity (n k) (m k))) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop, ∀ (V : Type u) [Fintype V] (d : V → ℕ),
        GraphConditions (n k) (m k) α d → ∀ a b : V, a ≠ b →
          |(fixedDegreeLaw d).real {G | G.Adj a b} -
            graphApproximation (n k) (m k) (d a) (d b)| ≤
              C * graphErrorScale (n k) (m k)

end MajorityDynamics.Literature.EdgeProbabilities
