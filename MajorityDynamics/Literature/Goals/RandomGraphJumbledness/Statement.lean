import MajorityDynamics.Probability.RandomGraph.Basic

/-!
# Accepted random-graph jumbledness input

Source: Krivelevich–Sudakov, `Pseudo-random graphs`, Corollary 2.3,
arXiv:math/0503745v1, printed p. 4; restated as CKLT21 Lemma 4.1,
arXiv:2105.12709v1, printed p. 15.
https://arxiv.org/pdf/math/0503745v1#page=4
https://arxiv.org/pdf/2105.12709v1#page=15

We import only the sufficiently dense specialization `log(N)^2 ≤ pN`,
`p ≤ 0.99`. The printed shorthand with only an upper bound on `p` should
not be axiomatized for arbitrarily sparse sequences: small expected degree
does not control maximum degree by an absolute multiple of `pN`.
Our paper's polynomial regime satisfies the added lower bound, as proved
at the application. The absolute discrepancy constant is chosen before ε;
the failure estimate is uniform over the displayed density range. Edges
inside the overlap of the two sets are counted twice, exactly as in KS06.
Only jumbledness is imported, not minimum degree or `Pseudorandomness`.
-/

namespace MajorityDynamics.Literature

open MajorityDynamics.Paper

def RandomGraphJumbledness : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : unitInterval,
      (p : ℝ) ≤ 99 / 100 → (Real.log (N : ℝ)) ^ 2 ≤ (p : ℝ) * N →
      graphLaw N p {G | Jumbled G p (C * Real.sqrt ((p : ℝ) * N))}ᶜ ≤
        ENNReal.ofReal ε


end MajorityDynamics.Literature
