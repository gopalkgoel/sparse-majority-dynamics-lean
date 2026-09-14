import MajorityDynamics.Literature.LWFormal.Bip.Defs

set_option autoImplicit true

/-!
# Theorem 1.1 of Liebenau–Wormald (RSA 62 (2023), 259–286), bipartite case

> Let `μ₀ > 0` be sufficiently small and `1/2 < φ < 3/5`. Let `ℓ, n, m` be integers with
> `m/(nℓ) < μ₀`, `(ℓ+n)^{5-5φ} = o(ℓ n m^{3-5φ})` and `ℓ log^K n + n log^K ℓ = o(m)` for every
> fixed `K > 0`. Let `𝔇` be the set of sequences `(s, t)` with `∑ s_a = ∑ t_v = m`,
> `|s_a - s| ≤ s^φ`, `|t_v - t| ≤ t^φ`, where `s = m/ℓ`, `t = m/n`. Then uniformly for `d ∈ 𝔇`,
>   `P_{𝒟(𝒢(ℓ,n,m))}(d) = P_{ℬ_m}(d) H̃(d) (1 + O(log²ℓ/√ℓ + log²n/√n + min{s,t}^{5φ-5} m²/(ℓn)))`.

Asymptotics are as `n → ∞`.  As for Theorem 1.4, the `o(·)` hypotheses are made explicit through
an arbitrary `ω : ℕ → ℝ` tending to infinity: `ω(n) (ℓ+n)^{5-5φ} ≤ ℓ n m^{3-5φ}` and
`ℓ (log n)^{ω(n)} + n (log ℓ)^{ω(n)} ≤ m`.  The constant `C` may depend on `φ`, `μ₀`, `ω`.
-/

namespace LW.Bip

open Filter Real

/-- The error term `log²ℓ/√ℓ + log²n/√n + min{s,t}^{5φ-5} m²/(ℓn)`. -/
noncomputable def err11 (φ : ℝ) (ℓ n m : ℕ) : ℝ :=
  log ℓ ^ 2 / √ℓ + log n ^ 2 / √n +
    (min (m / ℓ : ℝ) (m / n)) ^ (5 * φ - 5) * m ^ 2 / (ℓ * n)

/-- `(s, t) ∈ 𝔇`: `∑ s_a = ∑ t_v = m`, `|s_a - s| ≤ s^φ`, `|t_v - t| ≤ t^φ`. -/
def InD (φ : ℝ) (ℓ n m : ℕ) (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : Prop :=
  ∑ a, s a = m ∧ ∑ v, t v = m ∧
    (∀ a, |(s a : ℝ) - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ) ∧ ∀ v, |(t v : ℝ) - m / n| ≤ (m / n : ℝ) ^ φ

/-- The statement of Theorem 1.1 (bipartite case). -/
def Theorem11 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧
    ∀ φ : ℝ, 1 / 2 < φ → φ < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ℓ m : ℕ,
          (m / (n * ℓ) : ℝ) < μ₀ →
          ω n * ((ℓ : ℝ) + n) ^ (5 - 5 * φ) ≤ ℓ * n * (m : ℝ) ^ (3 - 5 * φ) →
          (ℓ : ℝ) * log n ^ ω n + n * log ℓ ^ ω n ≤ m →
            ∀ (s : Fin ℓ → ℕ) (t : Fin n → ℕ), InD φ ℓ n m s t →
              ∃ θ : ℝ, |θ| ≤ C * err11 φ ℓ n m ∧
                probG ℓ n m s t = probB ℓ n m s t * Htilde s t * (1 + θ)

/-!
## Theorem 1.5 (bipartite case)

> Let `n, ℓ, m` and `𝔇` be as in Theorem 1.1 and `G = 𝒢(ℓ,n,m)`. Let `a ∈ S`, `v ∈ T`. Then
> uniformly for `d = (s, t) ∈ 𝔇`, the probability that `av` is an edge of `G ∈ 𝒢`, conditional on
> `𝒟(G) = d`, is
>   `(s_a t_v / m) (1 - (s_a - s)(t_v - t)/(m - ts) + (s_a - s)σ²(t)/(ts(ℓ - t))`
>     `+ (t_v - t)σ²(s)/(ts(n - s)) + O(min{s,t}^{4φ-4} m/(nℓ)))`,
> where `s = m/ℓ`, `t = m/n`.
-/

/-- `P(av ∈ G | 𝒟(G) = (s, t))` for `G` uniform in `𝒢(ℓ,n,m)`. -/
noncomputable def probEdge (ℓ n m : ℕ) (s : Fin ℓ → ℕ) (t : Fin n → ℕ) (a : Fin ℓ) (v : Fin n) :
    ℝ :=
  prob (Gm ℓ n m) (fun E => ldeg E = s ∧ rdeg E = t ∧ (a, v) ∈ E) / probG ℓ n m s t

/-- The main term of Theorem 1.5: the bracket `1 - … + … + …`. -/
noncomputable def edgeBracket (ℓ n m : ℕ) (s : Fin ℓ → ℕ) (t : Fin n → ℕ) (a : Fin ℓ) (v : Fin n) :
    ℝ :=
  1 - ((s a : ℝ) - m / ℓ) * ((t v : ℝ) - m / n) / (m - (m / n : ℝ) * (m / ℓ)) +
    ((s a : ℝ) - m / ℓ) * var t / ((m / n : ℝ) * (m / ℓ) * (ℓ - m / n)) +
    ((t v : ℝ) - m / n) * var s / ((m / n : ℝ) * (m / ℓ) * (n - m / ℓ))

/-- The error term `min{s,t}^{4φ-4} m/(nℓ)`. -/
noncomputable def err15 (φ : ℝ) (ℓ n m : ℕ) : ℝ :=
  (min (m / ℓ : ℝ) (m / n)) ^ (4 * φ - 4) * m / (n * ℓ)

/-- The statement of Theorem 1.5 (bipartite case). -/
def Theorem15 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧
    ∀ φ : ℝ, 1 / 2 < φ → φ < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ℓ m : ℕ,
          (m / (n * ℓ) : ℝ) < μ₀ →
          ω n * ((ℓ : ℝ) + n) ^ (5 - 5 * φ) ≤ ℓ * n * (m : ℝ) ^ (3 - 5 * φ) →
          (ℓ : ℝ) * log n ^ ω n + n * log ℓ ^ ω n ≤ m →
            ∀ (s : Fin ℓ → ℕ) (t : Fin n → ℕ), InD φ ℓ n m s t →
              ∀ (a : Fin ℓ) (v : Fin n), ∃ θ : ℝ, |θ| ≤ C * err15 φ ℓ n m ∧
                probEdge ℓ n m s t a v =
                  (s a : ℝ) * t v / m * (edgeBracket ℓ n m s t a v + θ)

end LW.Bip
