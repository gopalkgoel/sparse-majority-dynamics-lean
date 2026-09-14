import MajorityDynamics.Literature.LWFormal.Defs

set_option autoImplicit true

/-!
# Theorem 1.4 of Liebenau–Wormald (JEMS 26 (2024), 1–60)

> Let `μ₀ > 0` be a sufficiently small constant, and let `1/2 < α < 3/5`. Let `n` and `m` be
> integers, and assume that `d = 2m/n` satisfies `(log n)^ω ≤ d ≤ μ₀ n`. Let `𝔇` be the set of
> sequences `𝐝` of length `n` satisfying `∑ᵢ dᵢ = 2m` and `|dᵢ - d| ≤ d^α` for all `i ∈ [n]`.
> Then uniformly for all `𝐝 ∈ 𝔇` we have
>   `P_{𝒟(𝒢(n,m))}(𝐝) = P_{ℬ_m}(𝐝) exp(1/4 - γ₂²/(4μ²(1-μ)²)) (1 + O((log n)²/√n + d^{5α-3}))`,
> where `μ = μ(𝐝) = d/(n-1)` and `γ₂ = γ₂(𝐝)`.

Here `ω` is an arbitrary function of `n` tending to infinity.  The implicit constant in `O(·)`
is allowed to depend on `α`, `μ₀` and `ω`, but not on `n`, `m`, or `𝐝`.
-/

namespace LW

open Filter Real

/-- The error term `(log n)²/√n + d^{5α-3}`. -/
noncomputable def err14 (α : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  Real.log n ^ 2 / Real.sqrt n + d ^ (5 * α - 3)

/-- Sequence `𝐝 ∈ 𝔇`: `∑ dᵢ = 2m` and `|dᵢ - d| ≤ d^α` for all `i`, where `d = 2m/n`. -/
def InD (α : ℝ) (n m : ℕ) (d : Fin n → ℕ) : Prop :=
  ∑ i, d i = 2 * m ∧ ∀ i, |(d i : ℝ) - 2 * m / n| ≤ (2 * m / n : ℝ) ^ α

/-- The statement of Theorem 1.4; proved as `theorem_1_4` in `LWFormal.Final`. -/
def Theorem14 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧
    ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
          Real.log n ^ ω n ≤ 2 * m / n → (2 * m / n : ℝ) ≤ μ₀ * n →
            ∀ d : Fin n → ℕ, InD α n m d →
              ∃ θ : ℝ, |θ| ≤ C * err14 α n (2 * m / n) ∧
                probGnm n m d = probBinom n m d * expFactor d * (1 + θ)

/-!
## Theorem 1.6

> Let `𝔇` be as in Theorem 1.4 and let `a, b ∈ [n]`, `a ≠ b`. Then for all `𝐝 ∈ 𝔇`,
>   `P_{ab}(𝐝) = (d_a d_b / (d(n-1))) (1 - (d_a-d)(d_b-d)/(d(n-1-d)))`
>     `+ O(√(d log n)/n² + (√(d log n))³/n³)`,
> where `P_{ab}(𝐝)` is the probability that `v_a v_b` is an edge of a uniformly random graph with
> degree sequence `𝐝`.

As printed, the statement is not correct over the whole of `𝔇`: the proof (Lemma 7.1(b), (7.4))
gives `P_{ab} = π(1 + O(μ d^{4α-4}))` with `π = μ(1+ε_a)(1+ε_b)(1 + (-με_aε_b + (ε_a+ε_b)σ²/(dn))/(1-μ)
+ (ε_a+ε_b)/(n-1))`, and the terms in `ε_a + ε_b` contribute `≍ d^α/n²` to `P_{ab}` (e.g. for
`d_a = d_b = d + d^α`), larger than the printed error whenever `α > 1/2`.  We therefore state two
versions:

* `Theorem16`: the by-product of the proof, on `𝔇` of Theorem 1.4, in the same form as
  Theorem 1.5 of the bipartite paper — the bracket keeps the `ε_a + ε_b` terms and the error is
  `O(μ d^{4α-4}) = O(d^{4α-3}/n)`;
* `Theorem16'`: the formula and error term exactly as printed, on the set `𝔇` of Theorem 6.3
  (`|dᵢ - d| ≤ C₀ √(d log n)`, `σ²(𝐝) ≤ 2d`), where the omitted terms are `O(√(d log n)/n²)`.
-/

/-- `P(ab ∈ G | 𝒟(G) = 𝐝)` for `G` uniform in `𝒢(n,m)`. -/
noncomputable def probEdge (n m : ℕ) (d : Fin n → ℕ) (a b : Fin n) : ℝ :=
  prob (Gnm n m) (fun E => degSeq E = d ∧ s(a, b) ∈ E) / probGnm n m d

/-- `σ²(𝐝) = n⁻¹ ∑ (dᵢ - d)²`. -/
noncomputable def var (d : Fin n → ℕ) : ℝ := (∑ i, ((d i : ℝ) - avgDeg d) ^ 2) / n

/-- The main factor `d_a d_b / (d(n-1))`, `d = 2m/n`. -/
noncomputable def edgeMain (n m : ℕ) (d : Fin n → ℕ) (a b : Fin n) : ℝ :=
  (d a : ℝ) * d b / ((2 * m / n : ℝ) * (n - 1))

/-- The printed bracket `1 - (d_a-d)(d_b-d)/(d(n-1-d))`. -/
noncomputable def edgeBracket0 (n m : ℕ) (d : Fin n → ℕ) (a b : Fin n) : ℝ :=
  1 - ((d a : ℝ) - 2 * m / n) * ((d b : ℝ) - 2 * m / n) / ((2 * m / n : ℝ) * (n - 1 - 2 * m / n))

/-- The full bracket of (7.4): the printed one plus
`(d_a+d_b-2d)(n-1)σ²/(d²n(n-1-d)) + (d_a+d_b-2d)/(d(n-1))`. -/
noncomputable def edgeBracket (n m : ℕ) (d : Fin n → ℕ) (a b : Fin n) : ℝ :=
  edgeBracket0 n m d a b +
    ((d a : ℝ) + d b - 2 * (2 * m / n)) * (n - 1) * var d /
      ((2 * m / n : ℝ) ^ 2 * n * (n - 1 - 2 * m / n)) +
    ((d a : ℝ) + d b - 2 * (2 * m / n)) / ((2 * m / n : ℝ) * (n - 1))

/-- The error term `μ d^{4α-4} ≍ d^{4α-3}/n`. -/
noncomputable def err16 (α : ℝ) (n : ℕ) (d : ℝ) : ℝ := d ^ (4 * α - 3) / n

/-- Theorem 1.6 as it follows from the proof: `𝔇` of Theorem 1.4, full bracket, error `O(d^{4α-3}/n)`. -/
def Theorem16 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧
    ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
          Real.log n ^ ω n ≤ 2 * m / n → (2 * m / n : ℝ) ≤ μ₀ * n →
            ∀ d : Fin n → ℕ, InD α n m d → ∀ a b : Fin n, a ≠ b →
              ∃ θ : ℝ, |θ| ≤ C * err16 α n (2 * m / n) ∧
                probEdge n m d a b = edgeMain n m d a b * (edgeBracket n m d a b + θ)

/-- `𝐝 ∈ 𝔇` of Theorem 6.3: `∑ dᵢ = 2m`, `|dᵢ - d| ≤ C₀ √(d log n)`, `σ²(𝐝) ≤ 2d`. -/
def InD6 (C₀ : ℝ) (n m : ℕ) (d : Fin n → ℕ) : Prop :=
  ∑ i, d i = 2 * m ∧ (∀ i, |(d i : ℝ) - 2 * m / n| ≤ C₀ * √(2 * m / n * Real.log n)) ∧
    var d ≤ 2 * (2 * m / n)

/-- The printed error term `√(d log n)/n² + (d log n)^{3/2}/n³`. -/
noncomputable def err16' (n : ℕ) (d : ℝ) : ℝ :=
  √(d * Real.log n) / n ^ 2 + √(d * Real.log n) ^ 3 / n ^ 3

/-- Theorem 1.6 exactly as printed, on `𝔇` of Theorem 6.3. -/
def Theorem16' : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧
    ∀ C₀ : ℝ, ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
      ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
        Real.log n ^ ω n ≤ 2 * m / n → (2 * m / n : ℝ) ≤ μ₀ * n →
          ∀ d : Fin n → ℕ, InD6 C₀ n m d → ∀ a b : Fin n, a ≠ b →
            ∃ θ : ℝ, |θ| ≤ C * err16' n (2 * m / n) ∧
              probEdge n m d a b = edgeMain n m d a b * edgeBracket0 n m d a b + θ

end LW
