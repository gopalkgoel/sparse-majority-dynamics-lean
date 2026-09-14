import MajorityDynamics.Literature.LWFormal.Operators

set_option autoImplicit true

/-!
# §7: The approximations `P^gr`, `R^gr`, `Y^gr` and the sets `𝔇`, `Q₁¹`
-/

namespace LW

open Finset Real Filter

variable {n : ℕ}

/-- `ε_i = (d_i - d̄)/d̄`. -/
noncomputable def eps (d : Seq n) (i : Fin n) : ℝ := ((d i : ℝ) - dbar d) / dbar d

/-- `π(x, z, μ, σ², d, n)`. -/
noncomputable def piF (x z μ σ2 d : ℝ) (n : ℕ) : ℝ :=
  μ * (1 + x) * (1 + z) *
    (1 + (-μ * x * z + (x + z) * σ2 / (d * n)) / (1 - μ) + (x + z) / ((n : ℝ) - 1))

/-- `ρ(x, z, μ, σ², d, n)`. -/
noncomputable def rhoF (x z μ σ2 d : ℝ) (n : ℕ) : ℝ :=
  (1 + x) / (1 + z) * ((1 - μ * (1 + z) + 1 / n) / (1 - μ * (1 + x) + 1 / n)) *
    (1 + (x - z) * σ2 / ((1 - μ) ^ 2 * d * n))

/-- `P^gr_{av}(d) = π(ε_a, ε_v)`. -/
noncomputable def Pgr : PFun n := fun a v d =>
  piF (eps d a) (eps d v) (mu d) (sigma2 d) (dbar d) n

/-- `R^gr_{ab}(d) = ρ(ε_a, ε_b)`. -/
noncomputable def Rgr : RFun n := fun a b d =>
  rhoF (eps d a) (eps d b) (mu d) (sigma2 d) (dbar d) n

/-- `Y^gr_{avb}(d) = π(ε_a, ε_v) π(ε_b, ε_v - δ) (1 + (1 + ε_a - μ(1 + ε_a + ε_b))/((n-1)(1-μ)))`,
`δ = 1/d̄`. -/
noncomputable def Ygr : YFun n := fun a v b d =>
  piF (eps d a) (eps d v) (mu d) (sigma2 d) (dbar d) n *
  piF (eps d b) (eps d v - 1 / dbar d) (mu d) (sigma2 d) (dbar d) n *
  (1 + (1 + eps d a - mu d * (1 + eps d a + eps d b)) / (((n : ℝ) - 1) * (1 - mu d)))

/-- Hypotheses of Lemma 7.1 on `d`: `μ(d) < 1/4` and `|dᵢ - d̄| ≤ 2 d̄^α` (the factor `2`
accommodates the `O(log n)`-neighbourhood of `𝔇` used in the proof of (7.4)–(7.5)). -/
def Spread (α : ℝ) (d : Seq n) : Prop :=
  mu d < 1 / 4 ∧ ∀ i, |(d i : ℝ) - dbar d| ≤ 2 * dbar d ^ α

/-- `μ₁ ε⁴ = μ(d) d̄^{4α-4}`. -/
noncomputable def err71 (α : ℝ) (d : Seq n) : ℝ := mu d * dbar d ^ (4 * α - 4)

/-- `𝔇 = 𝔇(n, m, α)`: nonnegative sequences with `∑ dᵢ = 2m` and `|dᵢ - d| ≤ d^α`. -/
def Dset (α : ℝ) (n m : ℕ) : Set (Seq n) :=
  {d | (∀ i, 0 ≤ d i) ∧ M1 d = 2 * m ∧ ∀ i, |(d i : ℝ) - 2 * m / n| ≤ (2 * m / n : ℝ) ^ α}

/-- `Q₁¹`: sequences `d` with `d - e_a ∈ 𝔇` for some `a`. -/
def Q1D (α : ℝ) (n m : ℕ) : Set (Seq n) := {d | ∃ a, d - e a ∈ Dset α n m}

/-- The range of `(n, m)` in Theorem 1.4: `(log n)^{ω(n)} ≤ d ≤ μ₀ n`. -/
def Range (ω : ℕ → ℝ) (μ₀ : ℝ) (n m : ℕ) : Prop :=
  log n ^ ω n ≤ 2 * m / n ∧ (2 * m / n : ℝ) ≤ μ₀ * n

end LW
