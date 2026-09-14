import MajorityDynamics.Literature.LWFormal.Bip.Operators
import MajorityDynamics.Literature.LWFormal.Shift

set_option autoImplicit true

/-!
# §4: The approximations `P*`, `R*`, `Y*` for bipartite graphs
-/

namespace LW.Bip

open Finset Real

variable {ℓ n : ℕ}

/-- `μ(d) = (M₁(s) + M₁(t)) / (2ℓn)`. -/
noncomputable def mu (d : BSeq ℓ n) : ℝ := ((M1 d.1 : ℝ) + M1 d.2) / (2 * ℓ * n)

/-- `σ_S²/(s̄ n)`. -/
noncomputable def sS (d : BSeq ℓ n) : ℝ := sigma2 d.1 / (dbar d.1 * n)

/-- `σ_T²/(t̄ ℓ)`. -/
noncomputable def sT (d : BSeq ℓ n) : ℝ := sigma2 d.2 / (dbar d.2 * ℓ)

/-- `π = μ(1+x)(1+y)(1 + AcorrB)`, `AcorrB = (-μxy + x σ_T²/(t̄ℓ) + y σ_S²/(s̄n))/(1-μ)`. -/
noncomputable def AcorrB (μ sS sT x y : ℝ) : ℝ := (-μ * x * y + x * sT + y * sS) / (1 - μ)

noncomputable def piB (μ sS sT x y : ℝ) : ℝ := μ * (1 + x) * (1 + y) * (1 + AcorrB μ sS sT x y)

/-- The correction factor of `Y*`: `Y* = π π' (1 + TcB)`, `δT = 1/t̄`. -/
noncomputable def TcB (μ δT xa xb : ℝ) : ℝ := δT * (μ * (1 + xa) - μ ^ 2 * (1 + xa + xb)) / (1 - μ)

/-- `ρ(x, z)` with `δS = 1/s̄`, `λ = 1/ℓ`. -/
noncomputable def rhoB (μ δS sT lam x z : ℝ) : ℝ :=
  (1 + x) / (1 + z) * ((1 - μ * (1 + z) + μ * δS) / (1 - μ * (1 + x) + μ * δS)) *
    (1 + (x - z) * (sT / (1 - μ) - lam) / (1 - μ))

noncomputable def Pst : PFun ℓ n := fun a v d =>
  piB (mu d) (sS d) (sT d) (eps d.1 a) (eps d.2 v)

noncomputable def Rst : RFun ℓ n := fun a b d =>
  rhoB (mu d) (1 / dbar d.1) (sT d) (1 / ℓ) (eps d.1 a) (eps d.1 b)

noncomputable def Yst : YFun ℓ n := fun a v b d =>
  Pst a v d * piB (mu d) (sS d) (sT d) (eps d.1 b) (eps d.2 v - 1 / dbar d.2) *
    (1 + TcB (mu d) (1 / dbar d.2) (eps d.1 a) (eps d.1 b))

/-- Hypotheses of Lemma 4.1 on `d`: `μ(d) < 1/4`, `|s_a - s̄| ≤ 2 s̄^φ`, `|t_v - t̄| ≤ 2 t̄^φ`. -/
def Spread (φ : ℝ) (d : BSeq ℓ n) : Prop :=
  mu d < 1 / 4 ∧ (∀ a, |(d.1 a : ℝ) - dbar d.1| ≤ 2 * dbar d.1 ^ φ) ∧
    ∀ v, |(d.2 v : ℝ) - dbar d.2| ≤ 2 * dbar d.2 ^ φ

/-- `d̄ = min{s̄, t̄}`. -/
noncomputable def dmin (d : BSeq ℓ n) : ℝ := min (dbar d.1) (dbar d.2)

/-- `μ ε⁴ = μ(d) d̄^{4φ-4}`. -/
noncomputable def err41 (φ : ℝ) (d : BSeq ℓ n) : ℝ := mu d * dmin d ^ (4 * φ - 4)

/-! ### Shift identities for `μ` -/

theorem mu_sub_eS (d : BSeq ℓ n) (a : Fin ℓ) : mu (d - eS a) = mu d - 1 / (2 * ℓ * n) := by
  simp only [mu, sub_eS_fst, sub_eS_snd, M1_sub_e]; push_cast; ring

theorem mu_sub_eT (d : BSeq ℓ n) (v : Fin n) : mu (d - eT v) = mu d - 1 / (2 * ℓ * n) := by
  simp only [mu, sub_eT_fst, sub_eT_snd, M1_sub_e]; push_cast; ring

theorem mu_sub_eS_sub_eT (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) :
    mu (d - eS a - eT v) = mu d - 1 / (ℓ * n) := by
  rw [mu_sub_eT, mu_sub_eS]; ring

/-- On a balanced sequence `1/n = μ/s̄`, `1/ℓ = μ/t̄`. -/
theorem inv_n_of_bal {d : BSeq ℓ n} (h : Bal d) (hℓ : (ℓ : ℝ) ≠ 0) (hn : (n : ℝ) ≠ 0)
    (hs : dbar d.1 ≠ 0) : 1 / (n : ℝ) = mu d * (1 / dbar d.1) := by
  have : (M1 d.1 : ℝ) = M1 d.2 := by exact_mod_cast h
  have hM : (M1 d.1 : ℝ) ≠ 0 := fun h0 => hs (by rw [dbar, h0, zero_div])
  rw [mu, dbar, ← this]; field_simp; ring

theorem inv_l_of_bal {d : BSeq ℓ n} (h : Bal d) (hℓ : (ℓ : ℝ) ≠ 0) (hn : (n : ℝ) ≠ 0)
    (ht : dbar d.2 ≠ 0) : 1 / (ℓ : ℝ) = mu d * (1 / dbar d.2) := by
  have : (M1 d.1 : ℝ) = M1 d.2 := by exact_mod_cast h
  have hM : (M1 d.2 : ℝ) ≠ 0 := fun h0 => ht (by rw [dbar, h0, zero_div])
  rw [mu, dbar, this]; field_simp; ring

end LW.Bip
