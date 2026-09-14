import MajorityDynamics.Literature.LWFormal.OpY

set_option autoImplicit true

/-!
# Lemma 7.1(b): the expansion of `𝒫(P^gr, R^gr)`

With `d' = d - e_v`, `d''_b = d - e_b - e_v`, `S = n⁻¹ ∑_{b ≠ v} R^gr_{ba}(d') (1 - P^gr_{bv}(d''_b))`
and `pDen = (1 + ε_a)(1 + Acorr μ s₀ m ε_a ε_v)(1 + m) S`,
`𝒫(P^gr,R^gr)_{av}(d) / P^gr_{av}(d) = (1 - P^gr_{av}(d''_a)) / pDen`.
`opP_expansion` shows `pG := (1 - P^gr_{av}(d''_a) - pDen) / μ = O(η⁴)` and `pDen = 1 - μ + O(η)`.
-/

namespace LW

open Finset LW.TM

/-- `π(x, y) = pQ μ (σ²/(dn)) (1/(n-1)) x y`. -/
noncomputable def pQ (μ s m x y : ℝ) : ℝ := μ * (1 + x) * (1 + y) * (1 + Acorr μ s m x y)

theorem piF_eq_pQ (x y μ σ2 d : ℝ) (n : ℕ) :
    piF x y μ σ2 d n = pQ μ (σ2 / (d * n)) (1 / ((n : ℝ) - 1)) x y := piF_eq x y μ σ2 d n

/-- `R^gr_{ba}(d') (1 - P^gr_{bv}(d''_b))` in the parameters of `d'` and `d''_b`. -/
noncomputable def pTerm (μ' σ2' d' : ℝ) (n : ℕ) (xa xb μ3 s3 m xb3 xv3 : ℝ) : ℝ :=
  rhoF xb xa μ' σ2' d' n * (1 - pQ μ3 s3 m xb3 xv3)

/-- `(1 + ε_a)(1 + Acorr μ s₀ m ε_a ε_v)(1 + m) S`. -/
noncomputable def pDen (μ s0 m ea ev S : ℝ) : ℝ :=
  (1 + ea) * (1 + Acorr μ s0 m ea ev) * (1 + m) * S

/-- `pQ (μκ) (μs) (μδ) x y = μ · pQ' μ κ (1-μκ)⁻¹ s δ x y`. -/
noncomputable def pQ' (μ κ i s δ x y : ℝ) : ℝ := κ * (1 + x) * (1 + y) * (1 + μ * Acorr' i κ s δ x y)

theorem pQ_eq' (μ κ s δ x y : ℝ) :
    pQ (μ * κ) (μ * s) (μ * δ) x y = μ * pQ' μ κ (1 - μ * κ)⁻¹ s δ x y := by
  unfold pQ pQ'; rw [Acorr_eq']; ring

/-- `(R^gr_{ba}(d') (1+x_a)/(1+x_b) - 1)/μ` with `I = (1 - μ'(1+x_b) + 1/n)⁻¹`, `J = (1-μ')⁻²`,
`μ' = μ(1-c)`, `σ2'/(d'n) = μ s'`. -/
noncomputable def pRho (μ c I J s' xa xb : ℝ) : ℝ :=
  (1 - c) * (xb - xa) * I + (xb - xa) * s' * J + μ * (1 - c) * (xb - xa) ^ 2 * I * s' * J

/-- `(pTerm - (1+ε_b)/(1+ε_a))/μ`. -/
noncomputable def pH (μ c ea xb ρ Q : ℝ) : ℝ :=
  (1 + xb) * ((1 - c) * (1 + ea)⁻¹) * (ρ - Q - μ * ρ * Q)

theorem pTerm_decomp {μ σ2' d' : ℝ} {n : ℕ} {xa xb κ s3' δ xb3 xv3 c s' ea eb : ℝ}
    (hn : (n : ℝ) ≠ 0) (hd' : d' ≠ 0) (hμ' : 1 - μ * (1 - c) ≠ 0)
    (hI : 1 - μ * (1 - c) * (1 + xb) + 1 / n ≠ 0) (hc : 1 - c ≠ 0) (hea : 1 + ea ≠ 0)
    (hs' : σ2' / (d' * n) = μ * s')
    (hxa : 1 + xa = (1 + ea) / (1 - c)) (hxb : 1 + xb = (1 + eb) / (1 - c)) :
    pTerm (μ * (1 - c)) σ2' d' n xa xb (μ * κ) (μ * s3') (μ * δ) xb3 xv3 =
      (1 + eb) / (1 + ea) + μ * pH μ c ea xb
        (pRho μ c (1 - μ * (1 - c) * (1 + xb) + 1 / n)⁻¹ ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹)
          s' xa xb)
        (pQ' μ κ (1 - μ * κ)⁻¹ s3' δ xb3 xv3) := by
  have key : (xb - xa) * σ2' / ((1 - μ * (1 - c)) ^ 2 * d' * n) =
      (xb - xa) * (μ * s') * ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) := by
    rw [← hs']; field_simp
  have hR : (1 - μ * (1 - c) * (1 + xa) + 1 / n) / (1 - μ * (1 - c) * (1 + xb) + 1 / n) =
      1 + μ * (1 - c) * (xb - xa) * (1 - μ * (1 - c) * (1 + xb) + 1 / n)⁻¹ := by
    rw [div_eq_iff hI]
    linear_combination (-(μ * (1 - c) * (xb - xa))) * inv_mul_cancel₀ hI
  have hab : (1 + xb) / (1 + xa) = (1 + xb) * ((1 - c) * (1 + ea)⁻¹) := by
    rw [hxa]; field_simp
  have heb : (1 + eb) / (1 + ea) = (1 + xb) * ((1 - c) * (1 + ea)⁻¹) := by
    rw [hxb]; field_simp
  unfold pTerm rhoF
  rw [key, hR, pQ_eq', hab, heb]
  unfold pH pRho
  ring

/-- Lower bound on the ratio denominators of `R^gr`. -/
theorem pI_pos {μ x ν : ℝ} (hμ : 0 ≤ μ) (hμ4 : μ ≤ 1 / 4) (hx : |x| ≤ 2) (hν : 0 ≤ ν) :
    0 < 1 - μ * (1 + x) + ν := by
  have := (abs_le.1 hx).2
  nlinarith

set_option maxHeartbeats 0 in
/-- `pG = O(η⁴)` and `pDen = 1 - μ + O(η)`, in the normalised variables of `bad_expansion`;
`V = [n] \ {v}`, `a ∈ V`, and `xb1, xb3, xv3, μ3, s3 : V → ℝ` are the parameters of `d'`, `d''_b`. -/
theorem opP_expansion : ∃ bG bD : Bd, ∀ {ι : Type} (η μ δ t s₃ ea ev c μ' σ2' d' xa1 s0 : ℝ)
    (n : ℕ) (V : Finset ι) (a : ι) (ε xb1 xb3 xv3 μ3 s3 : ι → ℝ),
    0 < η → η ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 4 → 0 < δ → δ ≤ η ^ 2 → 0 ≤ t → t ≤ η ^ 2 →
    |s₃| ≤ η ^ 3 → |ea| ≤ η → |ev| ≤ η → (∀ b ∈ V, |ε b| ≤ η) → 3 ≤ n → V.card = n - 1 →
    a ∈ V → ε a = ea → 1 / ((n : ℝ) - 1) = μ * δ → c = δ / n →
    ∑ b ∈ V, ε b = -ev → ∑ b ∈ V, ε b ^ 2 = n * t - ev ^ 2 → ∑ b ∈ V, ε b ^ 3 = n * s₃ - ev ^ 3 →
    μ' = μ * (1 - c) → 1 / d' = δ / (1 - c) → xa1 = (ea + c) / (1 - c) →
    (∀ b ∈ V, xb1 b = (ε b + c) / (1 - c)) →
    σ2' / (d' * n) = (t + c * δ * (1 - 1 / n) - 2 * c * ev) * μ / ((1 + μ * δ) * (1 - c)) →
    (∀ b ∈ V, μ3 b = μ * (1 - 2 * c)) → (∀ b ∈ V, xb3 b = (ε b - δ + 2 * c) / (1 - 2 * c)) →
    (∀ b ∈ V, xv3 b = (ev - δ + 2 * c) / (1 - 2 * c)) →
    (∀ b ∈ V, s3 b = (t + 2 * c * δ * (1 - 2 / n) - 2 * c * (ε b + ev)) * (μ * (1 - 1 / n)) /
      (1 - 2 * c)) →
    s0 = t * (μ * (1 - 1 / n)) →
    Valid η 0 ((1 - pQ (μ3 a) (s3 a) (1 / ((n : ℝ) - 1)) (xb3 a) (xv3 a) -
        pDen μ s0 (1 / ((n : ℝ) - 1)) ea ev
          ((∑ b ∈ V, pTerm μ' σ2' d' n xa1 (xb1 b) (μ3 b) (s3 b) (1 / ((n : ℝ) - 1)) (xb3 b)
            (xv3 b)) / n)) / μ)
      (Pc.mk0 0 0 0 0) bG ∧
    Valid η 0 (pDen μ s0 (1 / ((n : ℝ) - 1)) ea ev
        ((∑ b ∈ V, pTerm μ' σ2' d' n xa1 (xb1 b) (μ3 b) (s3 b) (1 / ((n : ℝ) - 1)) (xb3 b)
          (xv3 b)) / n))
      (Pc.mk0 (1 - μ) (-μ * (ea + ev))
        (μ * (2 * δ * μ - 2 * δ - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (μ * (ea + ev) * (-δ * μ ^ 2 + 3 * δ * μ - δ - ea * ev * μ + μ * t) / (μ - 1))) bD := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  intro ι η μ δ t s₃ ea ev c μ' σ2' d' xa1 s0 n V a ε xb1 xb3 xv3 μ3 s3 hη hη2 hμ hμ4 hδ hδη ht
    htη hs₃ hea hev hεV hn3 hcard haV hεa hmud hc hm1 hm2 hm3 hμ' hd' hxa1 hxb1 hs' hμ3 hxb3
    hxv3 hs3 hs0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hμ1 : μ - 1 ≠ 0 := by linarith
  have h1μ : (1 : ℝ) - μ ≠ 0 := by linarith
  have hμδ : μ * δ * ((n : ℝ) - 1) = 1 := by rw [← hmud]; field_simp
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  have h1μδ : 1 + μ * δ ≠ 0 := by positivity
  have hν : 1 / (n : ℝ) = μ * δ * (1 + μ * δ)⁻¹ := by
    field_simp; linear_combination -hμδ
  have hν' : 1 / (n : ℝ) = μ * δ * (1 - 1 / n) := by
    field_simp; linear_combination -hμδ
  have hcpos : 0 < c := by rw [hc]; positivity
  have hη4 : η ^ 2 ≤ 1 / 4 := by nlinarith
  have hcη : c ≤ η ^ 2 / 3 := by
    rw [hc, div_le_iff₀ hn0]; nlinarith [mul_le_mul_of_nonneg_left hn3' (sq_nonneg η)]
  have hc12 : c ≤ 1 / 12 := by linarith
  have hc1 : 1 - c ≠ 0 := (by linarith : (0 : ℝ) < 1 - c).ne'
  have hκ0 : 1 - 2 * c ≠ 0 := (by linarith : (0 : ℝ) < 1 - 2 * c).ne'
  have hd'0 : d' ≠ 0 := by
    intro h; rw [h, div_zero] at hd'
    exact absurd hd' (div_ne_zero hδ.ne' hc1).symm
  have hea1 : 1 + ea ≠ 0 := by have := (abs_le.1 hea).1; linarith
  have hcardR : (V.card : ℝ) = n - 1 := by
    rw [hcard, Nat.cast_sub (by omega)]; norm_num
  have hVn : (V.card : ℝ) ≤ n := by linarith
  have hne : V.Nonempty := ⟨a, haV⟩
  -- factor `μ` out of `c`, `s'`, `s₀`, `s₃`
  obtain ⟨c', hc'⟩ : ∃ x, x = δ ^ 2 * (1 - 1 / (n : ℝ)) := ⟨_, rfl⟩
  have hcc : c = μ * c' :=
    calc c = δ * (1 / n) := by rw [hc]; ring
      _ = μ * c' := by rw [hν', hc']; ring
  obtain ⟨s', hs'd⟩ : ∃ x, x =
    (t + c * δ * (1 - 1 / (n : ℝ)) - 2 * c * ev) / ((1 + μ * δ) * (1 - c)) := ⟨_, rfl⟩
  have hs'' : σ2' / (d' * n) = μ * s' := by rw [hs', hs'd]; ring
  obtain ⟨s0', hs0'⟩ : ∃ x, x = t * (1 - 1 / (n : ℝ)) := ⟨_, rfl⟩
  have hs0'' : s0 = μ * s0' := by rw [hs0, hs0']; ring
  obtain ⟨s3', hs3'⟩ : ∃ f : ι → ℝ, f = fun b =>
    (t + 2 * c * δ * (1 - 2 / n) - 2 * c * (ε b + ev)) * (1 - 1 / n) / (1 - 2 * c) := ⟨_, rfl⟩
  have hs3'' : ∀ b ∈ V, s3 b = μ * s3' b := fun b hb => by rw [hs3 b hb, hs3']; ring
  subst hs0'' hμ'
  -- leaves (valid for every `z`)
  have L1 : ∀ z, Valid η z 1 (Pc.single 0 0 1) _ := fun z => Valid.const zero_le_one (by simp)
  have Lμ : ∀ z, Valid η z μ (Pc.single 0 0 μ) _ := fun z =>
    Valid.const (A := 1 / 4) (by norm_num) (by rw [abs_of_pos hμ]; exact hμ4)
  have Lδ : ∀ z, Valid η z δ (Pc.single 2 0 δ) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδ]; simpa using hδη)
  have Lt : ∀ z, Valid η z t (Pc.single 2 0 t) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg ht]; simpa using htη)
  have Ls₃ : ∀ z, Valid η z s₃ (Pc.single 3 0 s₃) _ := fun z =>
    Valid.leaf 3 (by norm_num) zero_le_one (by simpa using hs₃)
  have Lea : ∀ z, Valid η z ea (Pc.single 1 0 ea) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Lev : ∀ z, Valid η z ev (Pc.single 1 0 ev) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hev)
  have L2 : ∀ z, Valid η z 2 (Pc.single 0 0 2) _ := fun z =>
    Valid.const (A := 2) (by norm_num) (by simp)
  -- derived `z`-free quantities
  have Lm : ∀ z, Valid η z (1 / ((n : ℝ) - 1)) (Pc.mk0 0 0 (μ * δ) 0) _ := fun z =>
    (((Lμ z).mul (Lδ z)).congr_val hmud.symm).congr (by pieces)
  have Lμδ : ∀ z, Valid η z (1 + μ * δ) (Pc.mk0 1 0 (μ * δ) 0) _ := fun z =>
    ((L1 z).add ((Lμ z).mul (Lδ z))).congr (by pieces)
  have Lim : ∀ z, Valid η z (1 + μ * δ)⁻¹ (Pc.mk0 1 0 (-(μ * δ)) 0) _ := fun z =>
    ((Lμδ z).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lν : ∀ z, Valid η z (1 / (n : ℝ)) (Pc.mk0 0 0 (μ * δ) 0) _ := fun z =>
    ((((Lμ z).mul (Lδ z)).mul (Lim z)).congr_val hν.symm).congr (by pieces)
  have Lomν : ∀ z, Valid η z (1 - 1 / (n : ℝ)) (Pc.mk0 1 0 (-(μ * δ)) 0) _ := fun z =>
    ((L1 z).sub (Lν z)).congr (by pieces)
  have Lc' : ∀ z, Valid η z c' (Pc.mk0 0 0 0 0) _ := fun z =>
    ((((Lδ z).mul (Lδ z)).mul (Lomν z)).congr_val (by rw [hc']; ring)).congr (by pieces)
  have Lc : ∀ z, Valid η z c (Pc.mk0 0 0 0 0) _ := fun z =>
    (((Lμ z).mul (Lc' z)).congr_val hcc.symm).congr (by pieces)
  have Lomc : ∀ z, Valid η z (1 - c) (Pc.mk0 1 0 0 0) _ := fun z =>
    ((L1 z).sub (Lc z)).congr (by pieces)
  have Lomci : ∀ z, Valid η z (1 - c)⁻¹ (Pc.mk0 1 0 0 0) _ := fun z =>
    ((Lomc z).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lκ : ∀ z, Valid η z (1 - 2 * c) (Pc.mk0 1 0 0 0) _ := fun z =>
    ((L1 z).sub ((L2 z).mul (Lc z))).congr (by pieces)
  have Lκi : ∀ z, Valid η z (1 - 2 * c)⁻¹ (Pc.mk0 1 0 0 0) _ := fun z =>
    ((Lκ z).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lμ' : ∀ z, Valid η z (μ * (1 - c)) (Pc.mk0 μ 0 0 0) _ := fun z =>
    ((Lμ z).mul (Lomc z)).congr (by pieces)
  have Lμ3 : ∀ z, Valid η z (μ * (1 - 2 * c)) (Pc.mk0 μ 0 0 0) _ := fun z =>
    ((Lμ z).mul (Lκ z)).congr (by pieces)
  have Lxa1 : ∀ z, Valid η z xa1 (Pc.mk0 0 ea 0 0) _ := fun z =>
    ((((Lea z).add (Lc z)).mul (Lomci z)).congr_val (by rw [hxa1]; ring)).congr (by pieces)
  have Ls' : ∀ z, Valid η z s' (Pc.mk0 0 0 t 0) _ := fun z =>
    ((((((Lt z).add (((Lc z).mul (Lδ z)).mul (Lomν z))).sub
      (((L2 z).mul (Lc z)).mul (Lev z))).mul (Lim z)).mul (Lomci z)).congr_val
      (by rw [hs'd]; field_simp)).congr (by pieces)
  have Ls0 : ∀ z, Valid η z s0' (Pc.mk0 0 0 t 0) _ := fun z =>
    (((Lt z).mul (Lomν z)).congr_val hs0'.symm).congr (by pieces)
  have L1μ : ∀ z, Valid η z (1 - μ) (Pc.mk0 (1 - μ) 0 0 0) _ := fun z =>
    ((L1 z).sub (Lμ z)).congr (by pieces)
  have Li0 : ∀ z, Valid η z (1 - μ)⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    ((L1μ z).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have L1μ' : ∀ z, Valid η z (1 - μ * (1 - c)) (Pc.mk0 (1 - μ) 0 0 0) _ := fun z =>
    ((L1 z).sub (Lμ' z)).congr (by pieces)
  have Li1 : ∀ z, Valid η z (1 - μ * (1 - c))⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    ((L1μ' z).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have LJ : ∀ z, Valid η z ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹)
      (Pc.mk0 (1 / (μ - 1) ^ 2) 0 0 0) _ := fun z =>
    ((Li1 z).mul (Li1 z)).congr (by pieces)
  have L1μ3 : ∀ z, Valid η z (1 - μ * (1 - 2 * c)) (Pc.mk0 (1 - μ) 0 0 0) _ := fun z =>
    ((L1 z).sub (Lμ3 z)).congr (by pieces)
  have Li3 : ∀ z, Valid η z (1 - μ * (1 - 2 * c))⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    ((L1μ3 z).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have Li1pea : ∀ z, Valid η z (1 + ea)⁻¹ (Pc.mk0 1 (-ea) (ea ^ 2) (-ea ^ 3)) _ := fun z =>
    (((L1 z).add (Lea z)).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ) + 0|; norm_num)).congr
      (by pieces)
  -- the parameters of `d''_a`
  have hxa3 := hxb3 a haV
  have hxv3a := hxv3 a haV
  rw [hεa] at hxa3
  have Lxa3 : Valid η 0 (xb3 a) (Pc.mk0 0 ea (-δ) 0) _ :=
    (((((Lea 0).sub (Lδ 0)).add ((L2 0).mul (Lc 0))).mul (Lκi 0)).congr_val
      (by rw [hxa3]; ring)).congr (by pieces)
  have Lxv3 : Valid η 0 (xv3 a) (Pc.mk0 0 ev (-δ) 0) _ :=
    (((((Lev 0).sub (Lδ 0)).add ((L2 0).mul (Lc 0))).mul (Lκi 0)).congr_val
      (by rw [hxv3a]; ring)).congr (by pieces)
  have Ls3a : Valid η 0 (s3' a) (Pc.mk0 0 0 t 0) _ :=
    (((((Lt 0).add ((((L2 0).mul (Lc 0)).mul (Lδ 0)).mul ((L1 0).sub ((L2 0).mul (Lν 0))))).sub
      (((L2 0).mul (Lc 0)).mul ((Lea 0).add (Lev 0)))).mul (Lomν 0)).mul (Lκi 0)).congr_val
      (by rw [hs3']; beta_reduce; rw [hεa]; ring) |>.congr (by pieces)
  have LAav3 : Valid η 0 (Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) (s3' a) δ (xb3 a) (xv3 a))
      (Pc.mk0 0 0 (ea * ev / (μ - 1)) (-(ea + ev) * (-δ * μ + 2 * δ + t) / (μ - 1))) _ :=
    ((Li3 0).acorr' (Lκ 0) Ls3a (Lδ 0) Lxa3 Lxv3).congr (by unfold Pc.acorr; pieces)
  have LQa : Valid η 0 (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' a) δ (xb3 a) (xv3 a))
      (Pc.mk0 1 (ea + ev) (-(2 * δ * μ - 2 * δ - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (-(ea + ev) * (-δ * μ ^ 2 + 3 * δ * μ - δ - ea * ev * μ + μ * t) / (μ - 1))) _ :=
    (((((Lκ 0).mul ((L1 0).add Lxa3)).mul ((L1 0).add Lxv3)).mul
      ((L1 0).add ((Lμ 0).mul LAav3))).congr_val (by unfold pQ'; ring)).congr (by pieces)
  have LA0 : Valid η 0 (Acorr' (1 - μ)⁻¹ 1 s0' δ ea ev)
      (Pc.mk0 0 0 (ea * ev / (μ - 1)) (-(ea + ev) * (-δ * μ + δ + t) / (μ - 1))) _ :=
    ((Li0 0).acorr' (L1 0) (Ls0 0) (Lδ 0) (Lea 0) (Lev 0)).congr (by unfold Pc.acorr; pieces)
  -- the `b`-dependent factor, expanded in `z = ε b`
  have hH : ∀ b ∈ V, Valid η (ε b)
      (pH μ c ea (xb1 b)
        (pRho μ c (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
          ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) s' xa1 (xb1 b))
        (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' b) δ (xb3 b) (xv3 b)))
      (Pc.mk (-1) (-ev) (-1) ((2 * δ * μ - 2 * δ - ea * ev) / (μ - 1)) (-2 * ev) 0
        ((-δ * ea * μ + 2 * δ * ea - δ * ev * μ ^ 2 + 3 * δ * ev * μ - δ * ev + ea ^ 2 * ev
          + ea * t + ev * μ * t) / (μ - 1))
        ((-δ * μ ^ 2 + 4 * δ * μ - 3 * δ - 2 * ea * ev - ev ^ 2 * μ + μ * t - t) / (μ - 1))
        (-ev) 0) _ := fun b hb =>
    have hz : Valid η (ε b) (ε b) (Pc.single 1 1 1) _ := Valid.var
    have Lxb1 : Valid η (ε b) (xb1 b) (Pc.mk 0 0 1 0 0 0 0 0 0 0) _ :=
      (((hz.add (Lc _)).mul (Lomci _)).congr_val (by rw [hxb1 b hb]; ring)).congr (by pieces)
    have Lxb3 : Valid η (ε b) (xb3 b) (Pc.mk 0 0 1 (-δ) 0 0 0 0 0 0) _ :=
      ((((hz.sub (Lδ _)).add ((L2 _).mul (Lc _))).mul (Lκi _)).congr_val
        (by rw [hxb3 b hb]; ring)).congr (by pieces)
    have Lxv3b : Valid η (ε b) (xv3 b) (Pc.mk0 0 ev (-δ) 0) _ :=
      (((((Lev _).sub (Lδ _)).add ((L2 _).mul (Lc _))).mul (Lκi _)).congr_val
        (by rw [hxv3 b hb]; ring)).congr (by pieces)
    have Ls3b : Valid η (ε b) (s3' b) (Pc.mk0 0 0 t 0) _ :=
      (((((Lt _).add ((((L2 _).mul (Lc _)).mul (Lδ _)).mul ((L1 _).sub ((L2 _).mul (Lν _))))).sub
        (((L2 _).mul (Lc _)).mul (hz.add (Lev _)))).mul (Lomν _)).mul (Lκi _)).congr_val
        (by rw [hs3']; beta_reduce; ring) |>.congr (by pieces)
    have LIbd : Valid η (ε b) (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)
        (Pc.mk (1 - μ) 0 (-μ) (δ * μ) 0 0 0 0 0 0) _ :=
      (((L1 _).sub ((Lμ' _).mul ((L1 _).add Lxb1))).add (Lν _)).congr (by pieces)
    have LIb : Valid η (ε b) (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
        (Pc.mk (-1 / (μ - 1)) 0 (μ / (μ - 1) ^ 2) (-δ * μ / (μ - 1) ^ 2) 0 (-μ ^ 2 / (μ - 1) ^ 3)
          0 (2 * δ * μ ^ 2 / (μ - 1) ^ 3) 0 (μ ^ 3 / (μ - 1) ^ 4)) _ :=
      (LIbd.inv (L := 3 / 4) (by norm_num)
        (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
        (by pieces)
    have LAbv3 : Valid η (ε b)
        (Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) (s3' b) δ (xb3 b) (xv3 b))
        (Pc.mk 0 0 0 0 (ev / (μ - 1)) 0 (-ev * (-δ * μ + 2 * δ + t) / (μ - 1))
          (-(-δ * μ + 2 * δ + t) / (μ - 1)) 0 0) _ :=
      ((Li3 _).acorr' (Lκ _) Ls3b (Lδ _) Lxb3 Lxv3b).congr (by unfold Pc.acorr; pieces)
    have LQb : Valid η (ε b)
        (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' b) δ (xb3 b) (xv3 b))
        (Pc.mk 1 ev 1 (-2 * δ) (ev * (2 * μ - 1) / (μ - 1)) 0
          (-ev * (-δ * μ ^ 2 + 3 * δ * μ - δ + μ * t) / (μ - 1))
          (-(-δ * μ ^ 2 + 3 * δ * μ - δ - ev ^ 2 * μ + μ * t) / (μ - 1)) (ev * μ / (μ - 1)) 0) _ :=
      (((((Lκ _).mul ((L1 _).add Lxb3)).mul ((L1 _).add Lxv3b)).mul
        ((L1 _).add ((Lμ _).mul LAbv3))).congr_val (by unfold pQ'; ring)).congr (by pieces)
    have Ldx : Valid η (ε b) (xb1 b - xa1) (Pc.mk 0 (-ea) 1 0 0 0 0 0 0 0) _ :=
      (Lxb1.sub (Lxa1 _)).congr (by pieces)
    have Lρ : Valid η (ε b)
        (pRho μ c (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
          ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) s' xa1 (xb1 b))
        (Pc.mk 0 (ea / (μ - 1)) (-1 / (μ - 1)) 0 (-ea * μ / (μ - 1) ^ 2) (μ / (μ - 1) ^ 2)
          (-ea * (-δ * μ + t) / (μ - 1) ^ 2) ((-δ * μ + t) / (μ - 1) ^ 2)
          (ea * μ ^ 2 / (μ - 1) ^ 3) (-μ ^ 2 / (μ - 1) ^ 3)) _ :=
      (((((Lomc _).mul Ldx).mul LIb).add ((Ldx.mul (Ls' _)).mul (LJ _))).add
        ((((((Lμ _).mul (Lomc _)).mul (Ldx.mul Ldx)).mul LIb).mul (Ls' _)).mul (LJ _))).congr_val
        (by unfold pRho; ring) |>.congr (by pieces)
    have Lpref : Valid η (ε b) ((1 + xb1 b) * ((1 - c) * (1 + ea)⁻¹))
        (Pc.mk 1 (-ea) 1 (ea ^ 2) (-ea) 0 (-ea ^ 3) (ea ^ 2) 0 0) _ :=
      (((L1 _).add Lxb1).mul ((Lomc _).mul (Li1pea _))).congr (by pieces)
    (Lpref.mul ((Lρ.sub LQb).sub (((Lμ _).mul Lρ).mul LQb))).congr_val (by unfold pH; ring)
      |>.congr (by pieces)
  -- moments of `ε` over `V`
  have LP0 : Valid η 0 (1 - 1 / (n : ℝ)) (Pc.mk0 1 0 (-δ * μ) 0) _ := (Lomν 0).congr (by pieces)
  have LP1 : Valid η 0 (-(1 / (n : ℝ)) * ev) (Pc.mk0 0 0 0 (-δ * ev * μ)) _ :=
    ((Lν 0).neg.mul (Lev 0)).congr (by pieces)
  have LP2 : Valid η 0 (t - 1 / (n : ℝ) * ev ^ 2) (Pc.mk0 0 0 t 0) _ :=
    (((Lt 0).sub ((Lν 0).mul ((Lev 0).mul (Lev 0)))).congr_val (by ring)).congr (by pieces)
  have LP3 : Valid η 0 (s₃ - 1 / (n : ℝ) * ev ^ 3) (Pc.mk0 0 0 0 s₃) _ :=
    (((Ls₃ 0).sub ((Lν 0).mul (((Lev 0).mul (Lev 0)).mul (Lev 0)))).congr_val (by ring)).congr
      (by pieces)
  have Lavg : Valid η 0
      ((∑ b ∈ V, pH μ c ea (xb1 b)
        (pRho μ c (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
          ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) s' xa1 (xb1 b))
        (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' b) δ (xb3 b) (xv3 b))) / n)
      (Pc.mk0 (-1) (-ev) ((δ * μ ^ 2 + δ * μ - 2 * δ - ea * ev) / (μ - 1))
        ((-δ * ea * μ + 2 * δ * ea + δ * ev * μ ^ 2 + δ * ev * μ - δ * ev + ea ^ 2 * ev + ea * t
          + ev * t) / (μ - 1))) _ :=
    (Valid.avg4 hne hεV hH hn0 hVn
      (by simp [hcardR]; field_simp)
      (by simp only [pow_one, hm1]; ring)
      (by rw [hm2]; field_simp)
      (by rw [hm3]; field_simp) LP0 LP1 LP2 LP3).congr (by pieces)
  have Lpref : Valid η 0 ((1 + ea) * (1 + μ * Acorr' (1 - μ)⁻¹ 1 s0' δ ea ev) * (1 + μ * δ))
      (Pc.mk0 1 ea (μ * (δ * μ - δ + ea * ev) / (μ - 1))
        (-μ * (-2 * δ * ea * μ + 2 * δ * ea - δ * ev * μ + δ * ev - ea ^ 2 * ev + ea * t + ev * t) /
          (μ - 1))) _ :=
    ((((L1 0).add (Lea 0)).mul ((L1 0).add ((Lμ 0).mul LA0))).mul (Lμδ 0)).congr (by pieces)
  have LE : Valid η 0 (δ * ev - pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' a) δ (xb3 a) (xv3 a) -
      Acorr' (1 - μ)⁻¹ 1 s0' δ ea ev * (1 - μ * δ * ev) -
      (1 + ea) * (1 + μ * Acorr' (1 - μ)⁻¹ 1 s0' δ ea ev) * (1 + μ * δ) *
        ((∑ b ∈ V, pH μ c ea (xb1 b)
          (pRho μ c (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
            ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) s' xa1 (xb1 b))
          (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' b) δ (xb3 b) (xv3 b))) / n))
      (Pc.mk0 0 0 0 0) _ :=
    (((((Lδ 0).mul (Lev 0)).sub LQa).sub
      (LA0.mul ((L1 0).sub (((Lμ 0).mul (Lδ 0)).mul (Lev 0))))).sub (Lpref.mul Lavg)).congr
      (by pieces)
  have LD : Valid η 0 ((1 + μ * Acorr' (1 - μ)⁻¹ 1 s0' δ ea ev) * (1 - μ * δ * ev) +
      μ * ((1 + ea) * (1 + μ * Acorr' (1 - μ)⁻¹ 1 s0' δ ea ev) * (1 + μ * δ) *
        ((∑ b ∈ V, pH μ c ea (xb1 b)
          (pRho μ c (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
            ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) s' xa1 (xb1 b))
          (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' b) δ (xb3 b) (xv3 b))) / n)))
      (Pc.mk0 (1 - μ) (-μ * (ea + ev))
        (μ * (2 * δ * μ - 2 * δ - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (μ * (ea + ev) * (-δ * μ ^ 2 + 3 * δ * μ - δ - ea * ev * μ + μ * t) / (μ - 1))) _ :=
    ((((L1 0).add ((Lμ 0).mul LA0)).mul ((L1 0).sub (((Lμ 0).mul (Lδ 0)).mul (Lev 0)))).add
      ((Lμ 0).mul (Lpref.mul Lavg))).congr (by pieces)
  -- the exact decomposition of the sum
  have hμ'0 : 1 - μ * (1 - c) ≠ 0 := (by nlinarith : (0 : ℝ) < 1 - μ * (1 - c)).ne'
  have hsum : ∑ b ∈ V, pTerm (μ * (1 - c)) σ2' d' n xa1 (xb1 b) (μ3 b) (s3 b) (1 / ((n : ℝ) - 1))
      (xb3 b) (xv3 b) =
      ((n : ℝ) - 1 - ev) / (1 + ea) + μ * ∑ b ∈ V, pH μ c ea (xb1 b)
        (pRho μ c (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
          ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) s' xa1 (xb1 b))
        (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' b) δ (xb3 b) (xv3 b)) := by
    rw [show ((n : ℝ) - 1 - ev) / (1 + ea) = ∑ b ∈ V, (1 + ε b) / (1 + ea) by
      rw [← sum_div, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, hcardR, hm1]; ring]
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun b hb => ?_
    have hI : 1 - μ * (1 - c) * (1 + xb1 b) + 1 / n ≠ 0 := by
      have hb1 : |xb1 b| ≤ 2 := by
        rw [hxb1 b hb, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - c),
          div_le_iff₀ (by linarith)]
        calc |ε b + c| ≤ |ε b| + |c| := abs_add_le _ _
          _ ≤ η + c := by rw [abs_of_pos hcpos]; linarith [hεV b hb]
          _ ≤ 2 * (1 - c) := by linarith
      exact (pI_pos (mul_nonneg hμ.le (by linarith)) (by nlinarith) hb1 (by positivity)).ne'
    rw [hμ3 b hb, hs3'' b hb, hmud]
    exact pTerm_decomp hn0' hd'0 hμ'0 hI hc1 hea1 hs''
      (by rw [hxa1]; field_simp; ring) (by rw [hxb1 b hb]; field_simp; ring)
  have hn_eq : (n : ℝ) = 1 + 1 / (μ * δ) := by
    field_simp; linear_combination hμδ
  have hQa : pQ (μ3 a) (s3 a) (μ * δ) (xb3 a) (xv3 a) =
      μ * pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' a) δ (xb3 a) (xv3 a) := by
    rw [hμ3 a haV, hs3'' a haV, pQ_eq']
  rw [hmud]
  set SH := ∑ b ∈ V, pH μ c ea (xb1 b)
    (pRho μ c (1 - μ * (1 - c) * (1 + xb1 b) + 1 / n)⁻¹
      ((1 - μ * (1 - c))⁻¹ * (1 - μ * (1 - c))⁻¹) s' xa1 (xb1 b))
    (pQ' μ (1 - 2 * c) (1 - μ * (1 - 2 * c))⁻¹ (s3' b) δ (xb3 b) (xv3 b)) with hSH
  rw [hmud] at hsum
  have hμδ0 : μ * δ ≠ 0 := by positivity
  have hμδ1' : μ * δ + 1 ≠ 0 := by positivity
  constructor
  · refine LE.congr_val ?_
    rw [hQa, pDen, hsum, Acorr_eq'1, hn_eq, eq_div_iff hμ.ne']
    field_simp
    ring
  · refine LD.congr_val ?_
    rw [pDen, hsum, Acorr_eq'1, hn_eq]
    field_simp
    ring

end LW
