import MajorityDynamics.Literature.LWFormal.Bad

set_option autoImplicit true

/-!
# Lemma 7.1(c): the expansion of `𝒴(P^gr, Y^gr)`

With `d₃ = d - e_a - e_v`, `c = δ/n` and `μ₃, s₃, δ₃, x_a, x_v, x_b` the parameters of `d₃`,
`𝒴(P^gr,Y^gr)_{avb}(d) / Y^gr_{avb}(d) = (1 + 2c/(1+ε_v-δ)) · yNum / ((1-2c) · yDen)`.
`opY_expansion` shows `yG := ((1 + 2c/(1+ε_v-δ)) yNum - (1-2c) yDen) / μ = O(η⁴)` and
`yD := (1-2c) yDen = 1 - μ + O(η)`.
-/

namespace LW

open Finset LW.TM

/-- `Acorr (μκ) (μs) (μm) x y = μ · Acorr' (1-μκ)⁻¹ κ s m x y`. -/
noncomputable def Acorr' (i κ s m x y : ℝ) : ℝ := (-κ * x * y + (x + y) * s) * i + (x + y) * m

theorem Acorr_eq' (μ κ s m x y : ℝ) :
    Acorr (μ * κ) (μ * s) (μ * m) x y = μ * Acorr' (1 - μ * κ)⁻¹ κ s m x y := by
  unfold Acorr Acorr'; ring

theorem Acorr_eq'1 (μ s m x y : ℝ) :
    Acorr μ (μ * s) (μ * m) x y = μ * Acorr' (1 - μ)⁻¹ 1 s m x y := by
  unfold Acorr Acorr'; ring

/-- `Tcorr μ' (μm) xa xb = μ · Tcorr' (1-μ')⁻¹ μ' m xa xb`. -/
noncomputable def Tcorr' (i μ' m xa xb : ℝ) : ℝ := m * (1 + xa - μ' * (1 + xa + xb)) * i

theorem Tcorr_eq' (μ μ' m xa xb : ℝ) :
    Tcorr μ' (μ * m) xa xb = μ * Tcorr' (1 - μ')⁻¹ μ' m xa xb := by
  unfold Tcorr Tcorr'; ring

theorem TM.Valid.acorr' {η z i κ s m x y : ℝ} {ci cκ cs cm cx cy : Pc} {bi bκ bs bm bx by_ : Bd}
    (hi : Valid η z i ci bi) (hκ : Valid η z κ cκ bκ) (hs : Valid η z s cs bs)
    (hm : Valid η z m cm bm) (hx : Valid η z x cx bx) (hy : Valid η z y cy by_) :
    Valid η z (Acorr' i κ s m x y) (Pc.acorr cκ cs cm ci cx cy) (Bd.acorr bκ bs bm bi bx by_) :=
  (((((hκ.neg.mul hx).mul hy).add ((hx.add hy).mul hs)).mul hi).add
    ((hx.add hy).mul hm)).congr_val (by unfold Acorr'; ring)

theorem TM.Valid.tcorr' {η z i μ' m xa xb : ℝ} {c1 ci cμ cm ca cb : Pc} {b1 bi bμ bm ba bb : Bd}
    (h1 : Valid η z 1 c1 b1) (hi : Valid η z i ci bi) (hμ : Valid η z μ' cμ bμ)
    (hm : Valid η z m cm bm) (ha : Valid η z xa ca ba) (hb : Valid η z xb cb bb) :
    Valid η z (Tcorr' i μ' m xa xb)
      (Pc.mul (Pc.mul cm (Pc.add (Pc.add c1 ca) (Pc.neg (Pc.mul cμ (Pc.add (Pc.add c1 ca) cb)))))
        ci)
      (Bd.mul (Bd.mul bm (Bd.add (Bd.add b1 ba) (Bd.mul bμ (Bd.add (Bd.add b1 ba) bb)))) bi) :=
  ((hm.mul ((h1.add ha).sub (hμ.mul ((h1.add ha).add hb)))).mul hi).congr_val
    (by unfold Tcorr'; ring)

/-- `(P^gr_{bv}(d₃) - Y^gr_{avb}(d₃)) / (μ₃(1+x_b)(1+x_v))`. -/
noncomputable def yNum (μ3 s3 m δ3 xa xv xb : ℝ) : ℝ :=
  1 + Acorr μ3 s3 m xb xv - μ3 * (1 + xa) * (1 + Acorr μ3 s3 m xa xv) * (1 + xv - δ3) *
    (1 + Acorr μ3 s3 m xb (xv - δ3)) * (1 + Tcorr μ3 m xa xb)

/-- `(1 - P^gr_{av}(d₃)) · π(ε_b, ε_v - δ)(1 + Tcorr) / (μ(1+ε_b)(1+ε_v-δ))`. -/
noncomputable def yDen (μ s0 m δ ea ev eb μ3 s3 xa xv : ℝ) : ℝ :=
  (1 - μ3 * (1 + xa) * (1 + xv) * (1 + Acorr μ3 s3 m xa xv)) * (1 + Acorr μ s0 m eb (ev - δ)) *
    (1 + Tcorr μ m ea eb)

set_option maxHeartbeats 0 in
/-- `yG = O(η⁴)` and `yD = 1 - μ + O(η)`, in the normalised variables of `bad_expansion`, with
`c = δ/n`, `s₀ = σ²/(d̄ n)`, `s₃ = σ₃²/(d̄₃ n)`. -/
theorem opY_expansion : ∃ bG bD : Bd, ∀ (η μ δ t ea ev eb c μ3 δ3 xa xv xb s0 s3 : ℝ) (n : ℕ),
    0 < η → η ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 4 → 0 < δ → δ ≤ η ^ 2 → 0 ≤ t → t ≤ η ^ 2 →
    |ea| ≤ η → |ev| ≤ η → |eb| ≤ η → 3 ≤ n → 1 / ((n : ℝ) - 1) = μ * δ → c = δ / n →
    μ3 = μ * (1 - 2 * c) → δ3 = δ / (1 - 2 * c) →
    xa = (ea - δ + 2 * c) / (1 - 2 * c) → xv = (ev - δ + 2 * c) / (1 - 2 * c) →
    xb = (eb + 2 * c) / (1 - 2 * c) → s0 = t * (μ * (1 - 1 / n)) →
    s3 = (t + 2 * c * δ * (1 - 2 / n) - 2 * c * (ea + ev)) * (μ * (1 - 1 / n)) / (1 - 2 * c) →
    Valid η 0 ((yNum μ3 s3 (1 / ((n : ℝ) - 1)) δ3 xa xv xb -
        (1 - 2 * c) * yDen μ s0 (1 / ((n : ℝ) - 1)) δ ea ev eb μ3 s3 xa xv) / μ)
      (Pc.mk0 0 0 0 0) bG ∧
    Valid η 0 ((1 - 2 * c) * yDen μ s0 (1 / ((n : ℝ) - 1)) δ ea ev eb μ3 s3 xa xv)
      (Pc.mk0 (1 - μ) (-μ * (ea + ev))
        (-μ * (δ * μ ^ 2 - 4 * δ * μ + 3 * δ + 2 * ea * ev * μ - ea * ev + eb * ev * μ - eb * ev) /
          (μ - 1))
        (μ * (-3 * δ * ea * μ ^ 2 + 6 * δ * ea * μ - 2 * δ * ea - 2 * δ * eb * μ ^ 2
          + 4 * δ * eb * μ - 2 * δ * eb - 3 * δ * ev * μ ^ 2 + 6 * δ * ev * μ - 2 * δ * ev
          - ea ^ 2 * ev * μ - ea * eb * ev * μ - ea * ev ^ 2 * μ + ea * μ * t - eb * ev ^ 2 * μ
          + eb * μ * t - eb * t + 2 * ev * μ * t - ev * t) / (μ - 1))) bD := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  intro η μ δ t ea ev eb c μ3 δ3 xa xv xb s0 s3 n hη hη2 hμ hμ4 hδ hδη ht htη hea hev heb hn3
    hmud hc hμ3 hδ3 hxa hxv hxb hs0 hs3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hμ1 : μ - 1 ≠ 0 := by linarith
  have h1μ : (1 : ℝ) - μ ≠ 0 := by linarith
  have hμδ : μ * δ * ((n : ℝ) - 1) = 1 := by rw [← hmud]; field_simp
  have h1μδ : 1 + μ * δ ≠ 0 := by positivity
  have hν : 1 / (n : ℝ) = μ * δ * (1 + μ * δ)⁻¹ := by
    field_simp; linear_combination -hμδ
  have hν' : 1 / (n : ℝ) = μ * δ * (1 - 1 / n) := by
    field_simp; linear_combination -hμδ
  -- factor `μ` out of `c`, `s₀`, `s₃`
  obtain ⟨c', hc'⟩ : ∃ x, x = δ ^ 2 * (1 - 1 / (n : ℝ)) := ⟨_, rfl⟩
  have hcc : c = μ * c' :=
    calc c = δ * (1 / n) := by rw [hc]; ring
      _ = μ * c' := by rw [hν', hc']; ring
  obtain ⟨s0', hs0'⟩ : ∃ x, x = t * (1 - 1 / (n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨s3', hs3'⟩ : ∃ x, x =
    (t + 2 * c * δ * (1 - 2 / n) - 2 * c * (ea + ev)) * (1 - 1 / n) / (1 - 2 * c) := ⟨_, rfl⟩
  have hs0'' : s0 = μ * s0' := by rw [hs0, hs0']; ring
  have hs3'' : s3 = μ * s3' := by rw [hs3, hs3']; ring
  subst hs0'' hs3'' hμ3
  -- leaves
  have L1 : Valid η 0 1 (Pc.single 0 0 1) _ := Valid.const zero_le_one (by simp)
  have Lμ : Valid η 0 μ (Pc.single 0 0 μ) _ :=
    Valid.const (A := 1 / 4) (by norm_num) (by rw [abs_of_pos hμ]; exact hμ4)
  have Lδ : Valid η 0 δ (Pc.single 2 0 δ) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδ]; simpa using hδη)
  have Lt : Valid η 0 t (Pc.single 2 0 t) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg ht]; simpa using htη)
  have Lea : Valid η 0 ea (Pc.single 1 0 ea) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Lev : Valid η 0 ev (Pc.single 1 0 ev) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hev)
  have Leb : Valid η 0 eb (Pc.single 1 0 eb) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using heb)
  have L2 : Valid η 0 2 (Pc.single 0 0 2) _ := Valid.const (A := 2) (by norm_num) (by simp)
  -- derived quantities
  have Lm : Valid η 0 (1 / ((n : ℝ) - 1)) (Pc.mk0 0 0 (μ * δ) 0) _ :=
    ((Lμ.mul Lδ).congr_val hmud.symm).congr (by pieces)
  have Lμδ : Valid η 0 (1 + μ * δ) (Pc.mk0 1 0 (μ * δ) 0) _ := (L1.add (Lμ.mul Lδ)).congr (by pieces)
  have Lim : Valid η 0 (1 + μ * δ)⁻¹ (Pc.mk0 1 0 (-(μ * δ)) 0) _ :=
    (Lμδ.inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lν : Valid η 0 (1 / (n : ℝ)) (Pc.mk0 0 0 (μ * δ) 0) _ :=
    (((Lμ.mul Lδ).mul Lim).congr_val hν.symm).congr (by pieces)
  have Lomν : Valid η 0 (1 - 1 / (n : ℝ)) (Pc.mk0 1 0 (-(μ * δ)) 0) _ :=
    (L1.sub Lν).congr (by pieces)
  have Lc' : Valid η 0 c' (Pc.mk0 0 0 0 0) _ :=
    (((Lδ.mul Lδ).mul Lomν).congr_val (by rw [hc']; ring)).congr (by pieces)
  have Lc : Valid η 0 c (Pc.mk0 0 0 0 0) _ := ((Lμ.mul Lc').congr_val hcc.symm).congr (by pieces)
  have Lκ : Valid η 0 (1 - 2 * c) (Pc.mk0 1 0 0 0) _ := (L1.sub (L2.mul Lc)).congr (by pieces)
  have Lκi : Valid η 0 (1 - 2 * c)⁻¹ (Pc.mk0 1 0 0 0) _ :=
    (Lκ.inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lμ3 : Valid η 0 (μ * (1 - 2 * c)) (Pc.mk0 μ 0 0 0) _ := (Lμ.mul Lκ).congr (by pieces)
  have Lδ3 : Valid η 0 δ3 (Pc.mk0 0 0 δ 0) _ :=
    ((Lδ.mul Lκi).congr_val (by rw [hδ3]; ring)).congr (by pieces)
  have Lxa : Valid η 0 xa (Pc.mk0 0 ea (-δ) 0) _ :=
    ((((Lea.sub Lδ).add (L2.mul Lc)).mul Lκi).congr_val (by rw [hxa]; ring)).congr (by pieces)
  have Lxv : Valid η 0 xv (Pc.mk0 0 ev (-δ) 0) _ :=
    ((((Lev.sub Lδ).add (L2.mul Lc)).mul Lκi).congr_val (by rw [hxv]; ring)).congr (by pieces)
  have Lxb : Valid η 0 xb (Pc.mk0 0 eb 0 0) _ :=
    (((Leb.add (L2.mul Lc)).mul Lκi).congr_val (by rw [hxb]; ring)).congr (by pieces)
  have Ls0 : Valid η 0 s0' (Pc.mk0 0 0 t 0) _ :=
    ((Lt.mul Lomν).congr_val hs0'.symm).congr (by pieces)
  have Ls3 : Valid η 0 s3' (Pc.mk0 0 0 t 0) _ :=
    (((((Lt.add (((L2.mul Lc).mul Lδ).mul (L1.sub (L2.mul Lν)))).sub
      ((L2.mul Lc).mul (Lea.add Lev))).mul Lomν).mul Lκi).congr_val
      (by rw [hs3']; ring)).congr (by pieces)
  have L1μ : Valid η 0 (1 - μ) (Pc.mk0 (1 - μ) 0 0 0) _ := (L1.sub Lμ).congr (by pieces)
  have Li : Valid η 0 (1 - μ)⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ :=
    (L1μ.inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have L1μ3 : Valid η 0 (1 - μ * (1 - 2 * c)) (Pc.mk0 (1 - μ) 0 0 0) _ :=
    (L1.sub Lμ3).congr (by pieces)
  have Li3 : Valid η 0 (1 - μ * (1 - 2 * c))⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ :=
    (L1μ3.inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  -- the correction terms
  have LAbv : Valid η 0 (Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xb xv)
      (Pc.mk0 0 0 (eb * ev / (μ - 1))
        (-(-δ * eb * μ + 2 * δ * eb - δ * ev * μ + δ * ev + eb * t + ev * t) / (μ - 1))) _ :=
    (Li3.acorr' Lκ Ls3 Lδ Lxb Lxv).congr (by unfold Pc.acorr; pieces)
  have LAav : Valid η 0 (Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv)
      (Pc.mk0 0 0 (ea * ev / (μ - 1)) (-(ea + ev) * (-δ * μ + 2 * δ + t) / (μ - 1))) _ :=
    (Li3.acorr' Lκ Ls3 Lδ Lxa Lxv).congr (by unfold Pc.acorr; pieces)
  have LAbv2 : Valid η 0 (Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xb (xv - δ3))
      (Pc.mk0 0 0 (eb * ev / (μ - 1))
        (-(-δ * eb * μ + 3 * δ * eb - δ * ev * μ + δ * ev + eb * t + ev * t) / (μ - 1))) _ :=
    (Li3.acorr' Lκ Ls3 Lδ Lxb (Lxv.sub Lδ3)).congr (by unfold Pc.acorr; pieces)
  have LT3 : Valid η 0 (Tcorr' (1 - μ * (1 - 2 * c))⁻¹ (μ * (1 - 2 * c)) δ xa xb)
      (Pc.mk0 0 0 δ (δ * (ea * μ - ea + eb * μ) / (μ - 1))) _ :=
    (L1.tcorr' Li3 Lμ3 Lδ Lxa Lxb).congr (by pieces)
  have LA0 : Valid η 0 (Acorr' (1 - μ)⁻¹ 1 s0' δ eb (ev - δ))
      (Pc.mk0 0 0 (eb * ev / (μ - 1))
        (-(-δ * eb * μ + 2 * δ * eb - δ * ev * μ + δ * ev + eb * t + ev * t) / (μ - 1))) _ :=
    (Li.acorr' L1 Ls0 Lδ Leb (Lev.sub Lδ)).congr (by unfold Pc.acorr; pieces)
  have LT0 : Valid η 0 (Tcorr' (1 - μ)⁻¹ μ δ ea eb)
      (Pc.mk0 0 0 δ (δ * (ea * μ - ea + eb * μ) / (μ - 1))) _ :=
    (L1.tcorr' Li Lμ Lδ Lea Leb).congr (by pieces)
  have LP : Valid η 0 ((1 - 2 * c) * (1 + xa) *
      (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv) * (1 + xv - δ3) *
      (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xb (xv - δ3)) *
      (1 + μ * Tcorr' (1 - μ * (1 - 2 * c))⁻¹ (μ * (1 - 2 * c)) δ xa xb))
      (Pc.mk0 1 (ea + ev)
        ((δ * μ ^ 2 - 4 * δ * μ + 3 * δ + 2 * ea * ev * μ - ea * ev + eb * ev * μ) / (μ - 1))
        (-(-3 * δ * ea * μ ^ 2 + 6 * δ * ea * μ - 2 * δ * ea - 2 * δ * eb * μ ^ 2 + 3 * δ * eb * μ
          - 3 * δ * ev * μ ^ 2 + 5 * δ * ev * μ - δ * ev - ea ^ 2 * ev * μ - ea * eb * ev * μ
          - ea * ev ^ 2 * μ + ea * μ * t - eb * ev ^ 2 * μ + eb * μ * t + 2 * ev * μ * t) /
          (μ - 1))) _ :=
    (((((Lκ.mul (L1.add Lxa)).mul (L1.add (Lμ.mul LAav))).mul ((L1.add Lxv).sub Lδ3)).mul
      (L1.add (Lμ.mul LAbv2))).mul (L1.add (Lμ.mul LT3))).congr (by pieces)
  have LQ : Valid η 0 ((1 - 2 * c) * (1 + xa) * (1 + xv) *
      (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv))
      (Pc.mk0 1 (ea + ev) (-(2 * δ * μ - 2 * δ - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (-(ea + ev) * (-δ * μ ^ 2 + 3 * δ * μ - δ - ea * ev * μ + μ * t) / (μ - 1))) _ :=
    ((((Lκ.mul (L1.add Lxa)).mul (L1.add Lxv)).mul (L1.add (Lμ.mul LAav)))).congr (by pieces)
  -- `yG`, written with `μ` factored out
  have LE : Valid η 0 (2 * c' +
        (Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xb xv -
          (1 - 2 * c) * (1 + xa) *
            (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv) * (1 + xv - δ3) *
            (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xb (xv - δ3)) *
            (1 + μ * Tcorr' (1 - μ * (1 - 2 * c))⁻¹ (μ * (1 - 2 * c)) δ xa xb)) -
      (1 - 2 * c) * (Acorr' (1 - μ)⁻¹ 1 s0' δ eb (ev - δ) + Tcorr' (1 - μ)⁻¹ μ δ ea eb -
        (1 - 2 * c) * (1 + xa) * (1 + xv) *
          (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv)) -
      (1 - 2 * c) * μ * (Acorr' (1 - μ)⁻¹ 1 s0' δ eb (ev - δ) * Tcorr' (1 - μ)⁻¹ μ δ ea eb -
        (1 - 2 * c) * (1 + xa) * (1 + xv) *
          (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv) *
          Acorr' (1 - μ)⁻¹ 1 s0' δ eb (ev - δ) -
        (1 - 2 * c) * (1 + xa) * (1 + xv) *
          (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv) *
          Tcorr' (1 - μ)⁻¹ μ δ ea eb) +
      (1 - 2 * c) * μ * μ * ((1 - 2 * c) * (1 + xa) * (1 + xv) *
        (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv) *
        Acorr' (1 - μ)⁻¹ 1 s0' δ eb (ev - δ) * Tcorr' (1 - μ)⁻¹ μ δ ea eb))
      (Pc.mk0 0 0 0 0) _ :=
    ((((L2.mul Lc').add (LAbv.sub LP)).sub
      (Lκ.mul ((LA0.add LT0).sub LQ))).sub
      ((Lκ.mul Lμ).mul (((LA0.mul LT0).sub (LQ.mul LA0)).sub (LQ.mul LT0)))).add
      (((Lκ.mul Lμ).mul Lμ).mul ((LQ.mul LA0).mul LT0)) |>.congr (by pieces)
  have LD : Valid η 0 ((1 - 2 * c) * ((1 - μ * ((1 - 2 * c) * (1 + xa) * (1 + xv) *
      (1 + μ * Acorr' (1 - μ * (1 - 2 * c))⁻¹ (1 - 2 * c) s3' δ xa xv))) *
      (1 + μ * Acorr' (1 - μ)⁻¹ 1 s0' δ eb (ev - δ)) * (1 + μ * Tcorr' (1 - μ)⁻¹ μ δ ea eb)))
      (Pc.mk0 (1 - μ) (-μ * (ea + ev))
        (-μ * (δ * μ ^ 2 - 4 * δ * μ + 3 * δ + 2 * ea * ev * μ - ea * ev + eb * ev * μ - eb * ev) /
          (μ - 1))
        (μ * (-3 * δ * ea * μ ^ 2 + 6 * δ * ea * μ - 2 * δ * ea - 2 * δ * eb * μ ^ 2
          + 4 * δ * eb * μ - 2 * δ * eb - 3 * δ * ev * μ ^ 2 + 6 * δ * ev * μ - 2 * δ * ev
          - ea ^ 2 * ev * μ - ea * eb * ev * μ - ea * ev ^ 2 * μ + ea * μ * t - eb * ev ^ 2 * μ
          + eb * μ * t - eb * t + 2 * ev * μ * t - ev * t) / (μ - 1))) _ :=
    (Lκ.mul (((L1.sub (Lμ.mul LQ)).mul (L1.add (Lμ.mul LA0))).mul (L1.add (Lμ.mul LT0)))).congr
      (by pieces)
  rw [hmud]
  constructor
  · refine LE.congr_val ?_
    rw [eq_div_iff hμ.ne', hcc]
    simp only [yNum, yDen, Acorr_eq', Acorr_eq'1, Tcorr_eq']
    ring
  · refine LD.congr_val ?_
    simp only [yDen, Acorr_eq', Acorr_eq'1, Tcorr_eq']
    ring

end LW
