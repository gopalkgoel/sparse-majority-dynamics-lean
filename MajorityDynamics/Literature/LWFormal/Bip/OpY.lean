import MajorityDynamics.Literature.LWFormal.Bip.Bad
import MajorityDynamics.Literature.LWFormal.OpY

set_option autoImplicit true

/-!
# Lemma 4.1(c): the expansion of `𝒴(P*, Y*)` (bipartite)

With `d₃ = d - e_a - e_v` and `μ₃, sS₃, sT₃, δT₃, x_a, x_v, x_b` its parameters,
`𝒴(P*,Y*)_{avb}(d) / Y*_{avb}(d) = yNumB / yDenB`. `opYB_expansion` shows
`(yNumB - yDenB) / μ = O(η⁴)` and `yDenB = 1 - μ + O(η)`.
-/

namespace LW.Bip

open Finset LW.TM

/-- `AcorrB (μκ) (μs) (μt) x y = μ · AcorrB' (1-μκ)⁻¹ κ s t x y`. -/
noncomputable def AcorrB' (i κ s t x y : ℝ) : ℝ := (-κ * x * y + x * t + y * s) * i

theorem AcorrB_eq' (μ κ s t x y : ℝ) :
    AcorrB (μ * κ) (μ * s) (μ * t) x y = μ * AcorrB' (1 - μ * κ)⁻¹ κ s t x y := by
  unfold AcorrB AcorrB'; ring

theorem AcorrB_eq'1 (μ s t x y : ℝ) :
    AcorrB μ (μ * s) (μ * t) x y = μ * AcorrB' (1 - μ)⁻¹ 1 s t x y := by
  unfold AcorrB AcorrB'; ring

/-- `TcB (μκ) δ xa xb = μ · Tcorr' (1-μκ)⁻¹ (μκ) (κδ) xa xb`. -/
theorem TcB_eq' (μ κ δ xa xb : ℝ) :
    TcB (μ * κ) δ xa xb = μ * Tcorr' (1 - μ * κ)⁻¹ (μ * κ) (κ * δ) xa xb := by
  unfold TcB Tcorr'; ring

theorem TcB_eq'1 (μ δ xa xb : ℝ) : TcB μ δ xa xb = μ * Tcorr' (1 - μ)⁻¹ μ δ xa xb := by
  unfold TcB Tcorr'; ring

end LW.Bip

namespace LW.TM

open LW.Bip

theorem Valid.acorrB' {η z i κ s t x y : ℝ} {ci cκ cs ct cx cy : Pc} {bi bκ bs bt bx by_ : Bd}
    (hi : Valid η z i ci bi) (hκ : Valid η z κ cκ bκ) (hs : Valid η z s cs bs)
    (ht : Valid η z t ct bt) (hx : Valid η z x cx bx) (hy : Valid η z y cy by_) :
    Valid η z (AcorrB' i κ s t x y) (Pc.acorrB cκ cs ct ci cx cy) (Bd.acorrB bκ bs bt bi bx by_) :=
  (((((hκ.neg.mul hx).mul hy).add (hx.mul ht)).add (hy.mul hs)).mul hi).congr_val
    (by unfold AcorrB'; ring)

end LW.TM

namespace LW.Bip

open Finset LW.TM

/-- `(P*_{bv}(d₃) - Y*_{avb}(d₃)) / (μ₃(1+x_b))`. -/
noncomputable def yNumB (μ3 sS3 sT3 δ3 xa xv xb : ℝ) : ℝ :=
  (1 + xv) * (1 + AcorrB μ3 sS3 sT3 xb xv) -
    piB μ3 sS3 sT3 xa xv * (1 + xv - δ3) * (1 + AcorrB μ3 sS3 sT3 xb (xv - δ3)) *
      (1 + TcB μ3 δ3 xa xb)

/-- `(1 - P*_{av}(d₃)) · Y*_{avb}(d) / (P*_{av}(d) μ (1+ε_b))`. -/
noncomputable def yDenB (μ sS0 sT0 δT ea ev eb μ3 sS3 sT3 xa xv : ℝ) : ℝ :=
  (1 + ev - δT) * (1 + AcorrB μ sS0 sT0 eb (ev - δT)) * (1 + TcB μ δT ea eb) *
    (1 - piB μ3 sS3 sT3 xa xv)

set_option maxHeartbeats 0 in
/-- `(yNumB - yDenB)/μ = O(η⁴)` and `yDenB = 1 - μ + O(η)`, where `νS = 1/n = μ δS`,
`νT = 1/ℓ = μ δT` and the primed quantities are the parameters of `d₃ = d - e_a - e_v`. -/
theorem opYB_expansion : ∃ bG bD : Bd,
    ∀ (η μ δS δT tS tT ea ev eb νS νT μ3 sS3 sT3 δT3 xa xv xb sS0 sT0 : ℝ),
    0 < η → η ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 4 → 0 < δS → δS ≤ η ^ 2 → 0 < δT → δT ≤ η ^ 2 →
    0 ≤ tS → tS ≤ η ^ 2 → 0 ≤ tT → tT ≤ η ^ 2 → |ea| ≤ η → |ev| ≤ η → |eb| ≤ η →
    νS = μ * δS → νT = μ * δT → μ3 = μ * (1 - δT * νS) →
    sS3 = (tS * μ + (1 - νT) * νT * νS * δS - 2 * ea * νT * νS) / (1 - δS * νT) →
    sT3 = (tT * μ + (1 - νS) * νS * νT * δT - 2 * ev * νS * νT) / (1 - δT * νS) →
    δT3 = δT / (1 - δT * νS) →
    xa = (ea - δS + δS * νT) / (1 - δS * νT) → xv = (ev - δT + δT * νS) / (1 - δT * νS) →
    xb = (eb + δS * νT) / (1 - δS * νT) → sS0 = μ * tS → sT0 = μ * tT →
    Valid η 0 ((yNumB μ3 sS3 sT3 δT3 xa xv xb - yDenB μ sS0 sT0 δT ea ev eb μ3 sS3 sT3 xa xv) / μ)
      (Pc.mk0 0 0 0 0) bG ∧
    Valid η 0 (yDenB μ sS0 sT0 δT ea ev eb μ3 sS3 sT3 xa xv)
      (Pc.mk0 (1 - μ) (-ea * μ - 2 * ev * μ + ev)
        ((δS * μ ^ 2 - δS * μ - δT * μ ^ 3 + 4 * δT * μ ^ 2 - 4 * δT * μ + δT - 3 * ea * ev * μ ^ 2
          + 2 * ea * ev * μ - eb * ev * μ ^ 2 + eb * ev * μ - ev ^ 2 * μ ^ 2 + ev ^ 2 * μ) / (μ - 1))
        (μ * (3 * δS * ev * μ - 2 * δS * ev - 2 * δT * ea * μ ^ 2 + 6 * δT * ea * μ - 3 * δT * ea
          - δT * eb * μ ^ 2 + 2 * δT * eb * μ - δT * eb - 2 * δT * ev * μ ^ 2 + 5 * δT * ev * μ
          - 3 * δT * ev - ea ^ 2 * ev * μ - ea * eb * ev * μ - 3 * ea * ev ^ 2 * μ + ea * ev ^ 2
          + ea * μ * tT - 2 * eb * ev ^ 2 * μ + eb * ev ^ 2 + eb * μ * tT - eb * tT + 2 * ev * μ * tS
          - ev * tS) / (μ - 1))) bD := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  intro η μ δS δT tS tT ea ev eb νS νT μ3 sS3 sT3 δT3 xa xv xb sS0 sT0 hη hη2 hμ hμ4 hδS hδSη hδT
    hδTη htS htSη htT htTη hea hev heb hνS hνT hμ3 hsS3 hsT3 hδT3 hxa hxv hxb hsS0 hsT0
  have hμ1 : μ - 1 ≠ 0 := by linarith
  have h1μ : (1 : ℝ) - μ ≠ 0 := by linarith
  have hη4 : η ^ 2 ≤ 1 / 4 := by nlinarith
  have hcpos : 0 < δT * νS := by rw [hνS]; positivity
  have hcη : δT * νS ≤ 1 / 64 := by
    rw [hνS]
    calc δT * (μ * δS) ≤ 1 / 4 * (1 / 4 * (1 / 4)) := by gcongr <;> linarith
      _ = 1 / 64 := by norm_num
  have hcST : δS * νT = δT * νS := by rw [hνS, hνT]; ring
  have hc1 : 1 - δT * νS ≠ 0 := by linarith
  -- factor `μ` out of `sS₃`, `sT₃`
  obtain ⟨sS3', hsS3'⟩ : ∃ x, x =
    (tS + (1 - νT) * δT * νS * δS - 2 * ea * δT * νS) / (1 - δS * νT) := ⟨_, rfl⟩
  obtain ⟨sT3', hsT3'⟩ : ∃ x, x =
    (tT + (1 - νS) * δS * νT * δT - 2 * ev * δS * νT) / (1 - δT * νS) := ⟨_, rfl⟩
  have hsS3'' : sS3 = μ * sS3' := by rw [hsS3, hsS3', hνT]; ring
  have hsT3'' : sT3 = μ * sT3' := by rw [hsT3, hsT3', hνS]; ring
  subst hsS3'' hsT3'' hμ3 hsS0 hsT0
  -- leaves
  have L1 : Valid η 0 1 (Pc.single 0 0 1) _ := Valid.const zero_le_one (by simp)
  have Lμ : Valid η 0 μ (Pc.single 0 0 μ) _ :=
    Valid.const (A := 1 / 4) (by norm_num) (by rw [abs_of_pos hμ]; exact hμ4)
  have LδS : Valid η 0 δS (Pc.single 2 0 δS) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδS]; simpa using hδSη)
  have LδT : Valid η 0 δT (Pc.single 2 0 δT) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδT]; simpa using hδTη)
  have LtS : Valid η 0 tS (Pc.single 2 0 tS) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg htS]; simpa using htSη)
  have LtT : Valid η 0 tT (Pc.single 2 0 tT) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg htT]; simpa using htTη)
  have Lea : Valid η 0 ea (Pc.single 1 0 ea) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Lev : Valid η 0 ev (Pc.single 1 0 ev) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hev)
  have Leb : Valid η 0 eb (Pc.single 1 0 eb) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using heb)
  have L2 : Valid η 0 2 (Pc.single 0 0 2) _ := Valid.const (A := 2) (by norm_num) (by simp)
  -- derived quantities
  have LνS : Valid η 0 νS (Pc.mk0 0 0 (μ * δS) 0) _ :=
    ((Lμ.mul LδS).congr_val hνS.symm).congr (by pieces)
  have LνT : Valid η 0 νT (Pc.mk0 0 0 (μ * δT) 0) _ :=
    ((Lμ.mul LδT).congr_val hνT.symm).congr (by pieces)
  have Lc : Valid η 0 (δT * νS) (Pc.mk0 0 0 0 0) _ := (LδT.mul LνS).congr (by pieces)
  have LcS : Valid η 0 (δS * νT) (Pc.mk0 0 0 0 0) _ := (LδS.mul LνT).congr (by pieces)
  have Lc' : Valid η 0 (δS * δT) (Pc.mk0 0 0 0 0) _ := (LδS.mul LδT).congr (by pieces)
  have Lκ : Valid η 0 (1 - δT * νS) (Pc.mk0 1 0 0 0) _ := (L1.sub Lc).congr (by pieces)
  have Lκi : Valid η 0 (1 - δT * νS)⁻¹ (Pc.mk0 1 0 0 0) _ :=
    (Lκ.inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have LκS : Valid η 0 (1 - δS * νT) (Pc.mk0 1 0 0 0) _ := (L1.sub LcS).congr (by pieces)
  have LκSi : Valid η 0 (1 - δS * νT)⁻¹ (Pc.mk0 1 0 0 0) _ :=
    (LκS.inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lμ3 : Valid η 0 (μ * (1 - δT * νS)) (Pc.mk0 μ 0 0 0) _ := (Lμ.mul Lκ).congr (by pieces)
  have L1μ : Valid η 0 (1 - μ) (Pc.mk0 (1 - μ) 0 0 0) _ := (L1.sub Lμ).congr (by pieces)
  have Li : Valid η 0 (1 - μ)⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ :=
    (L1μ.inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have L1μ3 : Valid η 0 (1 - μ * (1 - δT * νS)) (Pc.mk0 (1 - μ) 0 0 0) _ :=
    (L1.sub Lμ3).congr (by pieces)
  have Li3 : Valid η 0 (1 - μ * (1 - δT * νS))⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ :=
    (L1μ3.inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have Lxa : Valid η 0 xa (Pc.mk0 0 ea (-δS) 0) _ :=
    ((((Lea.sub LδS).add LcS).mul LκSi).congr_val (by rw [hxa]; ring)).congr (by pieces)
  have Lxv : Valid η 0 xv (Pc.mk0 0 ev (-δT) 0) _ :=
    ((((Lev.sub LδT).add Lc).mul Lκi).congr_val (by rw [hxv]; ring)).congr (by pieces)
  have Lxb : Valid η 0 xb (Pc.mk0 0 eb 0 0) _ :=
    (((Leb.add LcS).mul LκSi).congr_val (by rw [hxb]; ring)).congr (by pieces)
  have LδT3 : Valid η 0 δT3 (Pc.mk0 0 0 δT 0) _ :=
    ((LδT.mul Lκi).congr_val (by rw [hδT3]; ring)).congr (by pieces)
  have LsS3 : Valid η 0 sS3' (Pc.mk0 0 0 tS 0) _ :=
    ((((LtS.add ((((L1.sub LνT).mul LδT).mul LνS).mul LδS)).sub
      (((L2.mul Lea).mul LδT).mul LνS)).mul LκSi).congr_val (by rw [hsS3']; ring)).congr
      (by pieces)
  have LsT3 : Valid η 0 sT3' (Pc.mk0 0 0 tT 0) _ :=
    ((((LtT.add ((((L1.sub LνS).mul LδS).mul LνT).mul LδT)).sub
      (((L2.mul Lev).mul LδS).mul LνT)).mul Lκi).congr_val (by rw [hsT3']; ring)).congr
      (by pieces)
  -- correction terms at `d₃` and at `d`
  have LAbv : Valid η 0 (AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xb xv)
      (Pc.mk0 0 0 (eb * ev / (μ - 1)) (-(δT * eb + eb * tT + ev * tS) / (μ - 1))) _ :=
    (Li3.acorrB' Lκ LsS3 LsT3 Lxb Lxv).congr (by unfold Pc.acorrB; pieces)
  have LAbw : Valid η 0 (AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xb (xv - δT3))
      (Pc.mk0 0 0 (eb * ev / (μ - 1)) (-(2 * δT * eb + eb * tT + ev * tS) / (μ - 1))) _ :=
    (Li3.acorrB' Lκ LsS3 LsT3 Lxb (Lxv.sub LδT3)).congr (by unfold Pc.acorrB; pieces)
  have LAav : Valid η 0 (AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xa xv)
      (Pc.mk0 0 0 (ea * ev / (μ - 1)) (-(δS * ev + δT * ea + ea * tT + ev * tS) / (μ - 1))) _ :=
    (Li3.acorrB' Lκ LsS3 LsT3 Lxa Lxv).congr (by unfold Pc.acorrB; pieces)
  have LT3 : Valid η 0 (Tcorr' (1 - μ * (1 - δT * νS))⁻¹ (μ * (1 - δT * νS)) ((1 - δT * νS) * δT3)
      xa xb) (Pc.mk0 0 0 δT (δT * (ea * μ - ea + eb * μ) / (μ - 1))) _ :=
    (L1.tcorr' Li3 Lμ3 (Lκ.mul LδT3) Lxa Lxb).congr (by pieces)
  have LA0 : Valid η 0 (AcorrB' (1 - μ)⁻¹ 1 tS tT eb (ev - δT))
      (Pc.mk0 0 0 (eb * ev / (μ - 1)) (-(δT * eb + eb * tT + ev * tS) / (μ - 1))) _ :=
    (Li.acorrB' L1 LtS LtT Leb (Lev.sub LδT)).congr (by unfold Pc.acorrB; pieces)
  have LT0 : Valid η 0 (Tcorr' (1 - μ)⁻¹ μ δT ea eb)
      (Pc.mk0 0 0 δT (δT * (ea * μ - ea + eb * μ) / (μ - 1))) _ :=
    (L1.tcorr' Li Lμ LδT Lea Leb).congr (by pieces)
  have LQ : Valid η 0 ((1 - δT * νS) * (1 + xa) * (1 + xv) *
      (1 + μ * AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xa xv))
      (Pc.mk0 1 (ea + ev) (-(δS * μ - δS + δT * μ - δT - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (-(2 * δS * ev * μ - δS * ev + 2 * δT * ea * μ - δT * ea - ea ^ 2 * ev * μ
          - ea * ev ^ 2 * μ + ea * μ * tT + ev * μ * tS) / (μ - 1))) _ :=
    (((Lκ.mul (L1.add Lxa)).mul (L1.add Lxv)).mul (L1.add (Lμ.mul LAav))).congr (by pieces)
  have LP : Valid η 0 ((1 + xv - δT3) *
      (1 + μ * AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xb (xv - δT3)) *
      (1 + μ * Tcorr' (1 - μ * (1 - δT * νS))⁻¹ (μ * (1 - δT * νS)) ((1 - δT * νS) * δT3) xa xb))
      (Pc.mk0 1 ev ((δT * μ ^ 2 - 3 * δT * μ + 2 * δT + eb * ev * μ) / (μ - 1))
        (μ * (δT * ea * μ - δT * ea + δT * eb * μ - 2 * δT * eb + δT * ev * μ - δT * ev
          + eb * ev ^ 2 - eb * tT - ev * tS) / (μ - 1))) _ :=
    ((((L1.add Lxv).sub LδT3).mul (L1.add (Lμ.mul LAbw))).mul (L1.add (Lμ.mul LT3))).congr
      (by pieces)
  -- `(yNumB - yDenB)/μ` and `yDenB`
  have LE : Valid η 0 (δS * δT * (1 + ev - δT) * (1 - δT * νS)⁻¹ +
      (1 + xv) * AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xb xv -
      (1 - δT * νS) * (1 + xa) * (1 + xv) *
        (1 + μ * AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xa xv) *
        ((1 + xv - δT3) *
          (1 + μ * AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xb (xv - δT3)) *
          (1 + μ * Tcorr' (1 - μ * (1 - δT * νS))⁻¹ (μ * (1 - δT * νS)) ((1 - δT * νS) * δT3)
            xa xb)) -
      (1 + ev - δT) * (AcorrB' (1 - μ)⁻¹ 1 tS tT eb (ev - δT) + Tcorr' (1 - μ)⁻¹ μ δT ea eb +
        μ * AcorrB' (1 - μ)⁻¹ 1 tS tT eb (ev - δT) * Tcorr' (1 - μ)⁻¹ μ δT ea eb) +
      (1 - δT * νS) * (1 + xa) * (1 + xv) *
        (1 + μ * AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xa xv) *
        (1 + ev - δT) * (1 + μ * AcorrB' (1 - μ)⁻¹ 1 tS tT eb (ev - δT)) *
        (1 + μ * Tcorr' (1 - μ)⁻¹ μ δT ea eb))
      (Pc.mk0 0 0 0 0) _ :=
    ((((((Lc'.mul ((L1.add Lev).sub LδT)).mul Lκi).add ((L1.add Lxv).mul LAbv)).sub
      (LQ.mul LP)).sub (((L1.add Lev).sub LδT).mul ((LA0.add LT0).add ((Lμ.mul LA0).mul LT0)))).add
      ((((LQ.mul ((L1.add Lev).sub LδT)).mul (L1.add (Lμ.mul LA0))).mul
        (L1.add (Lμ.mul LT0))))).congr (by pieces)
  have LD : Valid η 0 ((1 + ev - δT) * (1 + μ * AcorrB' (1 - μ)⁻¹ 1 tS tT eb (ev - δT)) *
      (1 + μ * Tcorr' (1 - μ)⁻¹ μ δT ea eb) *
      (1 - μ * ((1 - δT * νS) * (1 + xa) * (1 + xv) *
        (1 + μ * AcorrB' (1 - μ * (1 - δT * νS))⁻¹ (1 - δT * νS) sS3' sT3' xa xv))))
      (Pc.mk0 (1 - μ) (-ea * μ - 2 * ev * μ + ev)
        ((δS * μ ^ 2 - δS * μ - δT * μ ^ 3 + 4 * δT * μ ^ 2 - 4 * δT * μ + δT - 3 * ea * ev * μ ^ 2
          + 2 * ea * ev * μ - eb * ev * μ ^ 2 + eb * ev * μ - ev ^ 2 * μ ^ 2 + ev ^ 2 * μ) / (μ - 1))
        (μ * (3 * δS * ev * μ - 2 * δS * ev - 2 * δT * ea * μ ^ 2 + 6 * δT * ea * μ - 3 * δT * ea
          - δT * eb * μ ^ 2 + 2 * δT * eb * μ - δT * eb - 2 * δT * ev * μ ^ 2 + 5 * δT * ev * μ
          - 3 * δT * ev - ea ^ 2 * ev * μ - ea * eb * ev * μ - 3 * ea * ev ^ 2 * μ + ea * ev ^ 2
          + ea * μ * tT - 2 * eb * ev ^ 2 * μ + eb * ev ^ 2 + eb * μ * tT - eb * tT + 2 * ev * μ * tS
          - ev * tS) / (μ - 1))) _ :=
    (((((L1.add Lev).sub LδT).mul (L1.add (Lμ.mul LA0))).mul (L1.add (Lμ.mul LT0))).mul
      (L1.sub (Lμ.mul LQ))).congr (by pieces)
  constructor
  · refine LE.congr_val ?_
    rw [eq_div_iff hμ.ne']
    simp only [yNumB, yDenB, piB, AcorrB_eq', AcorrB_eq'1, TcB_eq', TcB_eq'1 μ δT ea eb]
    have hxv' : 1 + xv = (1 + ev - δT) * (1 - δT * νS)⁻¹ := by
      rw [hxv, ← div_eq_mul_inv, eq_div_iff hc1]; field_simp; ring
    have hκ : (1 - δT * νS) * (1 - δT * νS)⁻¹ = 1 := mul_inv_cancel₀ hc1
    rw [hxv']
    subst hνS
    linear_combination -(1 + ev - δT) * hκ
  · refine LD.congr_val ?_
    simp only [yDenB, piB, AcorrB_eq', AcorrB_eq'1, TcB_eq'1 μ δT ea eb]
    ring

end LW.Bip
