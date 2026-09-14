import MajorityDynamics.Literature.LWFormal.Expansion
import MajorityDynamics.Literature.LWFormal.Bip.Approx

set_option autoImplicit true

/-!
# Lemma 4.1(a): the expansion of `bad(P*, Y*)` and of `ℛ(P*,Y*)/R*`

`badB_expansion` computes `bad(P*,Y*)_{ab}(d - e_b) / μ` to third order in `η` (where `|ε| ≤ η`,
`1/s̄, 1/t̄, σ_S²/s̄², σ_T²/t̄² ≤ η²`) with an explicit `O(η⁴)` remainder; the parameters are those
of the `S`-heavy sequence `d`, with `1/n = μ δS (1 + c')`, `1/ℓ = μ δT (1 - c')`, `|c'| ≤ μ δS δT`.
-/

namespace LW.Bip

open Finset LW.TM

/-- The `v`-dependent part of `Y*_{avb} / (μ²(1+ε_a)(1+ε_b)(1+TcB))`, `y = ε_v`. -/
noncomputable def GfunB (μ sS sT δT xa xb y : ℝ) : ℝ :=
  (1 + y) * (1 + y - δT) * (1 + AcorrB μ sS sT xa y) * (1 + AcorrB μ sS sT xb (y - δT))

/-- `bad(P*, Y*)_{ab}` written in terms of the parameters of the sequence. -/
noncomputable def badB {ι : Type*} (xa xb : ℝ) (V : Finset ι) (ε : ι → ℝ) (μ sS sT δT da : ℝ) :
    ℝ :=
  (∑ v ∈ V, piB μ sS sT xa (ε v) * piB μ sS sT xb (ε v - δT) * (1 + TcB μ δT xa xb)) / da

theorem bad_eq {ℓ n : ℕ} {a b : Fin ℓ} (d : BSeq ℓ n) (hab : a ≠ b) :
    bad Pst Yst a b d =
      badB (eps d.1 a) (eps d.1 b) univ (eps d.2) (mu d) (sS d) (sT d) (1 / dbar d.2) (d.1 a) := by
  simp only [bad, badB, Pst, Yst, if_neg hab]

/-- `bad / μ = pref * (∑_v G_v)/n`. -/
theorem badB_decomp {ι : Type*} (V : Finset ι) (ε : ι → ℝ) (xa xb μ sS' sT' δT δS ea c' r : ℝ)
    (n : ℕ) (hμ : μ ≠ 0) (hea : 1 + ea ≠ 0) (hn : (n : ℝ) ≠ 0) (hc' : 1 + c' ≠ 0)
    (hνS : 1 / (n : ℝ) = μ * δS * (1 + c')) :
    badB xa xb V ε (μ * r) sS' sT' δT (1 / δS * (1 + ea)) / μ =
      r ^ 2 * (1 + c')⁻¹ * (1 + xa) * (1 + xb) * (1 + TcB (μ * r) δT xa xb) * (1 + ea)⁻¹ *
        ((∑ v ∈ V, GfunB (μ * r) sS' sT' δT xa xb (ε v)) / n) := by
  have hδS : δS ≠ 0 := fun h => hn (by rw [h] at hνS; simpa using hνS)
  have hsum : ∑ v ∈ V, piB (μ * r) sS' sT' xa (ε v) * piB (μ * r) sS' sT' xb (ε v - δT) *
      (1 + TcB (μ * r) δT xa xb) =
      (μ * r) ^ 2 * (1 + xa) * (1 + xb) * (1 + TcB (μ * r) δT xa xb) *
        ∑ v ∈ V, GfunB (μ * r) sS' sT' δT xa xb (ε v) := by
    rw [mul_sum]; refine sum_congr rfl fun v _ => ?_; unfold piB GfunB; ring
  unfold badB
  rw [hsum, div_eq_mul_one_div (∑ v ∈ V, _) (n : ℝ), hνS]
  field_simp

end LW.Bip

namespace LW.TM

open LW.Bip

/-- Pieces of `AcorrB` from pieces of its arguments (`i = (1-μ)⁻¹`). -/
def Pc.acorrB (cμ cs ct ci cx cy : Pc) : Pc :=
  Pc.mul (Pc.add (Pc.add (Pc.mul (Pc.mul (Pc.neg cμ) cx) cy) (Pc.mul cx ct)) (Pc.mul cy cs)) ci

def Bd.acorrB (bμ bs bt bi bx by_ : Bd) : Bd :=
  Bd.mul (Bd.add (Bd.add (Bd.mul (Bd.mul bμ bx) by_) (Bd.mul bx bt)) (Bd.mul by_ bs)) bi

theorem Valid.acorrB {η z μ s t i x y : ℝ} {cμ cs ct ci cx cy : Pc} {bμ bs bt bi bx by_ : Bd}
    (hμ : Valid η z μ cμ bμ) (hs : Valid η z s cs bs) (ht : Valid η z t ct bt)
    (hi : Valid η z i ci bi) (hix : i = (1 - μ)⁻¹) (hx : Valid η z x cx bx)
    (hy : Valid η z y cy by_) :
    Valid η z (AcorrB μ s t x y) (Pc.acorrB cμ cs ct ci cx cy) (Bd.acorrB bμ bs bt bi bx by_) :=
  (((((hμ.neg.mul hx).mul hy).add (hx.mul ht)).add (hy.mul hs)).mul hi).congr_val
    (by subst hix; unfold AcorrB; ring)

end LW.TM

namespace LW.Bip

open Finset LW.TM

set_option maxHeartbeats 0 in
/-- Third-order expansion of `bad(P*,Y*)_{ab}(d - e_b) / μ` in the normalised variables
`δS = 1/s̄`, `δT = 1/t̄`, `tS = σ_S²/s̄²`, `tT = σ_T²/t̄²`, `s₃ = n⁻¹ ∑ ε_v³`, `ea = ε_a`, `eb = ε_b`,
`νS = 1/n`, `νT = 1/ℓ`; the primed quantities are those of `d - e_b`, `V = [n]`. -/
theorem badB_expansion : ∃ b : Bd, ∀ {ι : Type} (η μ δS δT tS tT s₃ ea eb c' νS νT : ℝ) (n : ℕ)
    (V : Finset ι) (ε : ι → ℝ) (μ' sS' sT' xa xb : ℝ),
    0 < η → η ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 4 → 0 < δS → δS ≤ η ^ 2 → 0 < δT → δT ≤ η ^ 2 →
    0 ≤ tS → tS ≤ η ^ 2 → 0 ≤ tT → tT ≤ η ^ 2 → |s₃| ≤ η ^ 3 → |ea| ≤ η → |eb| ≤ η →
    (∀ v ∈ V, |ε v| ≤ η) → |c'| ≤ μ * δS * δT → 0 < n → V.card = n →
    1 / (n : ℝ) = νS → νS = μ * δS * (1 + c') → νT = μ * δT * (1 - c') →
    ∑ v ∈ V, ε v = 0 → ∑ v ∈ V, ε v ^ 2 = n * tT → ∑ v ∈ V, ε v ^ 3 = n * s₃ →
    μ' = μ * (1 - δS * νT * (1 + c') / 2) →
    xa = (ea + δS * νT) / (1 - δS * νT) → xb = (eb - δS + δS * νT) / (1 - δS * νT) →
    sS' = (tS * (μ * (1 + c')) + (1 - νT) * νT * νS * δS - 2 * eb * νT * νS) / (1 - δS * νT) →
    sT' = tT * (μ * (1 - c')) →
    Valid η 0 (badB xa xb V ε μ' sS' sT' δT (1 / δS * (1 + ea)) / μ)
      (Pc.mk0 1 eb (-δS + δT * μ - δT + tT)
        ((δT * μ - δT + tT) * (ea * μ + 2 * eb * μ - eb) / (μ - 1))) b := by
  refine ⟨?_, ?_⟩
  swap
  intro ι η μ δS δT tS tT s₃ ea eb c' νS νT n V ε μ' sS' sT' xa xb hη hη2 hμ hμ4 hδS hδSη hδT hδTη
    htS htSη htT htTη hs3 hea heb hεV hc' hn hcard hnν hνS hνT hm1 hm2 hm3 hμ' hxa hxb hsS hsT
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ1 : μ - 1 ≠ 0 := by linarith
  have h1μ : (1 : ℝ) - μ ≠ 0 := by linarith
  have hμ0 := hμ.ne'
  have hδS0 := hδS.ne'
  have hδT0 := hδT.ne'
  have hea1 : 1 + ea ≠ 0 := by have := (abs_le.1 hea).1; linarith
  have hμδδ : 0 < μ * δS * δT := by positivity
  have hη4 : η ^ 2 ≤ 1 / 4 := by nlinarith
  have hsmall : μ * δS * δT ≤ 1 / 4 * (1 / 4) * (1 / 4) := by
    gcongr <;> linarith
  have hc'1 : 1 + c' ≠ 0 := by have := (abs_le.1 hc').1; linarith
  have hcardR : (V.card : ℝ) = n := by rw [hcard]
  have hne : V.Nonempty := by rw [← Finset.card_pos, hcard]; exact hn
  -- leaves (valid for every `z`)
  have L1 : ∀ z, Valid η z 1 (Pc.single 0 0 1) _ := fun z => Valid.const zero_le_one (by simp)
  have Lμ : ∀ z, Valid η z μ (Pc.single 0 0 μ) _ := fun z =>
    Valid.const (A := 1 / 4) (by norm_num) (by rw [abs_of_pos hμ]; exact hμ4)
  have LδS : ∀ z, Valid η z δS (Pc.single 2 0 δS) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδS]; simpa using hδSη)
  have LδT : ∀ z, Valid η z δT (Pc.single 2 0 δT) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδT]; simpa using hδTη)
  have LtS : ∀ z, Valid η z tS (Pc.single 2 0 tS) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg htS]; simpa using htSη)
  have LtT : ∀ z, Valid η z tT (Pc.single 2 0 tT) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg htT]; simpa using htTη)
  have Ls3 : ∀ z, Valid η z s₃ (Pc.single 3 0 s₃) _ := fun z =>
    Valid.leaf 3 (by norm_num) zero_le_one (by simpa using hs3)
  have Lea : ∀ z, Valid η z ea (Pc.single 1 0 ea) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Leb : ∀ z, Valid η z eb (Pc.single 1 0 eb) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using heb)
  have Lκ : ∀ z, Valid η z (c' / (μ * δS * δT)) (Pc.single 0 0 (c' / (μ * δS * δT))) _ := fun z =>
    Valid.const zero_le_one (by rw [abs_div, abs_of_pos hμδδ, div_le_one hμδδ]; exact hc')
  have L2 : ∀ z, Valid η z 2 (Pc.single 0 0 2) _ := fun z => Valid.const (A := 2) (by norm_num) (by simp)
  have Lhalf : ∀ z, Valid η z (1 / 2) (Pc.single 0 0 (1 / 2)) _ := fun z =>
    Valid.const (A := 1 / 2) (by norm_num) (by rw [abs_of_pos (by norm_num)])
  -- derived `z`-free quantities
  have Lc' : ∀ z, Valid η z c' (Pc.mk0 0 0 0 0) _ := fun z =>
    (((((Lμ z).mul (LδS z)).mul (LδT z)).mul (Lκ z)).congr_val (by field_simp)).congr (by pieces)
  have LνS : ∀ z, Valid η z νS (Pc.mk0 0 0 (μ * δS) 0) _ := fun z =>
    ((((Lμ z).mul (LδS z)).mul ((L1 z).add (Lc' z))).congr_val hνS.symm).congr (by pieces)
  have LνT : ∀ z, Valid η z νT (Pc.mk0 0 0 (μ * δT) 0) _ := fun z =>
    ((((Lμ z).mul (LδT z)).mul ((L1 z).sub (Lc' z))).congr_val hνT.symm).congr (by pieces)
  have LcS : ∀ z, Valid η z (δS * νT) (Pc.mk0 0 0 0 0) _ := fun z =>
    ((LδS z).mul (LνT z)).congr (by pieces)
  have Lomc : ∀ z, Valid η z (1 - δS * νT) (Pc.mk0 1 0 0 0) _ := fun z =>
    ((L1 z).sub (LcS z)).congr (by pieces)
  have Lomci : ∀ z, Valid η z (1 - δS * νT)⁻¹ (Pc.mk0 1 0 0 0) _ := fun z =>
    ((Lomc z).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lr : ∀ z, Valid η z (1 - δS * νT * (1 + c') / 2) (Pc.mk0 1 0 0 0) _ := fun z =>
    (((L1 z).sub (((LcS z).mul ((L1 z).add (Lc' z))).mul (Lhalf z))).congr_val (by ring)).congr
      (by pieces)
  have Lμ' : ∀ z, Valid η z μ' (Pc.mk0 μ 0 0 0) _ := fun z =>
    (((Lμ z).mul (Lr z)).congr_val hμ'.symm).congr (by pieces)
  have Lxa : ∀ z, Valid η z xa (Pc.mk0 0 ea 0 0) _ := fun z =>
    ((((Lea z).add (LcS z)).mul (Lomci z)).congr_val (by rw [hxa]; ring)).congr (by pieces)
  have Lxb : ∀ z, Valid η z xb (Pc.mk0 0 eb (-δS) 0) _ := fun z =>
    (((((Leb z).sub (LδS z)).add (LcS z)).mul (Lomci z)).congr_val (by rw [hxb]; ring)).congr
      (by pieces)
  have LsS : ∀ z, Valid η z sS' (Pc.mk0 0 0 (μ * tS) 0) _ := fun z =>
    (((((LtS z).mul ((Lμ z).mul ((L1 z).add (Lc' z)))).add
        (((((L1 z).sub (LνT z)).mul (LνT z)).mul (LνS z)).mul (LδS z))).sub
        ((((L2 z).mul (Leb z)).mul (LνT z)).mul (LνS z))).mul (Lomci z)).congr_val
      (by rw [hsS]; ring) |>.congr (by pieces)
  have LsT : ∀ z, Valid η z sT' (Pc.mk0 0 0 (μ * tT) 0) _ := fun z =>
    (((LtT z).mul ((Lμ z).mul ((L1 z).sub (Lc' z)))).congr_val hsT.symm).congr (by pieces)
  have Li1mmup : ∀ z, Valid η z (1 - μ')⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    (((L1 z).sub (Lμ' z)).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) + -μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have Li1pea : ∀ z, Valid η z (1 + ea)⁻¹ (Pc.mk0 1 (-ea) (ea ^ 2) (-ea ^ 3)) _ := fun z =>
    (((L1 z).add (Lea z)).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ) + 0|; norm_num)).congr
      (by pieces)
  have Li1pc : ∀ z, Valid η z (1 + c')⁻¹ (Pc.mk0 1 0 0 0) _ := fun z =>
    (((L1 z).add (Lc' z)).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ) + 0|; norm_num)).congr
      (by pieces)
  have LTp : ∀ z, Valid η z (TcB μ' δT xa xb)
      (Pc.mk0 0 0 (δT * μ) (δT * μ * (ea * μ - ea + eb * μ) / (μ - 1))) _ := fun z =>
    ((((LδT z).mul (((Lμ' z).mul ((L1 z).add (Lxa z))).sub
      (((Lμ' z).mul (Lμ' z)).mul (((L1 z).add (Lxa z)).add (Lxb z))))).mul
      (Li1mmup z)).congr_val (by unfold TcB; ring)).congr (by pieces)
  -- the `v`-dependent factor, expanded in `z = ε v`
  have hG : ∀ v ∈ V, Valid η (ε v) (GfunB μ' sS' sT' δT xa xb (ε v))
      (Pc.mk 1 0 2 (-δT) (μ * (ea + eb) / (μ - 1)) 1
        (-μ * (δT * eb + ea * tT + eb * tT) / (μ - 1))
        (-(δS * μ + δT * μ - δT + 2 * μ * tS) / (μ - 1)) (2 * μ * (ea + eb) / (μ - 1)) 0) _ :=
    fun v hv =>
    have hz : Valid η (ε v) (ε v) (Pc.single 1 1 1) _ := Valid.var
    have hAav : Valid η (ε v) (AcorrB μ' sS' sT' xa (ε v))
        (Pc.mk 0 0 0 0 (ea * μ / (μ - 1)) 0 (-ea * μ * tT / (μ - 1)) (-μ * tS / (μ - 1)) 0 0) _ :=
      ((Lμ' _).acorrB (LsS _) (LsT _) (Li1mmup _) rfl (Lxa _) hz).congr
        (by unfold Pc.acorrB; pieces)
    have hAbv : Valid η (ε v) (AcorrB μ' sS' sT' xb (ε v - δT))
        (Pc.mk 0 0 0 0 (eb * μ / (μ - 1)) 0 (-eb * μ * (δT + tT) / (μ - 1))
          (-μ * (δS + tS) / (μ - 1)) 0 0) _ :=
      ((Lμ' _).acorrB (LsS _) (LsT _) (Li1mmup _) rfl (Lxb _) (hz.sub (LδT _))).congr
        (by unfold Pc.acorrB; pieces)
    (((((L1 _).add hz).mul (((L1 _).add hz).sub (LδT _))).mul
      ((L1 _).add hAav)).mul ((L1 _).add hAbv)).congr_val (by unfold GfunB; ring) |>.congr
      (by pieces)
  -- moments of `ε` over `V`
  have LP1 : Valid η 0 (0 : ℝ) (Pc.single 0 0 0) _ := Valid.const le_rfl (by simp)
  have Lavg : Valid η 0 ((∑ v ∈ V, GfunB μ' sS' sT' δT xa xb (ε v)) / n)
      (Pc.mk0 1 0 (-δT + tT) (-μ * (δT * eb - ea * tT - eb * tT) / (μ - 1))) _ :=
    (Valid.avg4 hne hεV hG hn0 hcardR.le
      (by simp [hcardR]; field_simp)
      (by simp only [pow_one, hm1, zero_div])
      (by rw [hm2]; field_simp)
      (by rw [hm3]; field_simp) (L1 0) LP1 (LtT 0) (Ls3 0)).congr (by pieces)
  have Lpref : Valid η 0 ((1 - δS * νT * (1 + c') / 2) ^ 2 * (1 + c')⁻¹ * (1 + xa) * (1 + xb) *
      (1 + TcB μ' δT xa xb) * (1 + ea)⁻¹)
      (Pc.mk0 1 eb (-δS + δT * μ) (δT * μ * (ea * μ - ea + 2 * eb * μ - eb) / (μ - 1))) _ :=
    (((((((Lr 0).mul (Lr 0)).mul (Li1pc 0)).mul ((L1 0).add (Lxa 0))).mul
      ((L1 0).add (Lxb 0))).mul ((L1 0).add (LTp 0))).mul (Li1pea 0)).congr_val (by ring)
      |>.congr (by pieces)
  rw [hμ', badB_decomp V ε xa xb μ sS' sT' δT δS ea c' _ n hμ0 hea1 hn0.ne' hc'1 (hnν.trans hνS),
    ← hμ']
  refine (Lpref.mul Lavg).congr ?_
  pieces

/-! ### The ratio `ℛ(P*,Y*)/R*`

With `Fab = bad_{ab}(d-e_b)/μ`, `Fba = bad_{ba}(d-e_a)/μ`: `ℛ/R* - 1 = μ · ratioG / ratioD`. -/

/-- `K = (ε_a - ε_b)(1-c')(tT/(1-μ) - δT)/(1-μ)`, so that `R* = (1+ε_a)/(1+ε_b) · B/A · (1 + μK)`. -/
noncomputable def Kfun (μ δT tT c' ea eb : ℝ) : ℝ :=
  (ea - eb) * (1 - c') * (tT / (1 - μ) - δT) / (1 - μ)

noncomputable def ratioG (μ δS δT tT c' ea eb Fab Fba : ℝ) : ℝ :=
  (eb - ea) - (1 - μ * (1 + eb) + μ * δS) * Kfun μ δT tT c' ea eb
    - Fab * (1 - μ * (1 + ea) + μ * δS)
    + Fba * (1 - μ * (1 + eb) + μ * δS) * (1 + μ * Kfun μ δT tT c' ea eb)

noncomputable def ratioD (μ δS δT tT c' ea eb Fba : ℝ) : ℝ :=
  (1 - μ * Fba) * (1 - μ * (1 + eb) + μ * δS) * (1 + μ * Kfun μ δT tT c' ea eb)

set_option maxHeartbeats 0 in
/-- `ratioG = O(η⁴)` and `ratioD = (1-μ)² + O(η)`, given the expansions of `Fab`, `Fba`. -/
theorem ratioB_expansion (bF : Bd) : ∃ bG bD : Bd, ∀ (η μ δS δT tT c' ea eb Fab Fba : ℝ),
    0 < η → 0 < μ → μ ≤ 1 / 4 → 0 < δS → δS ≤ η ^ 2 → 0 < δT → δT ≤ η ^ 2 → 0 ≤ tT → tT ≤ η ^ 2 →
    |ea| ≤ η → |eb| ≤ η → |c'| ≤ μ * δS * δT →
    Valid η 0 Fab (Pc.mk0 1 eb (-δS + δT * μ - δT + tT)
      ((δT * μ - δT + tT) * (ea * μ + 2 * eb * μ - eb) / (μ - 1))) bF →
    Valid η 0 Fba (Pc.mk0 1 ea (-δS + δT * μ - δT + tT)
      ((δT * μ - δT + tT) * (eb * μ + 2 * ea * μ - ea) / (μ - 1))) bF →
    Valid η 0 (ratioG μ δS δT tT c' ea eb Fab Fba) (Pc.mk0 0 0 0 0) bG ∧
    Valid η 0 (ratioD μ δS δT tT c' ea eb Fba)
      (Pc.mk0 ((μ - 1) ^ 2) (μ * (ea + eb) * (μ - 1))
        (-μ * (2 * δS * μ - 2 * δS - δT * μ ^ 2 + 2 * δT * μ - δT - ea * eb * μ - μ * tT + tT))
        (-μ * (δS * ea * μ + δS * eb * μ - 2 * δT * ea * μ ^ 2 + 2 * δT * ea * μ
          - 2 * δT * eb * μ ^ 2 + 3 * δT * eb * μ - δT * eb - 2 * ea * μ * tT - 2 * eb * μ * tT
          + eb * tT))) bD := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  intro η μ δS δT tT c' ea eb Fab Fba hη hμ hμ4 hδS hδSη hδT hδTη htT htTη hea heb hc' hFab hFba
  have hμ1 : μ - 1 ≠ 0 := by linarith
  have h1μ : (1 : ℝ) - μ ≠ 0 := by linarith
  have hμ0 := hμ.ne'
  have hδS0 := hδS.ne'
  have hδT0 := hδT.ne'
  have hμδδ : 0 < μ * δS * δT := by positivity
  have L1 : Valid η 0 1 (Pc.single 0 0 1) _ := Valid.const zero_le_one (by simp)
  have Lμ : Valid η 0 μ (Pc.single 0 0 μ) _ :=
    Valid.const (A := 1 / 4) (by norm_num) (by rw [abs_of_pos hμ]; exact hμ4)
  have LδS : Valid η 0 δS (Pc.single 2 0 δS) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδS]; simpa using hδSη)
  have LδT : Valid η 0 δT (Pc.single 2 0 δT) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδT]; simpa using hδTη)
  have LtT : Valid η 0 tT (Pc.single 2 0 tT) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg htT]; simpa using htTη)
  have Lea : Valid η 0 ea (Pc.single 1 0 ea) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Leb : Valid η 0 eb (Pc.single 1 0 eb) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using heb)
  have Lκ : Valid η 0 (c' / (μ * δS * δT)) (Pc.single 0 0 (c' / (μ * δS * δT))) _ :=
    Valid.const zero_le_one (by rw [abs_div, abs_of_pos hμδδ, div_le_one hμδδ]; exact hc')
  have Lc' : Valid η 0 c' (Pc.mk0 0 0 0 0) _ :=
    ((((Lμ.mul LδS).mul LδT).mul Lκ).congr_val (by field_simp)).congr (by pieces)
  have L1μ : Valid η 0 (1 - μ) (Pc.mk0 (1 - μ) 0 0 0) _ := (L1.sub Lμ).congr (by pieces)
  have Li : Valid η 0 (1 - μ)⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ :=
    (L1μ.inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have LA : Valid η 0 (1 - μ * (1 + ea) + μ * δS) (Pc.mk0 (1 - μ) (-μ * ea) (μ * δS) 0) _ :=
    ((L1.sub (Lμ.mul (L1.add Lea))).add (Lμ.mul LδS)).congr (by pieces)
  have LB : Valid η 0 (1 - μ * (1 + eb) + μ * δS) (Pc.mk0 (1 - μ) (-μ * eb) (μ * δS) 0) _ :=
    ((L1.sub (Lμ.mul (L1.add Leb))).add (Lμ.mul LδS)).congr (by pieces)
  have LK : Valid η 0 (Kfun μ δT tT c' ea eb)
      (Pc.mk0 0 0 0 ((ea - eb) * (δT * μ - δT + tT) / (μ - 1) ^ 2)) _ :=
    ((((Lea.sub Leb).mul (L1.sub Lc')).mul ((LtT.mul Li).sub LδT)).mul Li).congr_val
      (by unfold Kfun; ring) |>.congr (by pieces)
  have LC : Valid η 0 (1 + μ * Kfun μ δT tT c' ea eb)
      (Pc.mk0 1 0 0 (μ * (ea - eb) * (δT * μ - δT + tT) / (μ - 1) ^ 2)) _ :=
    (L1.add (Lμ.mul LK)).congr (by pieces)
  have hG : Valid η 0 (ratioG μ δS δT tT c' ea eb Fab Fba) (Pc.mk0 0 0 0 0) _ :=
    ((((Leb.sub Lea).sub (LB.mul LK)).sub (hFab.mul LA)).add
      ((hFba.mul LB).mul LC)).congr_val (by unfold ratioG; ring) |>.congr (by pieces)
  have hD : Valid η 0 (ratioD μ δS δT tT c' ea eb Fba)
      (Pc.mk0 ((μ - 1) ^ 2) (μ * (ea + eb) * (μ - 1))
        (-μ * (2 * δS * μ - 2 * δS - δT * μ ^ 2 + 2 * δT * μ - δT - ea * eb * μ - μ * tT + tT))
        (-μ * (δS * ea * μ + δS * eb * μ - 2 * δT * ea * μ ^ 2 + 2 * δT * ea * μ
          - 2 * δT * eb * μ ^ 2 + 3 * δT * eb * μ - δT * eb - 2 * ea * μ * tT - 2 * eb * μ * tT
          + eb * tT))) _ :=
    (((L1.sub (Lμ.mul hFba)).mul LB).mul LC).congr_val (by unfold ratioD; ring)
      |>.congr (by pieces)
  constructor
  · exact hG
  · exact hD

end LW.Bip
