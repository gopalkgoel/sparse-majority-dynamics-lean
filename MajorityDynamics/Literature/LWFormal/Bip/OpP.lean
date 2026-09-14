import MajorityDynamics.Literature.LWFormal.Bip.Bad
import MajorityDynamics.Literature.LWFormal.OpP

set_option autoImplicit true

/-!
# Lemma 4.1(b): the expansion of `𝒫(P*, R*)`

With `d' = d - e_v`, `d''_b = d - e_b - e_v`, `S = ℓ⁻¹ ∑_{b ∈ S} R*_{ba}(d') (1 - P*_{bv}(d''_b))`
and `pDenB = (1 + ε_a)(1 + AcorrB μ sS sT ε_a ε_v) S`,
`𝒫(P*,R*)_{av}(d) / P*_{av}(d) = (1 - P*_{av}(d''_a)) / pDenB`.
`opPB_expansion` shows `pG := (1 - P*_{av}(d''_a) - pDenB) / μ = O(η⁴)` and `pDenB = 1 - μ + O(η)`.
-/

namespace LW.Bip

open Finset LW.TM

/-- `R*_{ba}(d') (1 - P*_{bv}(d''_b))` in the parameters of `d'` and `d''_b`. -/
noncomputable def pTermB (μ' δS sT' νT xb xa μ'' sS'' xb'' xv'' : ℝ) : ℝ :=
  rhoB μ' δS sT' νT xb xa * (1 - piB μ'' sS'' sT' xb'' xv'')

/-- `(1 + ε_a)(1 + AcorrB μ sS sT ε_a ε_v) S`. -/
noncomputable def pDenB (μ sS sT ea ev S : ℝ) : ℝ := (1 + ea) * (1 + AcorrB μ sS sT ea ev) * S

/-- `piB (μκ) sS sT x y = μ · pQB κ (μκ) sS sT x y`. -/
noncomputable def pQB (κ μκ sS sT x y : ℝ) : ℝ :=
  κ * (1 + x) * (1 + y) * (1 + AcorrB μκ sS sT x y)

theorem piB_eq_pQB {μ κ μκ : ℝ} (h : μκ = μ * κ) (sS sT x y : ℝ) :
    piB μκ sS sT x y = μ * pQB κ μκ sS sT x y := by
  unfold piB pQB; rw [h]; ring

/-- `(R*_{ba}(d') (1+ε_a)/(1+ε_b) - 1)/μ` with `I = (1 - μ'(1+ε_b) + μ' δS)⁻¹`,
`J = (s'/(1-μ') - δT)/(1-μ')`, `μ' = μ r`, `sT' = μ s'`. -/
noncomputable def pRhoB (μ r I J z ea : ℝ) : ℝ :=
  r * (z - ea) * I + (z - ea) * J + μ * r * (z - ea) ^ 2 * I * J

/-- `(pTermB - (1+ε_b)/(1+ε_a))/μ`. -/
noncomputable def pHB (ea z ρ Q μ : ℝ) : ℝ := (1 + z) * (1 + ea)⁻¹ * (ρ - Q - μ * ρ * Q)

theorem pTermB_decomp {μ r δS s' δT z ea κ μ'' sS'' xb'' xv'' : ℝ}
    (hI : 1 - μ * r * (1 + z) + μ * r * δS ≠ 0) (hi : 1 - μ * r ≠ 0) (hea : 1 + ea ≠ 0)
    (hμ'' : μ'' = μ * κ) :
    pTermB (μ * r) δS (μ * s') (μ * δT) z ea μ'' sS'' xb'' xv'' =
      (1 + z) / (1 + ea) + μ * pHB ea z
        (pRhoB μ r (1 - μ * r * (1 + z) + μ * r * δS)⁻¹
          ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) z ea)
        (pQB κ μ'' sS'' (μ * s') xb'' xv'') μ := by
  have hR : (1 - μ * r * (1 + ea) + μ * r * δS) / (1 - μ * r * (1 + z) + μ * r * δS) =
      1 + μ * r * (z - ea) * (1 - μ * r * (1 + z) + μ * r * δS)⁻¹ := by
    rw [div_eq_iff hI]
    linear_combination (-(μ * r * (z - ea))) * inv_mul_cancel₀ hI
  unfold pTermB rhoB
  rw [hR, piB_eq_pQB hμ'']
  unfold pHB pRhoB
  field_simp
  ring

set_option maxHeartbeats 0 in
/-- `pG = O(η⁴)` and `pDenB = 1 - μ + O(η)` for balanced `d` (`1/n = μ δS`, `1/ℓ = μ δT`);
`V = S`, `a ∈ V`, `ε = ε_S`, and `xb'', sS'' : V → ℝ` are the parameters of `d''_b`. -/
theorem opPB_expansion : ∃ bG bD : Bd, ∀ {ι : Type}
    (η μ δS δT tS tT s₃ ea ev νS νT μ' μ'' sT' xv'' sS0 sT0 : ℝ) (ℓ : ℕ) (V : Finset ι) (a : ι)
    (ε xb'' sS'' : ι → ℝ),
    0 < η → η ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 4 → 0 < δS → δS ≤ η ^ 2 → 0 < δT → δT ≤ η ^ 2 →
    0 ≤ tS → tS ≤ η ^ 2 → 0 ≤ tT → tT ≤ η ^ 2 → |s₃| ≤ η ^ 3 → |ea| ≤ η → |ev| ≤ η →
    (∀ b ∈ V, |ε b| ≤ η) → 0 < ℓ → V.card = ℓ → a ∈ V → ε a = ea →
    νS = μ * δS → νT = μ * δT →
    ∑ b ∈ V, ε b = 0 → ∑ b ∈ V, ε b ^ 2 = ℓ * tS → ∑ b ∈ V, ε b ^ 3 = ℓ * s₃ →
    μ' = μ * (1 - δT * νS / 2) → μ'' = μ * (1 - δT * νS) →
    sT' = (tT * μ + (1 - νS) * νS * νT * δT - 2 * ev * νS * νT) / (1 - δT * νS) →
    xv'' = (ev - δT + δT * νS) / (1 - δT * νS) →
    (∀ b ∈ V, xb'' b = (ε b - δS + δS * νT) / (1 - δS * νT)) →
    (∀ b ∈ V, sS'' b =
      (tS * μ + (1 - νT) * νT * νS * δS - 2 * ε b * νT * νS) / (1 - δS * νT)) →
    sS0 = tS * μ → sT0 = tT * μ →
    Valid η 0 ((1 - piB μ'' (sS'' a) sT' (xb'' a) xv'' -
        pDenB μ sS0 sT0 ea ev
          ((∑ b ∈ V, pTermB μ' δS sT' νT (ε b) ea μ'' (sS'' b) (xb'' b) xv'') / ℓ)) / μ)
      (Pc.mk0 0 0 0 0) bG ∧
    Valid η 0 (pDenB μ sS0 sT0 ea ev
        ((∑ b ∈ V, pTermB μ' δS sT' νT (ε b) ea μ'' (sS'' b) (xb'' b) xv'') / ℓ))
      (Pc.mk0 (1 - μ) (-μ * (ea + ev))
        (μ * (δS * μ - δS + δT * μ - δT - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (μ * (2 * δS * ev * μ - δS * ev + 2 * δT * ea * μ - δT * ea - ea ^ 2 * ev * μ
          - ea * ev ^ 2 * μ + ea * μ * tT + ev * μ * tS) / (μ - 1))) bD := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  intro ι η μ δS δT tS tT s₃ ea ev νS νT μ' μ'' sT' xv'' sS0 sT0 ℓ V a ε xb'' sS'' hη hη2 hμ hμ4
    hδS hδSη hδT hδTη htS htSη htT htTη hs₃ hea hev hεV hℓ hcard haV hεa hνS hνT hm1 hm2 hm3 hμ'
    hμ'' hsT' hxv'' hxb'' hsS'' hsS0 hsT0
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
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
  have hea1 : 1 + ea ≠ 0 := by have := (abs_le.1 hea).1; linarith
  have hcardR : (V.card : ℝ) = ℓ := by rw [hcard]
  have hne : V.Nonempty := ⟨a, haV⟩
  -- factor `μ` out of `μ'`, `sT'`
  obtain ⟨r, hr⟩ : ∃ x, x = 1 - δT * νS / 2 := ⟨_, rfl⟩
  have hμ'r : μ' = μ * r := by rw [hμ', hr]
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  obtain ⟨s', hs'⟩ : ∃ x, x =
    (tT + (1 - νS) * δS * νT * δT - 2 * ev * δS * νT) / (1 - δT * νS) := ⟨_, rfl⟩
  have hsT's : sT' = μ * s' := by rw [hsT', hs', hνS]; ring
  subst hsS0 hsT0
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
    Valid.leaf 3 (by norm_num) zero_le_one (by simpa using hs₃)
  have Lea : ∀ z, Valid η z ea (Pc.single 1 0 ea) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Lev : ∀ z, Valid η z ev (Pc.single 1 0 ev) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hev)
  have L2 : ∀ z, Valid η z 2 (Pc.single 0 0 2) _ := fun z =>
    Valid.const (A := 2) (by norm_num) (by simp)
  have Lhalf : ∀ z, Valid η z (1 / 2) (Pc.single 0 0 (1 / 2)) _ := fun z =>
    Valid.const (A := 1 / 2) (by norm_num) (by rw [abs_of_pos (by norm_num)])
  -- derived `z`-free quantities
  have LνS : ∀ z, Valid η z νS (Pc.mk0 0 0 (μ * δS) 0) _ := fun z =>
    (((Lμ z).mul (LδS z)).congr_val hνS.symm).congr (by pieces)
  have LνT : ∀ z, Valid η z νT (Pc.mk0 0 0 (μ * δT) 0) _ := fun z =>
    (((Lμ z).mul (LδT z)).congr_val hνT.symm).congr (by pieces)
  have Lc : ∀ z, Valid η z (δT * νS) (Pc.mk0 0 0 0 0) _ := fun z =>
    ((LδT z).mul (LνS z)).congr (by pieces)
  have LcS : ∀ z, Valid η z (δS * νT) (Pc.mk0 0 0 0 0) _ := fun z =>
    ((LδS z).mul (LνT z)).congr (by pieces)
  have Lomc : ∀ z, Valid η z (1 - δT * νS) (Pc.mk0 1 0 0 0) _ := fun z =>
    ((L1 z).sub (Lc z)).congr (by pieces)
  have Lomci : ∀ z, Valid η z (1 - δT * νS)⁻¹ (Pc.mk0 1 0 0 0) _ := fun z =>
    ((Lomc z).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have LomcS : ∀ z, Valid η z (1 - δS * νT) (Pc.mk0 1 0 0 0) _ := fun z =>
    ((L1 z).sub (LcS z)).congr (by pieces)
  have LomcSi : ∀ z, Valid η z (1 - δS * νT)⁻¹ (Pc.mk0 1 0 0 0) _ := fun z =>
    ((LomcS z).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lr : ∀ z, Valid η z r (Pc.mk0 1 0 0 0) _ := fun z =>
    (((L1 z).sub ((Lc z).mul (Lhalf z))).congr_val (by rw [hr]; ring)).congr (by pieces)
  have Lμ' : ∀ z, Valid η z (μ * r) (Pc.mk0 μ 0 0 0) _ := fun z =>
    ((Lμ z).mul (Lr z)).congr (by pieces)
  have Lμ'' : ∀ z, Valid η z μ'' (Pc.mk0 μ 0 0 0) _ := fun z =>
    (((Lμ z).mul (Lomc z)).congr_val hμ''.symm).congr (by pieces)
  have L1μ : ∀ z, Valid η z (1 - μ) (Pc.mk0 (1 - μ) 0 0 0) _ := fun z =>
    ((L1 z).sub (Lμ z)).congr (by pieces)
  have Li0 : ∀ z, Valid η z (1 - μ)⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    ((L1μ z).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have L1μ' : ∀ z, Valid η z (1 - μ * r) (Pc.mk0 (1 - μ) 0 0 0) _ := fun z =>
    ((L1 z).sub (Lμ' z)).congr (by pieces)
  have Li1 : ∀ z, Valid η z (1 - μ * r)⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    ((L1μ' z).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have L1μ'' : ∀ z, Valid η z (1 - μ'') (Pc.mk0 (1 - μ) 0 0 0) _ := fun z =>
    ((L1 z).sub (Lμ'' z)).congr (by pieces)
  have Li2 : ∀ z, Valid η z (1 - μ'')⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    ((L1μ'' z).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have Ls' : ∀ z, Valid η z s' (Pc.mk0 0 0 tT 0) _ := fun z =>
    (((((LtT z).add (((((L1 z).sub (LνS z)).mul (LδS z)).mul (LνT z)).mul (LδT z))).sub
      ((((L2 z).mul (Lev z)).mul (LδS z)).mul (LνT z))).mul (Lomci z)).congr_val
      (by rw [hs']; ring)).congr (by pieces)
  have LsT' : ∀ z, Valid η z sT' (Pc.mk0 0 0 (μ * tT) 0) _ := fun z =>
    (((Lμ z).mul (Ls' z)).congr_val hsT's.symm).congr (by pieces)
  have Lxv'' : ∀ z, Valid η z xv'' (Pc.mk0 0 ev (-δT) 0) _ := fun z =>
    (((((Lev z).sub (LδT z)).add (Lc z)).mul (Lomci z)).congr_val (by rw [hxv'']; ring)).congr
      (by pieces)
  have Li1pea : ∀ z, Valid η z (1 + ea)⁻¹ (Pc.mk0 1 (-ea) (ea ^ 2) (-ea ^ 3)) _ := fun z =>
    (((L1 z).add (Lea z)).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ) + 0|; norm_num)).congr
      (by pieces)
  have LA0 : Valid η 0 ((-ea * ev + ea * tT + ev * tS) * (1 - μ)⁻¹)
      (Pc.mk0 0 0 (ea * ev / (μ - 1)) (-(ea * tT + ev * tS) / (μ - 1))) _ :=
    (((((Lea 0).neg.mul (Lev 0)).add ((Lea 0).mul (LtT 0))).add ((Lev 0).mul (LtS 0))).mul
      (Li0 0)).congr (by pieces)
  -- the parameters of `d''_a`
  have hxa'' := hxb'' a haV
  have hsSa := hsS'' a haV
  rw [hεa] at hxa'' hsSa
  have Lxa'' : Valid η 0 (xb'' a) (Pc.mk0 0 ea (-δS) 0) _ :=
    (((((Lea 0).sub (LδS 0)).add (LcS 0)).mul (LomcSi 0)).congr_val
      (by rw [hxa'']; ring)).congr (by pieces)
  have LsSa : Valid η 0 (sS'' a) (Pc.mk0 0 0 (μ * tS) 0) _ :=
    (((((LtS 0).mul (Lμ 0)).add (((((L1 0).sub (LνT 0)).mul (LνT 0)).mul (LνS 0)).mul
      (LδS 0))).sub ((((L2 0).mul (Lea 0)).mul (LνT 0)).mul (LνS 0))).mul (LomcSi 0)).congr_val
      (by rw [hsSa]; ring) |>.congr (by pieces)
  have LAa : Valid η 0 (AcorrB μ'' (sS'' a) sT' (xb'' a) xv'')
      (Pc.mk0 0 0 (ea * ev * μ / (μ - 1))
        (-μ * (δS * ev + δT * ea + ea * tT + ev * tS) / (μ - 1))) _ :=
    ((Lμ'' 0).acorrB LsSa (LsT' 0) (Li2 0) rfl Lxa'' (Lxv'' 0)).congr (by unfold Pc.acorrB; pieces)
  have LQa : Valid η 0 (pQB (1 - δT * νS) μ'' (sS'' a) sT' (xb'' a) xv'')
      (Pc.mk0 1 (ea + ev) (-(δS * μ - δS + δT * μ - δT - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (-(2 * δS * ev * μ - δS * ev + 2 * δT * ea * μ - δT * ea - ea ^ 2 * ev * μ
          - ea * ev ^ 2 * μ + ea * μ * tT + ev * μ * tS) / (μ - 1))) _ :=
    (((((Lomc 0).mul ((L1 0).add Lxa'')).mul ((L1 0).add (Lxv'' 0))).mul
      ((L1 0).add LAa)).congr_val (by unfold pQB; ring)).congr (by pieces)
  -- the `b`-dependent factor, expanded in `z = ε b`
  have hH : ∀ b ∈ V, Valid η (ε b)
      (pHB ea (ε b)
        (pRhoB μ r (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
          ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) (ε b) ea)
        (pQB (1 - δT * νS) μ'' (sS'' b) sT' (xb'' b) xv'') μ)
      (Pc.mk (-1) (-ev) (-1) ((δS * μ - δS + δT * μ - δT - ea * ev) / (μ - 1)) (-2 * ev) 0
        (-(δS * ea * μ - δS * ea - 2 * δS * ev * μ + δS * ev - δT * ea * μ - ea ^ 2 * ev
          - ea * tT - ev * μ * tS) / (μ - 1))
        ((δS * μ - δS + δT * μ - δT - 2 * ea * ev - ev ^ 2 * μ + μ * tT - tT) / (μ - 1))
        (-ev) 0) _ := fun b hb =>
    have hz : Valid η (ε b) (ε b) (Pc.single 1 1 1) _ := Valid.var
    have Lxb : Valid η (ε b) (xb'' b) (Pc.mk 0 0 1 (-δS) 0 0 0 0 0 0) _ :=
      ((((hz.sub (LδS _)).add (LcS _)).mul (LomcSi _)).congr_val
        (by rw [hxb'' b hb]; ring)).congr (by pieces)
    have LsSb : Valid η (ε b) (sS'' b) (Pc.mk0 0 0 (μ * tS) 0) _ :=
      (((((LtS _).mul (Lμ _)).add (((((L1 _).sub (LνT _)).mul (LνT _)).mul (LνS _)).mul
        (LδS _))).sub ((((L2 _).mul hz).mul (LνT _)).mul (LνS _))).mul (LomcSi _)).congr_val
        (by rw [hsS'' b hb]; ring) |>.congr (by pieces)
    have LAb : Valid η (ε b) (AcorrB μ'' (sS'' b) sT' (xb'' b) xv'')
        (Pc.mk 0 0 0 0 (ev * μ / (μ - 1)) 0 (-ev * μ * (δS + tS) / (μ - 1))
          (-μ * (δT + tT) / (μ - 1)) 0 0) _ :=
      ((Lμ'' _).acorrB LsSb (LsT' _) (Li2 _) rfl Lxb (Lxv'' _)).congr (by unfold Pc.acorrB; pieces)
    have LQb : Valid η (ε b) (pQB (1 - δT * νS) μ'' (sS'' b) sT' (xb'' b) xv'')
        (Pc.mk 1 ev 1 (-δS - δT) (ev * (2 * μ - 1) / (μ - 1)) 0
          (-ev * (2 * δS * μ - δS + μ * tS) / (μ - 1))
          (-(2 * δT * μ - δT - ev ^ 2 * μ + μ * tT) / (μ - 1)) (ev * μ / (μ - 1)) 0) _ :=
      (((((Lomc _).mul ((L1 _).add Lxb)).mul ((L1 _).add (Lxv'' _))).mul
        ((L1 _).add LAb)).congr_val (by unfold pQB; ring)).congr (by pieces)
    have LIbd : Valid η (ε b) (1 - μ * r * (1 + ε b) + μ * r * δS)
        (Pc.mk (1 - μ) 0 (-μ) (δS * μ) 0 0 0 0 0 0) _ :=
      (((L1 _).sub ((Lμ' _).mul ((L1 _).add hz))).add ((Lμ' _).mul (LδS _))).congr (by pieces)
    have LIb : Valid η (ε b) (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
        (Pc.mk (-1 / (μ - 1)) 0 (μ / (μ - 1) ^ 2) (-δS * μ / (μ - 1) ^ 2) 0 (-μ ^ 2 / (μ - 1) ^ 3)
          0 (2 * δS * μ ^ 2 / (μ - 1) ^ 3) 0 (μ ^ 3 / (μ - 1) ^ 4)) _ :=
      (LIbd.inv (L := 3 / 4) (by norm_num)
        (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
        (by pieces)
    have LJ : Valid η (ε b) ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹)
        (Pc.mk0 0 0 ((δT * μ - δT + tT) / (μ - 1) ^ 2) 0) _ :=
      ((((Ls' _).mul (Li1 _)).sub (LδT _)).mul (Li1 _)).congr (by pieces)
    have Ldx : Valid η (ε b) (ε b - ea) (Pc.mk 0 (-ea) 1 0 0 0 0 0 0 0) _ :=
      (hz.sub (Lea _)).congr (by pieces)
    have Lρ : Valid η (ε b)
        (pRhoB μ r (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
          ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) (ε b) ea)
        (Pc.mk 0 (ea / (μ - 1)) (-1 / (μ - 1)) 0 (-ea * μ / (μ - 1) ^ 2) (μ / (μ - 1) ^ 2)
          (ea * (δS * μ - δT * μ + δT - tT) / (μ - 1) ^ 2)
          (-(δS * μ - δT * μ + δT - tT) / (μ - 1) ^ 2)
          (ea * μ ^ 2 / (μ - 1) ^ 3) (-μ ^ 2 / (μ - 1) ^ 3)) _ :=
      (((((Lr _).mul Ldx).mul LIb).add (Ldx.mul LJ)).add
        (((((Lμ _).mul (Lr _)).mul (Ldx.mul Ldx)).mul LIb).mul LJ)).congr_val
        (by unfold pRhoB; ring) |>.congr (by pieces)
    have Lpref : Valid η (ε b) ((1 + ε b) * (1 + ea)⁻¹)
        (Pc.mk 1 (-ea) 1 (ea ^ 2) (-ea) 0 (-ea ^ 3) (ea ^ 2) 0 0) _ :=
      (((L1 _).add hz).mul (Li1pea _)).congr (by pieces)
    (Lpref.mul ((Lρ.sub LQb).sub (((Lμ _).mul Lρ).mul LQb))).congr_val (by unfold pHB; ring)
      |>.congr (by pieces)
  -- moments of `ε` over `V`
  have LP1 : Valid η 0 (0 : ℝ) (Pc.single 0 0 0) _ := Valid.const le_rfl (by simp)
  have Lavg : Valid η 0
      ((∑ b ∈ V, pHB ea (ε b)
        (pRhoB μ r (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
          ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) (ε b) ea)
        (pQB (1 - δT * νS) μ'' (sS'' b) sT' (xb'' b) xv'') μ) / ℓ)
      (Pc.mk0 (-1) (-ev) ((δS * μ - δS + δT * μ - δT - ea * ev) / (μ - 1))
        (-(δS * ea * μ - δS * ea - 2 * δS * ev * μ + δS * ev - δT * ea * μ - ea ^ 2 * ev
          - ea * tT - ev * tS) / (μ - 1))) _ :=
    (Valid.avg4 hne hεV hH hℓ0 hcardR.le
      (by simp [hcardR]; field_simp)
      (by simp only [pow_one, hm1, zero_div])
      (by rw [hm2]; field_simp)
      (by rw [hm3]; field_simp) (L1 0) LP1 (LtS 0) (Ls3 0)).congr (by pieces)
  have LE : Valid η 0 (-pQB (1 - δT * νS) μ'' (sS'' a) sT' (xb'' a) xv'' -
      (-ea * ev + ea * tT + ev * tS) * (1 - μ)⁻¹ -
      (1 + μ * ((-ea * ev + ea * tT + ev * tS) * (1 - μ)⁻¹)) * (1 + ea) *
        ((∑ b ∈ V, pHB ea (ε b)
          (pRhoB μ r (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
            ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) (ε b) ea)
          (pQB (1 - δT * νS) μ'' (sS'' b) sT' (xb'' b) xv'') μ) / ℓ))
      (Pc.mk0 0 0 0 0) _ :=
    ((LQa.neg.sub LA0).sub ((((L1 0).add ((Lμ 0).mul LA0)).mul ((L1 0).add (Lea 0))).mul
      Lavg)).congr (by pieces)
  have LD : Valid η 0 ((1 + μ * ((-ea * ev + ea * tT + ev * tS) * (1 - μ)⁻¹)) *
      (1 + μ * (1 + ea) *
        ((∑ b ∈ V, pHB ea (ε b)
          (pRhoB μ r (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
            ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) (ε b) ea)
          (pQB (1 - δT * νS) μ'' (sS'' b) sT' (xb'' b) xv'') μ) / ℓ)))
      (Pc.mk0 (1 - μ) (-μ * (ea + ev))
        (μ * (δS * μ - δS + δT * μ - δT - 2 * ea * ev * μ + ea * ev) / (μ - 1))
        (μ * (2 * δS * ev * μ - δS * ev + 2 * δT * ea * μ - δT * ea - ea ^ 2 * ev * μ
          - ea * ev ^ 2 * μ + ea * μ * tT + ev * μ * tS) / (μ - 1))) _ :=
    (((L1 0).add ((Lμ 0).mul LA0)).mul ((L1 0).add ((((Lμ 0).mul ((L1 0).add (Lea 0))).mul
      Lavg)))).congr (by pieces)
  -- the exact decomposition of the sum
  have hμr0 : 1 - μ * r ≠ 0 := (by nlinarith : (0 : ℝ) < 1 - μ * r).ne'
  have hsum : ∑ b ∈ V, pTermB μ' δS sT' νT (ε b) ea μ'' (sS'' b) (xb'' b) xv'' =
      (ℓ : ℝ) / (1 + ea) + μ * ∑ b ∈ V, pHB ea (ε b)
        (pRhoB μ r (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
          ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) (ε b) ea)
        (pQB (1 - δT * νS) μ'' (sS'' b) sT' (xb'' b) xv'') μ := by
    rw [show (ℓ : ℝ) / (1 + ea) = ∑ b ∈ V, (1 + ε b) / (1 + ea) by
      rw [← sum_div, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, hcardR, hm1]; ring]
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun b hb => ?_
    have hI : 1 - μ * r * (1 + ε b) + μ * r * δS ≠ 0 :=
      (pI_pos (mul_nonneg hμ.le hr0) (by nlinarith) ((hεV b hb).trans (by linarith))
        (by positivity)).ne'
    rw [hμ'r, hsT's, hνT]
    exact pTermB_decomp hI hμr0 hea1 hμ''
  have hQa : piB μ'' (sS'' a) sT' (xb'' a) xv'' =
      μ * pQB (1 - δT * νS) μ'' (sS'' a) sT' (xb'' a) xv'' := piB_eq_pQB hμ'' _ _ _ _
  have hA0 : AcorrB μ (tS * μ) (tT * μ) ea ev = μ * ((-ea * ev + ea * tT + ev * tS) * (1 - μ)⁻¹) := by
    unfold AcorrB; ring
  set SH := ∑ b ∈ V, pHB ea (ε b)
    (pRhoB μ r (1 - μ * r * (1 + ε b) + μ * r * δS)⁻¹
      ((s' * (1 - μ * r)⁻¹ - δT) * (1 - μ * r)⁻¹) (ε b) ea)
    (pQB (1 - δT * νS) μ'' (sS'' b) sT' (xb'' b) xv'') μ with hSH
  constructor
  · refine LE.congr_val ?_
    rw [hQa, pDenB, hsum, hA0, eq_div_iff hμ.ne']
    field_simp
    ring
  · refine LD.congr_val ?_
    rw [pDenB, hsum, hA0]
    field_simp

end LW.Bip
