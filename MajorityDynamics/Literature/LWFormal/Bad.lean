import MajorityDynamics.Literature.LWFormal.Expansion
import MajorityDynamics.Literature.LWFormal.Approx

set_option autoImplicit true

/-!
# Lemma 7.1: the expansion of `bad(P^gr, Y^gr)`

`bad_expansion` computes `bad(P^gr,Y^gr)_{ab}(d - e_b) / μ` to third order in `η` (where
`|ε_i| ≤ η`, `1/d̄ ≤ η²`, `σ²/d̄² ≤ η²`) with an explicit `O(η⁴)` remainder, abstracting the
shifted sequence `d - e_b` through the identities it satisfies.
-/

namespace LW

open Finset LW.TM

/-- `π = μ(1+x)(1+y)(1 + Acorr μ s m x y)` with `s = σ²/(d n)`, `m = 1/(n-1)`. -/
noncomputable def Acorr (μ s m x y : ℝ) : ℝ := (-μ * x * y + (x + y) * s) / (1 - μ) + (x + y) * m

theorem piF_eq (x y μ σ2 d : ℝ) (n : ℕ) :
    piF x y μ σ2 d n =
      μ * (1 + x) * (1 + y) * (1 + Acorr μ (σ2 / (d * n)) (1 / ((n : ℝ) - 1)) x y) := by
  unfold piF Acorr; ring

/-- The correction factor of `Y^gr`: `Y^gr = π π' (1 + Tcorr)`. -/
noncomputable def Tcorr (μ m xa xb : ℝ) : ℝ := m * (1 + xa - μ * (1 + xa + xb)) / (1 - μ)

/-- The `v`-dependent part of `Y^gr_{avb} / (μ²(1+ε_a)(1+ε_b)(1+Tcorr))`, `y = ε_v`. -/
noncomputable def Gfun (μ s m δ' xa xb y : ℝ) : ℝ :=
  (1 + y) * (1 + y - δ') * (1 + Acorr μ s m xa y) * (1 + Acorr μ s m xb (y - δ'))

/-- `bad(P^gr, Y^gr)_{ab}` written in terms of the parameters of the sequence. -/
noncomputable def badF {ι : Type*} (xa xb : ℝ) (V : Finset ι) (ε' : ι → ℝ) (μ σ2 d : ℝ) (n : ℕ)
    (da : ℝ) : ℝ :=
  (piF xa xb μ σ2 d n + ∑ v ∈ V, piF xa (ε' v) μ σ2 d n * piF xb (ε' v - 1 / d) μ σ2 d n *
    (1 + (1 + xa - μ * (1 + xa + xb)) / (((n : ℝ) - 1) * (1 - μ)))) / da

theorem bad_eq {n : ℕ} {a b : Fin n} (d : Seq n) (hab : a ≠ b) :
    bad Pgr Ygr a b d =
      badF (eps d a) (eps d b) ((univ.erase a).erase b) (eps d) (mu d) (sigma2 d) (dbar d) n
        (d a) := by
  simp only [bad, badF, Pgr, Ygr, if_neg hab]

/-- `bad / μ` split as `term1 + pref * (∑_v G_v)/n`. -/
theorem badF_decomp {ι : Type*} (V : Finset ι) (ε' : ι → ℝ) (xa xb μ σ2' d' δ ea : ℝ) (n : ℕ)
    (hμ : μ ≠ 0) (hea : 1 + ea ≠ 0) (hn : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (hmud : 1 / ((n : ℝ) - 1) = μ * δ) :
    badF xa xb V ε' (μ * (1 - δ / n)) σ2' d' n (1 / δ * (1 + ea)) / μ =
      (1 - δ / n) * (1 + xa) * (1 + xb) *
          (1 + Acorr (μ * (1 - δ / n)) (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) xa xb) * δ *
          (1 + ea)⁻¹
        + (1 - δ / n) ^ 2 * (1 + 1 / ((n : ℝ) - 1)) * (1 + xa) * (1 + xb) *
          (1 + Tcorr (μ * (1 - δ / n)) (1 / ((n : ℝ) - 1)) xa xb) * (1 + ea)⁻¹ *
          ((∑ v ∈ V, Gfun (μ * (1 - δ / n)) (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) (1 / d') xa xb
            (ε' v)) / n) := by
  have h : μ * δ * ((n : ℝ) - 1) = 1 := by rw [← hmud]; field_simp
  have hδ : δ = 1 / (μ * ((n : ℝ) - 1)) := by field_simp; linear_combination h
  subst hδ
  unfold badF Gfun Tcorr
  simp only [piF_eq]
  rw [div_div, add_div, sum_div]
  congr 1
  · field_simp
  · conv_rhs => rw [← mul_div_assoc, mul_sum, sum_div]
    refine sum_congr rfl fun v _ => ?_
    field_simp; ring

namespace TM

/-- Pieces of `Acorr` from pieces of its arguments (`i = (1-μ)⁻¹`). -/
def Pc.acorr (cμ cs cm ci cx cy : Pc) : Pc :=
  Pc.add (Pc.mul (Pc.add (Pc.mul (Pc.mul (Pc.neg cμ) cx) cy) (Pc.mul (Pc.add cx cy) cs)) ci)
    (Pc.mul (Pc.add cx cy) cm)

def Bd.acorr (bμ bs bm bi bx by_ : Bd) : Bd :=
  Bd.add (Bd.mul (Bd.add (Bd.mul (Bd.mul bμ bx) by_) (Bd.mul (Bd.add bx by_) bs)) bi)
    (Bd.mul (Bd.add bx by_) bm)

theorem Valid.acorr {η z μ s m i x y : ℝ} {cμ cs cm ci cx cy : Pc} {bμ bs bm bi bx by_ : Bd}
    (hμ : Valid η z μ cμ bμ) (hs : Valid η z s cs bs) (hm : Valid η z m cm bm)
    (hi : Valid η z i ci bi) (hix : i = (1 - μ)⁻¹) (hx : Valid η z x cx bx)
    (hy : Valid η z y cy by_) :
    Valid η z (Acorr μ s m x y) (Pc.acorr cμ cs cm ci cx cy) (Bd.acorr bμ bs bm bi bx by_) :=
  (((((hμ.neg.mul hx).mul hy).add ((hx.add hy).mul hs)).mul hi).add
    ((hx.add hy).mul hm)).congr_val (by subst hix; unfold Acorr; ring)

end TM

set_option maxHeartbeats 0 in
/-- Third-order expansion of `bad(P^gr,Y^gr)_{ab}(d - e_b) / μ`, in the normalised variables
`δ = 1/d̄`, `t = σ²/d̄²`, `s₃ = n⁻¹ ∑ ε_i³`, `ea = ε_a`, `eb = ε_b`; the primed quantities are those
of `d - e_b`, `V = [n] \ {a, b}`. -/
theorem bad_expansion : ∃ b : Bd, ∀ {ι : Type} (η μ δ t s₃ ea eb : ℝ) (n : ℕ) (V : Finset ι)
    (ε : ι → ℝ) (μ' σ2' d' xa xb : ℝ) (ε' : ι → ℝ),
    0 < η → η ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 4 → 0 < δ → δ ≤ η ^ 2 → 0 ≤ t → t ≤ η ^ 2 →
    |s₃| ≤ η ^ 3 → |ea| ≤ η → |eb| ≤ η → (∀ v ∈ V, |ε v| ≤ η) → 3 ≤ n → V.card = n - 2 →
    1 / ((n : ℝ) - 1) = μ * δ →
    ∑ v ∈ V, ε v = -(ea + eb) → ∑ v ∈ V, ε v ^ 2 = n * t - ea ^ 2 - eb ^ 2 →
    ∑ v ∈ V, ε v ^ 3 = n * s₃ - ea ^ 3 - eb ^ 3 →
    μ' = μ * (1 - δ / n) → 1 / d' = δ / (1 - δ / n) →
    xa = (ea + δ / n) / (1 - δ / n) → xb = (eb - δ + δ / n) / (1 - δ / n) →
    (∀ v ∈ V, ε' v = (ε v + δ / n) / (1 - δ / n)) →
    σ2' / (d' * n) =
      (t + δ / n * δ * (1 - 1 / n) - 2 * (δ / n) * eb) * μ / ((1 + μ * δ) * (1 - δ / n)) →
    Valid η 0 (badF xa xb V ε' μ' σ2' d' n (1 / δ * (1 + ea)) / μ)
      (Pc.mk0 1 eb (-δ + t) (t * (ea * μ + 2 * eb * μ - eb) / (μ - 1))) b := by
  refine ⟨?_, ?_⟩
  swap
  intro ι η μ δ t s₃ ea eb n V ε μ' σ2' d' xa xb ε' hη hη2 hμ hμ4 hδ hδη ht htη hs3 hea heb hεV
    hn3 hcard hmud hm1 hm2 hm3 hμ' hd' hxa hxb hε' hs'
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
  have hea1 : 1 + ea ≠ 0 := by have := (abs_le.1 hea).1; linarith
  have hcardR : (V.card : ℝ) = n - 2 := by
    rw [hcard, Nat.cast_sub (by omega)]; norm_num
  have hVn : (V.card : ℝ) ≤ n := by linarith
  have hne : V.Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  -- leaves (valid for every `z`)
  have L1 : ∀ z, Valid η z 1 (Pc.single 0 0 1) _ := fun z => Valid.const zero_le_one (by simp)
  have Lμ : ∀ z, Valid η z μ (Pc.single 0 0 μ) _ := fun z =>
    Valid.const (A := 1 / 4) (by norm_num) (by rw [abs_of_pos hμ]; exact hμ4)
  have Lδ : ∀ z, Valid η z δ (Pc.single 2 0 δ) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδ]; simpa using hδη)
  have Lt : ∀ z, Valid η z t (Pc.single 2 0 t) _ := fun z =>
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg ht]; simpa using htη)
  have Ls3 : ∀ z, Valid η z s₃ (Pc.single 3 0 s₃) _ := fun z =>
    Valid.leaf 3 (by norm_num) zero_le_one (by simpa using hs3)
  have Lea : ∀ z, Valid η z ea (Pc.single 1 0 ea) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Leb : ∀ z, Valid η z eb (Pc.single 1 0 eb) _ := fun z =>
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using heb)
  -- derived `z`-free quantities
  have Lm : ∀ z, Valid η z (1 / ((n : ℝ) - 1)) (Pc.mk0 0 0 (μ * δ) 0) _ := fun z =>
    (((Lμ z).mul (Lδ z)).congr_val hmud.symm).congr (by pieces)
  have Lim : ∀ z, Valid η z (1 + μ * δ)⁻¹ (Pc.mk0 1 0 (-(μ * δ)) 0) _ := fun z =>
    (((L1 z).add ((Lm z).congr_val hmud)).inv (L := 1) one_pos
      (by show (1 : ℝ) ≤ |(1 : ℝ) + 0|; norm_num)).congr (by pieces)
  have Lν : ∀ z, Valid η z (1 / (n : ℝ)) (Pc.mk0 0 0 (μ * δ) 0) _ := fun z =>
    ((((Lm z).congr_val hmud).mul (Lim z)).congr_val hν.symm).congr (by pieces)
  have Lc : ∀ z, Valid η z (δ / n) (Pc.mk0 0 0 0 0) _ := fun z =>
    (((Lν z).mul (Lδ z)).congr_val (by ring)).congr (by pieces)
  have Lomc : ∀ z, Valid η z (1 - δ / n) (Pc.mk0 1 0 0 0) _ := fun z =>
    ((L1 z).sub (Lc z)).congr (by pieces)
  have Lomci : ∀ z, Valid η z (1 - δ / n)⁻¹ (Pc.mk0 1 0 0 0) _ := fun z =>
    ((Lomc z).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lμ' : ∀ z, Valid η z μ' (Pc.mk0 μ 0 0 0) _ := fun z =>
    (((Lμ z).mul (Lomc z)).congr_val hμ'.symm).congr (by pieces)
  have Lδ' : ∀ z, Valid η z (1 / d') (Pc.mk0 0 0 δ 0) _ := fun z =>
    (((Lδ z).mul (Lomci z)).congr_val (by rw [hd']; ring)).congr (by pieces)
  have Lxa : ∀ z, Valid η z xa (Pc.mk0 0 ea 0 0) _ := fun z =>
    ((((Lea z).add (Lc z)).mul (Lomci z)).congr_val (by rw [hxa]; ring)).congr
      (by pieces)
  have Lxb : ∀ z, Valid η z xb (Pc.mk0 0 eb (-δ) 0) _ := fun z =>
    (((((Leb z).sub (Lδ z)).add (Lc z)).mul (Lomci z)).congr_val
      (by rw [hxb]; ring)).congr (by pieces)
  have Ls' : ∀ z, Valid η z (σ2' / (d' * n)) (Pc.mk0 0 0 (μ * t) 0) _ := fun z =>
    (((((((Lt z).add (((Lc z).mul (Lδ z)).mul ((L1 z).sub (Lν z)))).sub
      ((((Valid.const (η := η) (z := z) (a := 2) (A := 2) (by norm_num) (by simp)).mul
        (Lc z)).mul (Leb z)))).mul (Lμ z)).mul
      (Lim z)).mul (Lomci z)).congr_val
      (by rw [hs', div_mul_eq_div_div]; ring)).congr (by pieces)
  have Li1mmup : ∀ z, Valid η z (1 - μ')⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ := fun z =>
    (((L1 z).sub (Lμ' z)).inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) + -μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have Li1pea : ∀ z, Valid η z (1 + ea)⁻¹ (Pc.mk0 1 (-ea) (ea ^ 2) (-ea ^ 3)) _ := fun z =>
    (((L1 z).add (Lea z)).inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ) + 0|; norm_num)).congr
      (by pieces)
  have LAab : ∀ z, Valid η z (Acorr μ' (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) xa xb)
      (Pc.mk0 0 0 (ea * eb * μ / (μ - 1))
        (-μ * (-δ * ea * μ + 2 * δ * ea - δ * eb * μ + δ * eb + ea * t + eb * t) / (μ - 1))) _ :=
    fun z => ((Lμ' z).acorr (Ls' z) (Lm z) (Li1mmup z) rfl (Lxa z) (Lxb z)).congr
      (by unfold Pc.acorr; pieces)
  have LTp : ∀ z, Valid η z (Tcorr μ' (1 / ((n : ℝ) - 1)) xa xb)
      (Pc.mk0 0 0 (δ * μ) (δ * μ * (ea * μ - ea + eb * μ) / (μ - 1))) _ := fun z =>
    ((((Lm z).mul (((L1 z).add (Lxa z)).sub ((Lμ' z).mul (((L1 z).add (Lxa z)).add (Lxb z))))).mul
      (Li1mmup z)).congr_val (by unfold Tcorr; ring)).congr (by pieces)
  have Lterm1 : Valid η 0 ((1 - δ / n) * (1 + xa) * (1 + xb) *
      (1 + Acorr μ' (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) xa xb) * δ * (1 + ea)⁻¹)
      (Pc.mk0 0 0 δ (δ * eb)) _ :=
    ((((((Lomc 0).mul ((L1 0).add (Lxa 0))).mul ((L1 0).add (Lxb 0))).mul
      ((L1 0).add (LAab 0))).mul (Lδ 0)).mul (Li1pea 0)).congr (by pieces)
  -- the `v`-dependent factor, expanded in `z = ε v`
  have hG : ∀ v ∈ V, Valid η (ε v)
      (Gfun μ' (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) (1 / d') xa xb (ε' v))
      (Pc.mk 1 0 2 (-δ) (μ * (ea + eb) / (μ - 1)) 1
        (-μ * (-δ * ea * μ + δ * ea - δ * eb * μ + 2 * δ * eb + ea * t + eb * t) / (μ - 1))
        (-(-2 * δ * μ ^ 2 + 4 * δ * μ - δ + 2 * μ * t) / (μ - 1))
        (2 * μ * (ea + eb) / (μ - 1)) 0) _ := fun v hv =>
    have hz : Valid η (ε v) (ε v) (Pc.single 1 1 1) _ := Valid.var
    have hepv : Valid η (ε v) (ε' v) (Pc.mk 0 0 1 0 0 0 0 0 0 0) _ :=
      (((hz.add (Lc _)).mul (Lomci _)).congr_val (by rw [hε' v hv]; ring)).congr
        (by pieces)
    have hAav : Valid η (ε v) (Acorr μ' (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) xa (ε' v))
        (Pc.mk 0 0 0 0 (ea * μ / (μ - 1)) 0 (-ea * μ * (-δ * μ + δ + t) / (μ - 1))
          (-μ * (-δ * μ + δ + t) / (μ - 1)) 0 0) _ :=
      ((Lμ' _).acorr (Ls' _) (Lm _) (Li1mmup _) rfl (Lxa _) hepv).congr
        (by unfold Pc.acorr; pieces)
    have hAbv : Valid η (ε v) (Acorr μ' (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) xb (ε' v - 1 / d'))
        (Pc.mk 0 0 0 0 (eb * μ / (μ - 1)) 0 (-eb * μ * (-δ * μ + 2 * δ + t) / (μ - 1))
          (-μ * (-δ * μ + 2 * δ + t) / (μ - 1)) 0 0) _ :=
      ((Lμ' _).acorr (Ls' _) (Lm _) (Li1mmup _) rfl (Lxb _) (hepv.sub (Lδ' _))).congr
        (by unfold Pc.acorr; pieces)
    (((((L1 _).add hepv).mul (((L1 _).add hepv).sub (Lδ' _))).mul
      ((L1 _).add hAav)).mul ((L1 _).add hAbv)).congr_val (by unfold Gfun; ring) |>.congr
      (by pieces)
  -- moments of `ε` over `V`
  have LP0 : Valid η 0 (1 - 2 * (1 / (n : ℝ))) (Pc.mk0 1 0 (-2 * δ * μ) 0) _ :=
    ((L1 0).sub ((Valid.const (a := 2) (A := 2) (by norm_num) (by simp)).mul (Lν 0))).congr
      (by pieces)
  have LP1 : Valid η 0 (-(1 / (n : ℝ)) * (ea + eb)) (Pc.mk0 0 0 0 (-δ * μ * (ea + eb))) _ :=
    ((Lν 0).neg.mul ((Lea 0).add (Leb 0))).congr (by pieces)
  have LP2 : Valid η 0 (t - 1 / (n : ℝ) * (ea ^ 2 + eb ^ 2)) (Pc.mk0 0 0 t 0) _ :=
    (((Lt 0).sub ((Lν 0).mul (((Lea 0).mul (Lea 0)).add ((Leb 0).mul (Leb 0))))).congr_val
      (by ring)).congr (by pieces)
  have LP3 : Valid η 0 (s₃ - 1 / (n : ℝ) * (ea ^ 3 + eb ^ 3)) (Pc.mk0 0 0 0 s₃) _ :=
    (((Ls3 0).sub ((Lν 0).mul ((((Lea 0).mul (Lea 0)).mul (Lea 0)).add
      (((Leb 0).mul (Leb 0)).mul (Leb 0))))).congr_val (by ring)).congr (by pieces)
  have Lavg : Valid η 0
      ((∑ v ∈ V, Gfun μ' (σ2' / (d' * n)) (1 / ((n : ℝ) - 1)) (1 / d') xa xb (ε' v)) / n)
      (Pc.mk0 1 0 (-2 * δ * μ - δ + t)
        (μ * (-δ * ea * μ + δ * ea - δ * eb * μ + ea * t + eb * t) / (μ - 1))) _ :=
    (Valid.avg4 hne hεV hG hn0 hVn
      (by simp [hcardR]; field_simp)
      (by simp only [pow_one, hm1]; ring)
      (by rw [hm2]; field_simp; ring)
      (by rw [hm3]; field_simp; ring) LP0 LP1 LP2 LP3).congr (by pieces)
  have Lpref : Valid η 0 ((1 - δ / n) ^ 2 * (1 + 1 / ((n : ℝ) - 1)) * (1 + xa) * (1 + xb) *
      (1 + Tcorr μ' (1 / ((n : ℝ) - 1)) xa xb) * (1 + ea)⁻¹)
      (Pc.mk0 1 eb (δ * (2 * μ - 1)) (δ * μ * (ea * μ - ea + 3 * eb * μ - 2 * eb) / (μ - 1))) _ :=
    (((((((Lomc 0).mul (Lomc 0)).mul ((L1 0).add (Lm 0))).mul ((L1 0).add (Lxa 0))).mul
      ((L1 0).add (Lxb 0))).mul ((L1 0).add (LTp 0))).mul (Li1pea 0)).congr_val (by ring)
      |>.congr (by pieces)
  rw [hμ', badF_decomp V ε' xa xb μ σ2' d' δ ea n hμ.ne' hea1 hn0.ne' hn1.ne' hmud, ← hμ']
  have hfin := Lterm1.add (Lpref.mul Lavg)
  refine hfin.congr ?_
  pieces

/-! ### The ratio `ℛ(P^gr,Y^gr)/R^gr`

With `Fab = bad_{ab}(d-e_b)/μ`, `Fba = bad_{ba}(d-e_a)/μ`, `ν = 1/n`:
`ℛ/R^gr - 1 = μ · ratioG / ratioD`. -/

noncomputable def ratioG (μ t ea eb ν Fab Fba : ℝ) : ℝ :=
  -(ea - eb) - Fab * (1 - μ * (1 + ea) + ν)
    - (1 - μ * (1 + eb) + ν) * (ea - eb) * t * (1 - ν) / (1 - μ) ^ 2
    + Fba * (1 - μ * (1 + eb) + ν) * (1 + (ea - eb) * t * μ * (1 - ν) / (1 - μ) ^ 2)

noncomputable def ratioD (μ t ea eb ν Fba : ℝ) : ℝ :=
  (1 - μ * Fba) * (1 - μ * (1 + eb) + ν) * (1 + (ea - eb) * t * μ * (1 - ν) / (1 - μ) ^ 2)

set_option maxHeartbeats 0 in
/-- `ratioG = O(η⁴)` and `ratioD = (1-μ)² + O(η)`, given the expansions of `Fab`, `Fba`. -/
theorem ratio_expansion (bF : Bd) : ∃ bG bD : Bd, ∀ (η μ δ t ea eb ν Fab Fba : ℝ),
    0 < η → 0 < μ → μ ≤ 1 / 4 → 0 < δ → δ ≤ η ^ 2 → 0 ≤ t → t ≤ η ^ 2 →
    |ea| ≤ η → |eb| ≤ η → ν = μ * δ * (1 + μ * δ)⁻¹ →
    Valid η 0 Fab (Pc.mk0 1 eb (-δ + t) (t * (ea * μ + 2 * eb * μ - eb) / (μ - 1))) bF →
    Valid η 0 Fba (Pc.mk0 1 ea (-δ + t) (t * (eb * μ + 2 * ea * μ - ea) / (μ - 1))) bF →
    Valid η 0 (ratioG μ t ea eb ν Fab Fba) (Pc.mk0 0 0 0 0) bG ∧
    Valid η 0 (ratioD μ t ea eb ν Fba)
      (Pc.mk0 ((μ - 1) ^ 2) (μ * (ea + eb) * (μ - 1))
        (μ * (-2 * δ * μ + 2 * δ + ea * eb * μ + μ * t - t))
        (μ * (-δ * ea * μ - δ * eb * μ + 2 * ea * μ * t + 2 * eb * μ * t - eb * t))) bD := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  intro η μ δ t ea eb ν Fab Fba hη hμ hμ4 hδ hδη ht htη hea heb hν hFab hFba
  have hμ1 : μ - 1 ≠ 0 := by linarith
  have h1μ : (1 : ℝ) - μ ≠ 0 := by linarith
  have L1 : Valid η 0 1 (Pc.single 0 0 1) _ := Valid.const zero_le_one (by simp)
  have Lμ : Valid η 0 μ (Pc.single 0 0 μ) _ :=
    Valid.const (A := 1 / 4) (by norm_num) (by rw [abs_of_pos hμ]; exact hμ4)
  have Lδ : Valid η 0 δ (Pc.single 2 0 δ) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_pos hδ]; simpa using hδη)
  have Lt : Valid η 0 t (Pc.single 2 0 t) _ :=
    Valid.leaf 2 (by norm_num) zero_le_one (by rw [abs_of_nonneg ht]; simpa using htη)
  have Lea : Valid η 0 ea (Pc.single 1 0 ea) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using hea)
  have Leb : Valid η 0 eb (Pc.single 1 0 eb) _ :=
    Valid.leaf 1 (by norm_num) zero_le_one (by simpa using heb)
  have Lμδ : Valid η 0 (1 + μ * δ) (Pc.mk0 1 0 (μ * δ) 0) _ := (L1.add (Lμ.mul Lδ)).congr (by pieces)
  have Lim : Valid η 0 (1 + μ * δ)⁻¹ (Pc.mk0 1 0 (-(μ * δ)) 0) _ :=
    (Lμδ.inv (L := 1) one_pos (by show (1 : ℝ) ≤ |(1 : ℝ)|; norm_num)).congr (by pieces)
  have Lν : Valid η 0 ν (Pc.mk0 0 0 (μ * δ) 0) _ :=
    (((Lμ.mul Lδ).mul Lim).congr_val hν.symm).congr (by pieces)
  have L1μ : Valid η 0 (1 - μ) (Pc.mk0 (1 - μ) 0 0 0) _ := (L1.sub Lμ).congr (by pieces)
  have Li : Valid η 0 (1 - μ)⁻¹ (Pc.mk0 (-1 / (μ - 1)) 0 0 0) _ :=
    (L1μ.inv (L := 3 / 4) (by norm_num)
      (by show (3 : ℝ) / 4 ≤ |(1 : ℝ) - μ|; rw [abs_of_pos (by linarith)]; linarith)).congr
      (by pieces)
  have LA : Valid η 0 (1 - μ * (1 + ea) + ν) (Pc.mk0 (1 - μ) (-μ * ea) (μ * δ) 0) _ :=
    ((L1.sub (Lμ.mul (L1.add Lea))).add Lν).congr (by pieces)
  have LB : Valid η 0 (1 - μ * (1 + eb) + ν) (Pc.mk0 (1 - μ) (-μ * eb) (μ * δ) 0) _ :=
    ((L1.sub (Lμ.mul (L1.add Leb))).add Lν).congr (by pieces)
  have LK : Valid η 0 ((ea - eb) * t * (1 - ν) / (1 - μ) ^ 2)
      (Pc.mk0 0 0 0 ((ea - eb) * t / (μ - 1) ^ 2)) _ :=
    (((((Lea.sub Leb).mul Lt).mul (L1.sub Lν)).mul Li).mul Li).congr_val
      (by rw [div_eq_mul_inv, ← inv_pow]; ring) |>.congr (by pieces)
  have LC : Valid η 0 (1 + (ea - eb) * t * μ * (1 - ν) / (1 - μ) ^ 2)
      (Pc.mk0 1 0 0 (μ * (ea - eb) * t / (μ - 1) ^ 2)) _ :=
    (L1.add (Lμ.mul LK)).congr_val (by ring) |>.congr (by pieces)
  have hG : Valid η 0 (ratioG μ t ea eb ν Fab Fba) (Pc.mk0 0 0 0 0) _ :=
    ((((Lea.sub Leb).neg.sub (hFab.mul LA)).sub (LB.mul LK)).add
      ((hFba.mul LB).mul LC)).congr_val (by unfold ratioG; ring) |>.congr (by pieces)
  have hD : Valid η 0 (ratioD μ t ea eb ν Fba) (Pc.mk0 ((μ - 1) ^ 2) (μ * (ea + eb) * (μ - 1))
      (μ * (-2 * δ * μ + 2 * δ + ea * eb * μ + μ * t - t))
      (μ * (-δ * ea * μ - δ * eb * μ + 2 * ea * μ * t + 2 * eb * μ * t - eb * t))) _ :=
    (((L1.sub (Lμ.mul hFba)).mul LB).mul LC).congr_val (by unfold ratioD; ring)
      |>.congr (by pieces)
  constructor
  · exact hG
  · exact hD

end LW
