import MajorityDynamics.Literature.LWFormal.Counting
import MajorityDynamics.Literature.LWFormal.Close

set_option autoImplicit true

/-!
# §5: The operators `𝒫`, `𝒴`, `ℛ`, `𝒞` and their contraction properties

Everything is for `A = [n]⁽²⁾`.  Asymptotic statements are made with explicit constants.
-/

namespace LW

open Finset

variable {n : ℕ}

abbrev PFun (n : ℕ) := Fin n → Fin n → Seq n → ℝ
abbrev YFun (n : ℕ) := Fin n → Fin n → Fin n → Seq n → ℝ
abbrev RFun (n : ℕ) := Fin n → Fin n → Seq n → ℝ

/-- (5.1): `bad(p,y)(a,b,d)`. -/
noncomputable def bad (p : PFun n) (y : YFun n) (a b : Fin n) (d : Seq n) : ℝ :=
  if a = b then 0 else (p a b d + ∑ v ∈ (univ.erase a).erase b, y a v b d) / d a

/-- (5.2): `𝒫(p,r)(a,v,d)`. -/
noncomputable def opP (p : PFun n) (r : RFun n) (a v : Fin n) (d : Seq n) : ℝ :=
  d v * (∑ b ∈ univ.erase v,
    r b a (d - e v) * (1 - p b v (d - e b - e v)) / (1 - p a v (d - e a - e v)))⁻¹

/-- (5.3): `𝒴(p,y)(a,v,b,d)`. -/
noncomputable def opY (p : PFun n) (y : YFun n) (a v b : Fin n) (d : Seq n) : ℝ :=
  p a v d * (p b v (d - e a - e v) - y a v b (d - e a - e v)) / (1 - p a v (d - e a - e v))

/-- (5.4): `ℛ(p,y)(a,b,d)`. -/
noncomputable def opR (p : PFun n) (y : YFun n) (a b : Fin n) (d : Seq n) : ℝ :=
  (d a : ℝ) / d b * (1 - bad p y a b (d - e b)) / (1 - bad p y b a (d - e a))

/-- `𝒞(p,y) = (p̂, 𝒴(p̂, y))` with `p̂ = 𝒫(p, ℛ(p,y))`. -/
noncomputable def opC (p : PFun n) (y : YFun n) : PFun n × YFun n :=
  let p' := opP p (opR p y)
  (p', opY p' y)

def IsEven (d : Seq n) : Prop := Even (M1 d)

/-- `L¹` distance. -/
def dist1 (d d' : Seq n) : ℤ := ∑ i, |d i - d' i|

/-- `Q₀ˢ(d)`: even sequences within `L¹` distance `s` of `d`. -/
def Q0 (s : ℕ) (d : Seq n) : Set (Seq n) := {d' | IsEven d' ∧ dist1 d d' ≤ s}

/-- `Q₁ˢ(d)`: odd sequences within `L¹` distance `s` of `d`. -/
def Q1 (s : ℕ) (d : Seq n) : Set (Seq n) := {d' | ¬ IsEven d' ∧ dist1 d d' ≤ s}

/-- Definition 5.1: `(p,y) ∈ Π_μ(D₀)`. -/
structure InPi (μ : ℝ) (D₀ : Set (Seq n)) (p : PFun n) (y : YFun n) : Prop where
  pa : ∀ d ∈ D₀, IsEven d → ∀ a v, a ≠ v → 0 ≤ p a v d ∧ p a v d ≤ μ
  pb : ∀ d ∈ D₀, IsEven d → ∀ a b, a ≠ b →
    ∑ v ∈ (univ.erase a).erase b, y a v b d ≤ μ * d a
  pc : ∀ d ∈ D₀, IsEven d → ∀ a v b, a ≠ v → a ≠ b → v ≠ b →
    0 ≤ y a v b d ∧ y a v b d ≤ μ * p b v d

theorem InPi.mono {μ : ℝ} {D₀ D₁ : Set (Seq n)} {p : PFun n} {y : YFun n} (h : InPi μ D₀ p y)
    (hD : D₁ ⊆ D₀) : InPi μ D₁ p y :=
  ⟨fun d hd => h.pa d (hD hd), fun d hd => h.pb d (hD hd), fun d hd => h.pc d (hD hd)⟩

/-! ### `L¹` distance and parity -/

theorem dist1_comm (d d' : Seq n) : dist1 d d' = dist1 d' d := by
  simp [dist1, abs_sub_comm]

theorem dist1_triangle (d d' d'' : Seq n) : dist1 d d'' ≤ dist1 d d' + dist1 d' d'' := by
  unfold dist1
  rw [← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

theorem dist1_sub_e (d : Seq n) (a : Fin n) : dist1 d (d - e a) = 1 := by
  simp [dist1, e, Pi.single_apply, apply_ite abs]

theorem dist1_sub_e_sub_e (d : Seq n) (a b : Fin n) : dist1 d (d - e a - e b) ≤ 2 := by
  calc dist1 d (d - e a - e b) ≤ dist1 d (d - e a) + dist1 (d - e a) (d - e a - e b) :=
        dist1_triangle _ _ _
    _ = 2 := by rw [dist1_sub_e, dist1_sub_e]; norm_num

theorem M1_sub_e (d : Seq n) (a : Fin n) : M1 (d - e a) = M1 d - 1 := by
  simp [M1, e, sum_sub_distrib]

theorem isEven_sub_e_sub_e {d : Seq n} (a b : Fin n) : IsEven (d - e a - e b) ↔ IsEven d := by
  unfold IsEven
  rw [M1_sub_e, M1_sub_e, sub_sub, Int.even_sub, show (1 : ℤ) + 1 = 2 by norm_num]
  simp

theorem isEven_sub_e_of_odd {d : Seq n} (h : ¬ IsEven d) (a : Fin n) : IsEven (d - e a) := by
  unfold IsEven at *
  rw [M1_sub_e, Int.even_sub_one]; exact h

theorem not_isEven_sub_e_of_even {d : Seq n} (h : IsEven d) (a : Fin n) : ¬ IsEven (d - e a) := by
  unfold IsEven at *
  rw [M1_sub_e, Int.even_sub_one]; exact not_not.2 h

theorem Q0_mono {s t : ℕ} (h : s ≤ t) (d : Seq n) : Q0 s d ⊆ Q0 t d :=
  fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans (by exact_mod_cast h)⟩

theorem self_mem_Q0 {d : Seq n} (h : IsEven d) (s : ℕ) : d ∈ Q0 s d :=
  ⟨h, by simp [dist1]⟩

theorem sub_e_mem_Q0 {d : Seq n} (h : ¬ IsEven d) (a : Fin n) : d - e a ∈ Q0 1 d :=
  ⟨isEven_sub_e_of_odd h a, by rw [dist1_sub_e]; norm_num⟩

theorem sub_e_mem_Q1 {d : Seq n} (h : IsEven d) (a : Fin n) : d - e a ∈ Q1 1 d :=
  ⟨not_isEven_sub_e_of_even h a, by rw [dist1_sub_e]; norm_num⟩

theorem sub_e_sub_e_mem_Q0 {d : Seq n} (h : IsEven d) (a b : Fin n) : d - e a - e b ∈ Q0 2 d :=
  ⟨(isEven_sub_e_sub_e a b).2 h, dist1_sub_e_sub_e d a b⟩

theorem sub_e_apply (d : Seq n) (a w : Fin n) : (d - e a) w = d w - if w = a then 1 else 0 := by
  simp [e_apply]

theorem sub_e_apply_of_ne (d : Seq n) {a w : Fin n} (h : w ≠ a) : (d - e a) w = d w := by
  simp [e_apply, h]

/-! ### Estimates for `bad` -/

theorem bad_close {p p' : PFun n} {y y' : YFun n} {a b : Fin n} (hab : a ≠ b) {d' : Seq n} {ξ : ℝ}
    (hp : Close (p a b d') (p' a b d') ξ) (hp0 : 0 ≤ p' a b d')
    (hy : ∀ v, a ≠ v → v ≠ b → Close (y a v b d') (y' a v b d') ξ)
    (hy0 : ∀ v, a ≠ v → v ≠ b → 0 ≤ y' a v b d') :
    Close (bad p y a b d') (bad p' y' a b d') ξ := by
  simp only [bad, hab, if_false, div_eq_inv_mul]
  refine Close.const_mul _ (Close.add hp ?_ hp0 (sum_nonneg fun v hv => ?_))
  · refine Close.sum _ (fun v hv => ?_) fun v hv => ?_
    · simp only [mem_erase, mem_univ, and_true] at hv; exact hy v (Ne.symm hv.2) hv.1
    · simp only [mem_erase, mem_univ, and_true] at hv; exact hy0 v (Ne.symm hv.2) hv.1
  · simp only [mem_erase, mem_univ, and_true] at hv; exact hy0 v (Ne.symm hv.2) hv.1

theorem bad_bounds {μ : ℝ} {D₀ : Set (Seq n)} {p : PFun n} {y : YFun n} (hPi : InPi μ D₀ p y)
    (hμ : 0 ≤ μ) {d' : Seq n} (hd' : d' ∈ D₀) (hev : IsEven d') {a b : Fin n} (hab : a ≠ b)
    (hda : 2 ≤ d' a) : 0 ≤ bad p y a b d' ∧ bad p y a b d' ≤ 3 / 2 * μ := by
  simp only [bad, hab, if_false]
  have hda' : (2 : ℝ) ≤ d' a := by exact_mod_cast hda
  obtain ⟨hp0, hp1⟩ := hPi.pa d' hd' hev a b hab
  have hy := hPi.pb d' hd' hev a b hab
  have hy0 : 0 ≤ ∑ v ∈ (univ.erase a).erase b, y a v b d' := sum_nonneg fun v hv => by
    simp only [mem_erase, mem_univ, and_true] at hv; exact (hPi.pc d' hd' hev a v b (Ne.symm hv.2) hab hv.1).1
  constructor
  · positivity
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-! ### Lemma 5.2 with explicit constants -/

/-- Core estimate for (a). -/
theorem ratio_close {c β₁ β₂ β₁' β₂' x : ℝ} (hx : 0 ≤ x) (hx6 : x ≤ 1 / 6)
    (h1 : |β₁ - β₁'| ≤ x) (h2 : |β₂ - β₂'| ≤ x) (h1' : β₁' ≤ 1 / 2) (h2' : β₂' ≤ 1 / 2) :
    Close (c * (1 - β₁) / (1 - β₂)) (c * (1 - β₁') / (1 - β₂')) (8 * x) := by
  have e1 := Close.one_sub h1 h1'
  have e2 := (Close.one_sub h2 h2').inv_le (by positivity) (by linarith) (by linarith)
    (le_refl (2 * (2 * x)))
  have := (e1.mul e2 (by positivity)).const_mul c
  simp only [div_eq_mul_inv, mul_assoc]
  exact this.mono (by nlinarith)

/-- Core estimate for the terms in (b). -/
theorem term_close {r r' q q' qa qa' x : ℝ} (hx : 0 ≤ x) (hx6 : x ≤ 1 / 6)
    (hr : Close r r' x) (hq : |q - q'| ≤ x) (hqa : |qa - qa'| ≤ x) (hq' : q' ≤ 1 / 2)
    (hqa' : qa' ≤ 1 / 2) :
    Close (r * (1 - q) / (1 - qa)) (r' * (1 - q') / (1 - qa')) (10 * x) := by
  have e1 := Close.one_sub hq hq'
  have e2 := (Close.one_sub hqa hqa').inv_le (by positivity) (by linarith) (by linarith)
    (le_refl (2 * (2 * x)))
  have := (hr.mul e1 hx).mul e2 (by positivity)
  simp only [div_eq_mul_inv]
  refine this.mono ?_
  nlinarith [mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx, mul_le_mul_of_nonneg_left hx6 hx,
    mul_le_mul_of_nonneg_left hx6 (mul_nonneg hx hx)]

/-- Core estimate for (c). -/
theorem opY_close_core {p₀ p₀' q q' y y' qa qa' x μ : ℝ} (hx : 0 ≤ x) (hx6 : x ≤ 1 / 6)
    (hμ1 : μ ≤ 1 / 2) (hp₀ : Close p₀ p₀' x)
    (hq : Close q q' x) (hq0 : 0 ≤ q') (hy : |y - y'| ≤ x * q') (hy1 : y' ≤ μ * q')
    (hqa : Close qa qa' x) (hqa0 : 0 ≤ qa') (hqa1 : qa' ≤ μ) :
    Close (p₀ * (q - y) / (1 - qa)) (p₀' * (q' - y') / (1 - qa')) (14 * x) := by
  have eN : Close (q - y) (q' - y') (4 * x) := by
    unfold Close at *
    rw [abs_of_nonneg hq0] at hq
    rw [abs_of_nonneg (by nlinarith : 0 ≤ q' - y')]
    calc |q - y - (q' - y')| = |(q - q') - (y - y')| := by ring_nf
      _ ≤ |q - q'| + |y - y'| := abs_sub _ _
      _ ≤ 4 * x * (q' - y') := by
          nlinarith [mul_le_mul_of_nonneg_left hy1 hx, mul_le_mul_of_nonneg_left hμ1 (mul_nonneg hx hq0)]
  have eD : Close (1 - qa) (1 - qa') (2 * x) := by
    refine Close.one_sub ?_ (by linarith)
    unfold Close at hqa; rw [abs_of_nonneg hqa0] at hqa; nlinarith
  have e2 := eD.inv_le (by positivity) (by linarith) (by linarith) (le_refl (2 * (2 * x)))
  have := (hp₀.mul eN hx).mul e2 (by positivity)
  simp only [div_eq_mul_inv]
  refine this.mono ?_
  nlinarith [mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx, mul_le_mul_of_nonneg_left hx6 hx,
    mul_le_mul_of_nonneg_left hx6 (mul_nonneg hx hx)]

/-- Lemma 5.2 (a)–(c) with explicit constants: `C = 1/20`, `K = 20`.  We assume `μ₀ ξ ≤ 1/20`
(rather than `ξ ≤ 1`, `μ₀ < C`), which is all the proof uses; in (b) the comparison ratio
function `r'` is required to be nonnegative (as in the paper's domain `ℝ≥0`).  Only the
reference pair `(p', y')` needs to lie in `Π_{μ₀}` (the paper also assumes it of `(p, y)`). -/
theorem lemma_5_2_explicit (d : Seq n) (hd : ∀ a, 2 ≤ d a) {ξ μ₀ : ℝ} (hξ : 0 < ξ) (hμ₀ : 0 < μ₀)
    (hμ₁ : μ₀ ≤ 1 / 3) (hμξ : μ₀ * ξ ≤ 1 / 20) (p p' : PFun n) (y y' : YFun n) (r r' : RFun n) :
    -- (a)
    (¬ IsEven d → InPi μ₀ (Q0 1 d) p' y' →
      (∀ d' ∈ Q0 1 d, ∀ c w, c ≠ w → Close (p c w d') (p' c w d') ξ) →
      (∀ d' ∈ Q0 1 d, ∀ c w h, c ≠ w → c ≠ h → w ≠ h →
        Close (y c w h d') (y' c w h d') ξ) →
      ∀ a b, Close (opR p y a b d) (opR p' y' a b d) (20 * μ₀ * ξ)) ∧
    -- (b)
    (IsEven d → InPi μ₀ (Q0 2 d) p' y' → ∀ a v, a ≠ v →
      (∀ d' ∈ Q1 1 d, ∀ c, 0 ≤ r' c a d') →
      (∀ d' ∈ Q0 2 d, ∀ c, c ≠ v → Close (p c v d') (p' c v d') ξ) →
      (∀ d' ∈ Q1 1 d, ∀ c, c ≠ v → Close (r c a d') (r' c a d') (μ₀ * ξ)) →
      Close (opP p r a v d) (opP p' r' a v d) (20 * μ₀ * ξ)) ∧
    -- (c)
    (IsEven d → InPi μ₀ (Q0 2 d) p' y' →
      ∀ a v b, a ≠ v → a ≠ b → v ≠ b →
      (∀ d' ∈ Q0 2 d, ∀ c, c ≠ v → Close (p c v d') (p' c v d') (μ₀ * ξ)) →
      (∀ d' ∈ Q0 2 d, ∀ c w h, c ≠ w → c ≠ h → w ≠ h →
        Close (y c w h d') (y' c w h d') ξ) →
      Close (opY p y a v b d) (opY p' y' a v b d) (20 * μ₀ * ξ)) := by
  have hx : 0 ≤ μ₀ * ξ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro hodd hPi' hp hy a b
    by_cases hab : a = b
    · subst hab; simp only [opR, bad, if_true]; exact Close.refl _ (by positivity)
    have hba : b ≠ a := Ne.symm hab
    have hd₁ := sub_e_mem_Q0 hodd b
    have hd₂ := sub_e_mem_Q0 hodd a
    have hb₁ := bad_bounds hPi' hμ₀.le hd₁ hd₁.1 hab (by rw [sub_e_apply_of_ne _ hab]; exact hd a)
    have hb₂ := bad_bounds hPi' hμ₀.le hd₂ hd₂.1 hba (by rw [sub_e_apply_of_ne _ hba]; exact hd b)
    have c₁ := bad_close hab (hp _ hd₁ a b hab) (hPi'.pa _ hd₁ hd₁.1 a b hab).1
      (fun v hav hvb => hy _ hd₁ a v b hav hab hvb)
      (fun v hav hvb => (hPi'.pc _ hd₁ hd₁.1 a v b hav hab hvb).1)
    have c₂ := bad_close hba (hp _ hd₂ b a hba) (hPi'.pa _ hd₂ hd₂.1 b a hba).1
      (fun v hbv hva => hy _ hd₂ b v a hbv hba hva)
      (fun v hbv hva => (hPi'.pc _ hd₂ hd₂.1 b v a hbv hba hva).1)
    unfold Close at c₁ c₂
    rw [abs_of_nonneg hb₁.1] at c₁; rw [abs_of_nonneg hb₂.1] at c₂
    have := ratio_close (c := (d a : ℝ) / d b) (x := 3 / 2 * μ₀ * ξ) (by positivity)
      (by nlinarith) (c₁.trans (by nlinarith)) (c₂.trans (by nlinarith)) (by linarith) (by linarith)
    exact this.mono (by nlinarith)
  · intro hev hPi' a v hav hr0 hp hr
    have hva : v ≠ a := Ne.symm hav
    have hd₁ := sub_e_mem_Q1 hev v
    have hda := sub_e_sub_e_mem_Q0 hev a v
    have hqa := (hPi'.pa _ hda hda.1 a v hav)
    have hpa := hp _ hda a hav
    unfold Close at hpa; rw [abs_of_nonneg hqa.1] at hpa
    have hT : ∀ b ∈ univ.erase v,
        Close (r b a (d - e v) * (1 - p b v (d - e b - e v)) / (1 - p a v (d - e a - e v)))
          (r' b a (d - e v) * (1 - p' b v (d - e b - e v)) / (1 - p' a v (d - e a - e v)))
          (10 * (μ₀ * ξ)) := by
      intro b hb
      have hbv : b ≠ v := (mem_erase.1 hb).1
      have hdb := sub_e_sub_e_mem_Q0 hev b v
      have hqb := hPi'.pa _ hdb hdb.1 b v hbv
      have hpb := hp _ hdb b hbv
      unfold Close at hpb; rw [abs_of_nonneg hqb.1] at hpb
      exact term_close hx (by linarith) (hr _ hd₁ b hbv) (hpb.trans (by nlinarith))
        (hpa.trans (by nlinarith)) (by linarith) (by linarith)
    have hT0 : ∀ b ∈ univ.erase v,
        0 ≤ r' b a (d - e v) * (1 - p' b v (d - e b - e v)) / (1 - p' a v (d - e a - e v)) := by
      intro b hb
      have hbv : b ≠ v := (mem_erase.1 hb).1
      have hdb := sub_e_sub_e_mem_Q0 hev b v
      have hqb := hPi'.pa _ hdb hdb.1 b v hbv
      have := hr0 _ hd₁ b
      apply div_nonneg (mul_nonneg this (by linarith)) (by linarith)
    have hS := Close.sum _ hT hT0
    unfold opP
    by_cases hS0 : ∑ b ∈ univ.erase v,
        r' b a (d - e v) * (1 - p' b v (d - e b - e v)) / (1 - p' a v (d - e a - e v)) = 0
    · have : ∑ b ∈ univ.erase v,
          r b a (d - e v) * (1 - p b v (d - e b - e v)) / (1 - p a v (d - e a - e v)) = 0 := by
        unfold Close at hS; rw [hS0] at hS; simpa using hS
      rw [this, hS0]; exact Close.refl _ (by positivity)
    · exact (Close.const_mul _ (hS.inv_le (by positivity) (by linarith) hS0
        (le_refl _))).mono (by nlinarith)
  · intro hev hPi' a v b hav hab hvb hp hy
    have hd₀ := self_mem_Q0 hev 2
    have hd₂ := sub_e_sub_e_mem_Q0 hev a v
    have hqb := hPi'.pa _ hd₂ hd₂.1 b v hvb.symm
    have hqa := hPi'.pa _ hd₂ hd₂.1 a v hav
    have hyb := hPi'.pc _ hd₂ hd₂.1 a v b hav hab hvb
    have hy' := hy _ hd₂ a v b hav hab hvb
    unfold Close at hy'; rw [abs_of_nonneg hyb.1] at hy'
    have := opY_close_core (μ := μ₀) hx (by linarith) (by linarith) (hp _ hd₀ a hav)
      (hp _ hd₂ b hvb.symm) hqb.1
      (hy'.trans (by nlinarith [mul_le_mul_of_nonneg_left hyb.2 hξ.le])) hyb.2 (hp _ hd₂ a hav)
      hqa.1 hqa.2
    exact (this.mono (by nlinarith))

/-- Lemma 5.2 (a)–(c), with explicit constants `C` (smallness of `μ₀ ξ`) and `K` (the `O(·)`). -/
theorem lemma_5_2 :
    ∃ C K : ℝ, 0 < C ∧ 1 ≤ K ∧
      ∀ (n : ℕ) (d : Seq n), (∀ a, 2 ≤ d a) →
        ∀ ξ μ₀ : ℝ, 0 < ξ → 0 < μ₀ → μ₀ ≤ 1 / 3 → μ₀ * ξ ≤ C →
          ∀ (p p' : PFun n) (y y' : YFun n) (r r' : RFun n),
            (¬ IsEven d → InPi μ₀ (Q0 1 d) p' y' →
              (∀ d' ∈ Q0 1 d, ∀ c w, c ≠ w → Close (p c w d') (p' c w d') ξ) →
              (∀ d' ∈ Q0 1 d, ∀ c w h, c ≠ w → c ≠ h → w ≠ h →
                Close (y c w h d') (y' c w h d') ξ) →
              ∀ a b, Close (opR p y a b d) (opR p' y' a b d) (K * μ₀ * ξ)) ∧
            (IsEven d → InPi μ₀ (Q0 2 d) p' y' → ∀ a v, a ≠ v →
              (∀ d' ∈ Q1 1 d, ∀ c, 0 ≤ r' c a d') →
              (∀ d' ∈ Q0 2 d, ∀ c, c ≠ v → Close (p c v d') (p' c v d') ξ) →
              (∀ d' ∈ Q1 1 d, ∀ c, c ≠ v → Close (r c a d') (r' c a d') (μ₀ * ξ)) →
              Close (opP p r a v d) (opP p' r' a v d) (K * μ₀ * ξ)) ∧
            (IsEven d → InPi μ₀ (Q0 2 d) p' y' →
              ∀ a v b, a ≠ v → a ≠ b → v ≠ b →
              (∀ d' ∈ Q0 2 d, ∀ c, c ≠ v → Close (p c v d') (p' c v d') (μ₀ * ξ)) →
              (∀ d' ∈ Q0 2 d, ∀ c w h, c ≠ w → c ≠ h → w ≠ h →
                Close (y c w h d') (y' c w h d') ξ) →
              Close (opY p y a v b d) (opY p' y' a v b d) (K * μ₀ * ξ)) :=
  ⟨1 / 20, 20, by norm_num, by norm_num, fun n d hd ξ μ₀ hξ hμ₀ hμ₁ hμξ p p' y y' r r' =>
    lemma_5_2_explicit d hd hξ hμ₀ hμ₁ hμξ p p' y y' r r'⟩

/-- `Ω⁽ˢ⁾`: sequences of `Ω₀` whose `L¹`-ball of radius `s` lies in `Ω₀`. -/
def Omega (Ω₀ : Set (Seq n)) (s : ℕ) : Set (Seq n) :=
  {d | d ∈ Ω₀ ∧ ∀ d', dist1 d d' ≤ s → d' ∈ Ω₀}

theorem Omega_subset (Ω₀ : Set (Seq n)) (s : ℕ) : Omega Ω₀ s ⊆ Ω₀ := fun _ h => h.1

theorem Omega_mono {Ω₀ : Set (Seq n)} {s t : ℕ} (h : s ≤ t) : Omega Ω₀ t ⊆ Omega Ω₀ s :=
  fun _ ⟨h1, h2⟩ => ⟨h1, fun d' hd' => h2 d' (hd'.trans (by exact_mod_cast h))⟩

theorem mem_Omega_of_dist1 {Ω₀ : Set (Seq n)} {s t : ℕ} {d d' : Seq n}
    (hd : d ∈ Omega Ω₀ (s + t)) (h : dist1 d d' ≤ t) : d' ∈ Omega Ω₀ s :=
  ⟨hd.2 d' (h.trans (by push_cast; linarith)), fun d'' h'' =>
    hd.2 d'' ((dist1_triangle d d' d'').trans (by push_cast; linarith))⟩

theorem Q0_subset_Omega {Ω₀ : Set (Seq n)} {s t : ℕ} {d : Seq n} (hd : d ∈ Omega Ω₀ (s + t)) :
    Q0 t d ⊆ Omega Ω₀ s := fun _ h => mem_Omega_of_dist1 hd h.2

theorem Q1_subset_Omega {Ω₀ : Set (Seq n)} {s t : ℕ} {d : Seq n} (hd : d ∈ Omega Ω₀ (s + t)) :
    Q1 t d ⊆ Omega Ω₀ s := fun _ h => mem_Omega_of_dist1 hd h.2

theorem opR_nonneg {μ₀ : ℝ} {D : Set (Seq n)} {p : PFun n} {y : YFun n} (hPi : InPi μ₀ D p y)
    (hμ₀ : 0 ≤ μ₀) (hμ₁ : μ₀ ≤ 1 / 3) {d : Seq n} (hodd : ¬ IsEven d) (hd : ∀ a, 2 ≤ d a)
    (hQ : Q0 1 d ⊆ D) (a b : Fin n) : 0 ≤ opR p y a b d := by
  have h2a : (0 : ℝ) ≤ d a := by exact_mod_cast (hd a).trans' (by norm_num)
  have h2b : (0 : ℝ) ≤ d b := by exact_mod_cast (hd b).trans' (by norm_num)
  by_cases hab : a = b
  · subst hab; simp only [opR, bad, if_true, sub_zero, div_one]; positivity
  have hba : b ≠ a := Ne.symm hab
  have hd₁ := sub_e_mem_Q0 hodd b
  have hd₂ := sub_e_mem_Q0 hodd a
  have hb₁ := bad_bounds (hPi.mono hQ) hμ₀ hd₁ hd₁.1 hab
    (by rw [sub_e_apply_of_ne _ hab]; exact hd a)
  have hb₂ := bad_bounds (hPi.mono hQ) hμ₀ hd₂ hd₂.1 hba
    (by rw [sub_e_apply_of_ne _ hba]; exact hd b)
  unfold opR
  exact div_nonneg (mul_nonneg (div_nonneg h2a h2b) (by linarith)) (by linarith)

/-- `χ⁽ˢ⁾((p,y),(p',y')) ≤ ξ`, over even sequences of `Ω⁽ˢ⁾`, in the form
`p = p'(1 ± ξ)`, `y = y'(1 ± ξ)` (equivalent to the paper's `|log|`-metric up to a factor `2`
when `ξ ≤ 1/2`, see `Close.logClose`/`Close.of_logClose`). -/
def ChiLe (Ω₀ : Set (Seq n)) (s : ℕ) (p p' : PFun n) (y y' : YFun n) (ξ : ℝ) : Prop :=
  (∀ d ∈ Omega Ω₀ s, IsEven d → ∀ c w, c ≠ w → Close (p c w d) (p' c w d) ξ) ∧
  (∀ d ∈ Omega Ω₀ s, IsEven d → ∀ c w h, c ≠ w → c ≠ h → w ≠ h →
    Close (y c w h d) (y' c w h d) ξ)

/-- Lemma 5.3 with explicit constants `C = 1/8000`, `K = 8000`.

The paper's proof applies Lemma 5.2(c) to the pair `(𝒫(p', ℛ(p',y')), y')`, which needs this pair
to lie in `Π_{μ₀}` as well; we make that (implicit) hypothesis explicit.  Only the reference
pair is needed in `Π_{μ₀}`. -/
theorem lemma_5_3_explicit (Ω₀ : Set (Seq n)) (hΩ : ∀ d ∈ Ω₀, ∀ a, 2 ≤ d a) {ξ μ₀ : ℝ}
    (hξ : 0 < ξ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1 / 3) (hμξ : μ₀ * ξ ≤ 1 / 8000) (s : ℕ)
    (p p' : PFun n) (y y' : YFun n) (hPi' : InPi μ₀ (Omega Ω₀ s) p' y')
    (hPi'' : InPi μ₀ (Omega Ω₀ (s + 2)) (opP p' (opR p' y')) y')
    (hχ : ChiLe Ω₀ s p p' y y' ξ) :
    ChiLe Ω₀ (s + 4) (opC p y).1 (opC p' y').1 (opC p y).2 (opC p' y').2 (8000 * μ₀ * ξ) := by
  have hx : 0 ≤ μ₀ * ξ := by positivity
  -- Step 1: `ℛ` on odd sequences of `Ω⁽ˢ⁺¹⁾`.
  have hr : ∀ d₁ ∈ Omega Ω₀ (s + 1), ¬ IsEven d₁ →
      ∀ a b, Close (opR p y a b d₁) (opR p' y' a b d₁) (20 * μ₀ * ξ) := by
    intro d₁ hd₁ hodd a b
    have hQ : Q0 1 d₁ ⊆ Omega Ω₀ s := Q0_subset_Omega hd₁
    exact (lemma_5_2_explicit d₁ (hΩ _ (Omega_subset _ _ hd₁)) hξ hμ₀ hμ₁ (by linarith) p p' y y'
      (opR p y) (opR p' y')).1 hodd (hPi'.mono hQ)
      (fun d' hd' c w hcw => hχ.1 d' (hQ hd') hd'.1 c w hcw)
      (fun d' hd' c w h hcw hch hwh => hχ.2 d' (hQ hd') hd'.1 c w h hcw hch hwh) a b
  -- Step 2: `𝒫` on even sequences of `Ω⁽ˢ⁺²⁾`.
  have hP : ∀ d₂ ∈ Omega Ω₀ (s + 2), IsEven d₂ → ∀ a v, a ≠ v →
      Close (opP p (opR p y) a v d₂) (opP p' (opR p' y') a v d₂) (400 * μ₀ * ξ) := by
    intro d₂ hd₂ hev a v hav
    have hQ0 : Q0 2 d₂ ⊆ Omega Ω₀ s := Q0_subset_Omega hd₂
    have hQ1 : Q1 1 d₂ ⊆ Omega Ω₀ (s + 1) := Q1_subset_Omega hd₂
    have := (lemma_5_2_explicit d₂ (hΩ _ (Omega_subset _ _ hd₂)) (ξ := 20 * ξ) (by positivity)
      hμ₀ hμ₁ (by linarith) p p' y y' (opR p y) (opR p' y')).2.1 hev (hPi'.mono hQ0) a v hav
      (fun d' hd' c => opR_nonneg hPi' hμ₀.le hμ₁ hd'.1 (hΩ _ (Omega_subset _ _ (hQ1 hd')))
        (Q0_subset_Omega (hQ1 hd')) c a)
      (fun d' hd' c hcv => (hχ.1 d' (hQ0 hd') hd'.1 c v hcv).mono (by linarith))
      (fun d' hd' c hcv => (hr d' (hQ1 hd') hd'.1 c a).mono (le_of_eq (by ring)))
    exact this.mono (le_of_eq (by ring))
  -- Step 3: `𝒴` on even sequences of `Ω⁽ˢ⁺⁴⁾`.
  refine ⟨fun d hd hev c w hcw => (hP d (Omega_mono (by omega) hd) hev c w hcw).mono
    (by linarith), fun d₃ hd₃ hev a v b hav hab hvb => ?_⟩
  have hQ0 : Q0 2 d₃ ⊆ Omega Ω₀ (s + 2) := Q0_subset_Omega hd₃
  have := (lemma_5_2_explicit d₃ (hΩ _ (Omega_subset _ _ hd₃)) (ξ := 400 * ξ) (by positivity)
    hμ₀ hμ₁ (by linarith) (opP p (opR p y)) (opP p' (opR p' y')) y y' (opR p y)
    (opR p' y')).2.2 hev (hPi''.mono hQ0) a v b hav hab hvb
    (fun d' hd' c hcv => (hP d' (hQ0 hd') hd'.1 c v hcv).mono (le_of_eq (by ring)))
    (fun d' hd' c w h hcw hch hwh =>
      (hχ.2 d' (Omega_mono (by omega) (hQ0 hd')) hd'.1 c w h hcw hch hwh).mono (by linarith))
  exact this.mono (le_of_eq (by ring))

/-- Lemma 5.3: `χ⁽ˢ⁺⁴⁾(𝒞(p,y), 𝒞(p',y')) = O(μ₀ ξ)`, with explicit constants. -/
theorem lemma_5_3 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (n : ℕ) (Ω₀ : Set (Seq n)), (∀ d ∈ Ω₀, ∀ a, 2 ≤ d a) →
        ∀ ξ μ₀ : ℝ, 0 < ξ → 0 < μ₀ → μ₀ ≤ 1 / 3 → μ₀ * ξ ≤ C →
          ∀ (s : ℕ) (p p' : PFun n) (y y' : YFun n),
            InPi μ₀ (Omega Ω₀ s) p' y' → InPi μ₀ (Omega Ω₀ (s + 2)) (opP p' (opR p' y')) y' →
            ChiLe Ω₀ s p p' y y' ξ →
            ChiLe Ω₀ (s + 4) (opC p y).1 (opC p' y').1 (opC p y).2 (opC p' y').2 (K * μ₀ * ξ) :=
  ⟨1 / 8000, 8000, by norm_num, by norm_num, fun n Ω₀ hΩ ξ μ₀ hξ hμ₀ hμ₁ hμξ s p p' y y' h1 h2 h3 =>
    lemma_5_3_explicit Ω₀ hΩ hξ hμ₀ hμ₁ hμξ s p p' y y' h1 h2 h3⟩

end LW
