import MajorityDynamics.Literature.LWFormal.Bip.Counting
import MajorityDynamics.Literature.LWFormal.Operators

set_option autoImplicit true

/-!
# §2.3 for bipartite graphs: the operators `𝒫`, `𝒴`, `ℛ`, `𝒞` and their contraction

The role of the parity of `M₁(d)` in the graph case is played by *balance*: `M₁(s) = M₁(t)`
("balanced", where `P` and `Y` live) versus `M₁(s) = M₁(t) + 1` ("S-heavy", where `R` lives).
-/

namespace LW.Bip

open Finset

variable {ℓ n : ℕ}

abbrev PFun (ℓ n : ℕ) := Fin ℓ → Fin n → BSeq ℓ n → ℝ
abbrev YFun (ℓ n : ℕ) := Fin ℓ → Fin n → Fin ℓ → BSeq ℓ n → ℝ
abbrev RFun (ℓ n : ℕ) := Fin ℓ → Fin ℓ → BSeq ℓ n → ℝ

/-- `bad(p,y)(a,b,d) = ∑_v y_avb(d) / s_a` (`a, b ∈ S` are never adjacent). -/
noncomputable def bad (_p : PFun ℓ n) (y : YFun ℓ n) (a b : Fin ℓ) (d : BSeq ℓ n) : ℝ :=
  if a = b then 0 else (∑ v, y a v b d) / d.1 a

/-- `𝒫(p,r)(a,v,d)`. -/
noncomputable def opP (p : PFun ℓ n) (r : RFun ℓ n) (a : Fin ℓ) (v : Fin n) (d : BSeq ℓ n) : ℝ :=
  d.2 v * (∑ b, r b a (d - eT v) * (1 - p b v (d - eS b - eT v)) /
    (1 - p a v (d - eS a - eT v)))⁻¹

/-- `𝒴(p,y)(a,v,b,d)`. -/
noncomputable def opY (p : PFun ℓ n) (y : YFun ℓ n) (a : Fin ℓ) (v : Fin n) (b : Fin ℓ)
    (d : BSeq ℓ n) : ℝ :=
  p a v d * (p b v (d - eS a - eT v) - y a v b (d - eS a - eT v)) / (1 - p a v (d - eS a - eT v))

/-- `ℛ(p,y)(a,b,d)`. -/
noncomputable def opR (p : PFun ℓ n) (y : YFun ℓ n) (a b : Fin ℓ) (d : BSeq ℓ n) : ℝ :=
  (d.1 a : ℝ) / d.1 b * (1 - bad p y a b (d - eS b)) / (1 - bad p y b a (d - eS a))

/-- `𝒞(p,y) = (p̂, 𝒴(p̂, y))` with `p̂ = 𝒫(p, ℛ(p,y))`. -/
noncomputable def opC (p : PFun ℓ n) (y : YFun ℓ n) : PFun ℓ n × YFun ℓ n :=
  let p' := opP p (opR p y)
  (p', opY p' y)

/-- Balanced: `∑ s = ∑ t`. -/
def Bal (d : BSeq ℓ n) : Prop := M1 d.1 = M1 d.2

/-- S-heavy: `∑ s = ∑ t + 1`. -/
def SH (d : BSeq ℓ n) : Prop := M1 d.1 = M1 d.2 + 1

/-- `L¹` distance. -/
def dist1 (d d' : BSeq ℓ n) : ℤ := LW.dist1 d.1 d'.1 + LW.dist1 d.2 d'.2

/-- Balanced sequences within `L¹` distance `s` of `d`. -/
def Q0 (s : ℕ) (d : BSeq ℓ n) : Set (BSeq ℓ n) := {d' | Bal d' ∧ dist1 d d' ≤ s}

/-- S-heavy sequences within `L¹` distance `s` of `d`. -/
def Q1 (s : ℕ) (d : BSeq ℓ n) : Set (BSeq ℓ n) := {d' | SH d' ∧ dist1 d d' ≤ s}

/-- Definition 2.7: `(p,y) ∈ Π_μ(D₀)`. -/
structure InPi (μ : ℝ) (D₀ : Set (BSeq ℓ n)) (p : PFun ℓ n) (y : YFun ℓ n) : Prop where
  pa : ∀ d ∈ D₀, Bal d → ∀ a v, 0 ≤ p a v d ∧ p a v d ≤ μ
  pb : ∀ d ∈ D₀, Bal d → ∀ a b, a ≠ b → ∑ v, y a v b d ≤ μ * d.1 a
  pc : ∀ d ∈ D₀, Bal d → ∀ a v b, a ≠ b → 0 ≤ y a v b d ∧ y a v b d ≤ μ * p b v d

theorem InPi.mono {μ : ℝ} {D₀ D₁ : Set (BSeq ℓ n)} {p : PFun ℓ n} {y : YFun ℓ n}
    (h : InPi μ D₀ p y) (hD : D₁ ⊆ D₀) : InPi μ D₁ p y :=
  ⟨fun d hd => h.pa d (hD hd), fun d hd => h.pb d (hD hd), fun d hd => h.pc d (hD hd)⟩

/-! ### `L¹` distance and balance -/

theorem dist1_comm (d d' : BSeq ℓ n) : dist1 d d' = dist1 d' d := by
  simp [dist1, LW.dist1_comm]

theorem dist1_triangle (d d' d'' : BSeq ℓ n) : dist1 d d'' ≤ dist1 d d' + dist1 d' d'' := by
  unfold dist1
  have := LW.dist1_triangle d.1 d'.1 d''.1
  have := LW.dist1_triangle d.2 d'.2 d''.2
  linarith

theorem dist1_self (d : BSeq ℓ n) : dist1 d d = 0 := by simp [dist1, LW.dist1]

theorem dist1_sub_eS (d : BSeq ℓ n) (a : Fin ℓ) : dist1 d (d - eS a) = 1 := by
  have := LW.dist1_sub_e d.1 a
  simp only [dist1, sub_eS_fst, sub_eS_snd, this]
  simp [LW.dist1]

theorem dist1_sub_eT (d : BSeq ℓ n) (v : Fin n) : dist1 d (d - eT v) = 1 := by
  have := LW.dist1_sub_e d.2 v
  simp only [dist1, sub_eT_fst, sub_eT_snd, this]
  simp [LW.dist1]

theorem dist1_sub_eS_sub_eT (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) :
    dist1 d (d - eS a - eT v) ≤ 2 := by
  calc dist1 d (d - eS a - eT v) ≤ dist1 d (d - eS a) + dist1 (d - eS a) (d - eS a - eT v) :=
        dist1_triangle _ _ _
    _ = 2 := by rw [dist1_sub_eS, dist1_sub_eT]; norm_num

theorem M1_sub_eS_fst (d : BSeq ℓ n) (a : Fin ℓ) : M1 (d - eS a).1 = M1 d.1 - 1 := by
  simp [LW.M1_sub_e]

theorem bal_sub_eS_sub_eT {d : BSeq ℓ n} (a : Fin ℓ) (v : Fin n) :
    Bal (d - eS a - eT v) ↔ Bal d := by
  unfold Bal
  simp only [sub_eT_fst, sub_eS_fst, sub_eT_snd, sub_eS_snd, LW.M1_sub_e]
  omega

theorem bal_sub_eS_of_SH {d : BSeq ℓ n} (h : SH d) (a : Fin ℓ) : Bal (d - eS a) := by
  unfold Bal SH at *
  simp only [sub_eS_fst, sub_eS_snd, LW.M1_sub_e]
  omega

theorem SH_sub_eT_of_bal {d : BSeq ℓ n} (h : Bal d) (v : Fin n) : SH (d - eT v) := by
  unfold Bal SH at *
  simp only [sub_eT_fst, sub_eT_snd, LW.M1_sub_e]
  omega

theorem Q0_mono {s t : ℕ} (h : s ≤ t) (d : BSeq ℓ n) : Q0 s d ⊆ Q0 t d :=
  fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans (by exact_mod_cast h)⟩

theorem self_mem_Q0 {d : BSeq ℓ n} (h : Bal d) (s : ℕ) : d ∈ Q0 s d :=
  ⟨h, by rw [dist1_self]; positivity⟩

theorem sub_eS_mem_Q0 {d : BSeq ℓ n} (h : SH d) (a : Fin ℓ) : d - eS a ∈ Q0 1 d :=
  ⟨bal_sub_eS_of_SH h a, by rw [dist1_sub_eS]; norm_num⟩

theorem sub_eT_mem_Q1 {d : BSeq ℓ n} (h : Bal d) (v : Fin n) : d - eT v ∈ Q1 1 d :=
  ⟨SH_sub_eT_of_bal h v, by rw [dist1_sub_eT]; norm_num⟩

theorem sub_eS_sub_eT_mem_Q0 {d : BSeq ℓ n} (h : Bal d) (a : Fin ℓ) (v : Fin n) :
    d - eS a - eT v ∈ Q0 2 d :=
  ⟨(bal_sub_eS_sub_eT a v).2 h, dist1_sub_eS_sub_eT d a v⟩

theorem sub_eS_fst_apply_of_ne (d : BSeq ℓ n) {a b : Fin ℓ} (h : b ≠ a) :
    (d - eS a).1 b = d.1 b := by
  simp [e_apply, h]

/-! ### Estimates for `bad` -/

theorem bad_close (p p' : PFun ℓ n) {y y' : YFun ℓ n} {a b : Fin ℓ} (hab : a ≠ b) {d' : BSeq ℓ n}
    {ξ : ℝ} (hy : ∀ v, Close (y a v b d') (y' a v b d') ξ) (hy0 : ∀ v, 0 ≤ y' a v b d') :
    Close (bad p y a b d') (bad p' y' a b d') ξ := by
  simp only [bad, hab, if_false, div_eq_inv_mul]
  exact Close.const_mul _ (Close.sum _ (fun v _ => hy v) fun v _ => hy0 v)

theorem bad_bounds {μ : ℝ} {D₀ : Set (BSeq ℓ n)} {p : PFun ℓ n} {y : YFun ℓ n}
    (hPi : InPi μ D₀ p y) (_hμ : 0 ≤ μ) {d' : BSeq ℓ n} (hd' : d' ∈ D₀) (hbal : Bal d')
    {a b : Fin ℓ} (hab : a ≠ b) (hda : 1 ≤ d'.1 a) :
    0 ≤ bad p y a b d' ∧ bad p y a b d' ≤ μ := by
  simp only [bad, hab, if_false]
  have hda' : (1 : ℝ) ≤ d'.1 a := by exact_mod_cast hda
  have hy := hPi.pb d' hd' hbal a b hab
  have hy0 : 0 ≤ ∑ v, y a v b d' :=
    sum_nonneg fun v _ => (hPi.pc d' hd' hbal a v b hab).1
  constructor
  · positivity
  · rw [div_le_iff₀ (by linarith)]; exact hy

/-! ### Lemma 2.8 (= Lemma 5.2 of the graph paper) with explicit constants -/

/-- Lemma 2.8 (a)–(c) with explicit constants `C = 1/20`, `K = 20`.  Only the reference pair
`(p', y')` needs to lie in `Π_{μ₀}`; in (b) the comparison ratio function `r'` is required to be
nonnegative. -/
theorem lemma_2_8_explicit (d : BSeq ℓ n) (hd : ∀ a, 1 ≤ d.1 a) {ξ μ₀ : ℝ} (hξ : 0 < ξ)
    (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1 / 3) (hμξ : μ₀ * ξ ≤ 1 / 20) (p p' : PFun ℓ n) (y y' : YFun ℓ n)
    (r r' : RFun ℓ n) :
    -- (a)
    (SH d → InPi μ₀ (Q0 1 d) p' y' →
      (∀ d' ∈ Q0 1 d, ∀ c w h, c ≠ h → Close (y c w h d') (y' c w h d') ξ) →
      ∀ a b, Close (opR p y a b d) (opR p' y' a b d) (20 * μ₀ * ξ)) ∧
    -- (b)
    (Bal d → InPi μ₀ (Q0 2 d) p' y' → ∀ a v,
      (∀ d' ∈ Q1 1 d, ∀ c, 0 ≤ r' c a d') →
      (∀ d' ∈ Q0 2 d, ∀ c, Close (p c v d') (p' c v d') ξ) →
      (∀ d' ∈ Q1 1 d, ∀ c, Close (r c a d') (r' c a d') (μ₀ * ξ)) →
      Close (opP p r a v d) (opP p' r' a v d) (20 * μ₀ * ξ)) ∧
    -- (c)
    (Bal d → InPi μ₀ (Q0 2 d) p' y' → ∀ a v b, a ≠ b →
      (∀ d' ∈ Q0 2 d, ∀ c, Close (p c v d') (p' c v d') (μ₀ * ξ)) →
      (∀ d' ∈ Q0 2 d, ∀ c w h, c ≠ h → Close (y c w h d') (y' c w h d') ξ) →
      Close (opY p y a v b d) (opY p' y' a v b d) (20 * μ₀ * ξ)) := by
  have hx : 0 ≤ μ₀ * ξ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro hSH hPi' hy a b
    by_cases hab : a = b
    · subst hab; simp only [opR, bad, if_true]; exact Close.refl _ (by positivity)
    have hba : b ≠ a := Ne.symm hab
    have hd₁ := sub_eS_mem_Q0 hSH b
    have hd₂ := sub_eS_mem_Q0 hSH a
    have hb₁ := bad_bounds hPi' hμ₀.le hd₁ hd₁.1 hab
      (by rw [sub_eS_fst_apply_of_ne _ hab]; exact hd a)
    have hb₂ := bad_bounds hPi' hμ₀.le hd₂ hd₂.1 hba
      (by rw [sub_eS_fst_apply_of_ne _ hba]; exact hd b)
    have c₁ := bad_close p p' hab (fun v => hy _ hd₁ a v b hab)
      (fun v => (hPi'.pc _ hd₁ hd₁.1 a v b hab).1)
    have c₂ := bad_close p p' hba (fun v => hy _ hd₂ b v a hba)
      (fun v => (hPi'.pc _ hd₂ hd₂.1 b v a hba).1)
    unfold Close at c₁ c₂
    rw [abs_of_nonneg hb₁.1] at c₁; rw [abs_of_nonneg hb₂.1] at c₂
    have := ratio_close (c := (d.1 a : ℝ) / d.1 b) (x := μ₀ * ξ) hx
      (by nlinarith) (c₁.trans (by nlinarith)) (c₂.trans (by nlinarith)) (by linarith)
      (by linarith)
    exact this.mono (by nlinarith)
  · intro hbal hPi' a v hr0 hp hr
    have hd₁ := sub_eT_mem_Q1 hbal v
    have hda := sub_eS_sub_eT_mem_Q0 hbal a v
    have hqa := (hPi'.pa _ hda hda.1 a v)
    have hpa := hp _ hda a
    unfold Close at hpa; rw [abs_of_nonneg hqa.1] at hpa
    have hT : ∀ b ∈ (univ : Finset (Fin ℓ)),
        Close (r b a (d - eT v) * (1 - p b v (d - eS b - eT v)) / (1 - p a v (d - eS a - eT v)))
          (r' b a (d - eT v) * (1 - p' b v (d - eS b - eT v)) / (1 - p' a v (d - eS a - eT v)))
          (10 * (μ₀ * ξ)) := by
      intro b _
      have hdb := sub_eS_sub_eT_mem_Q0 hbal b v
      have hqb := hPi'.pa _ hdb hdb.1 b v
      have hpb := hp _ hdb b
      unfold Close at hpb; rw [abs_of_nonneg hqb.1] at hpb
      exact term_close hx (by linarith) (hr _ hd₁ b) (hpb.trans (by nlinarith))
        (hpa.trans (by nlinarith)) (by linarith) (by linarith)
    have hT0 : ∀ b ∈ (univ : Finset (Fin ℓ)),
        0 ≤ r' b a (d - eT v) * (1 - p' b v (d - eS b - eT v)) /
          (1 - p' a v (d - eS a - eT v)) := by
      intro b _
      have hdb := sub_eS_sub_eT_mem_Q0 hbal b v
      have hqb := hPi'.pa _ hdb hdb.1 b v
      have := hr0 _ hd₁ b
      apply div_nonneg (mul_nonneg this (by linarith)) (by linarith)
    have hS := Close.sum _ hT hT0
    unfold opP
    by_cases hS0 : ∑ b, r' b a (d - eT v) * (1 - p' b v (d - eS b - eT v)) /
        (1 - p' a v (d - eS a - eT v)) = 0
    · have : ∑ b, r b a (d - eT v) * (1 - p b v (d - eS b - eT v)) /
          (1 - p a v (d - eS a - eT v)) = 0 := by
        unfold Close at hS; rw [hS0] at hS; simpa using hS
      rw [this, hS0]; exact Close.refl _ (by positivity)
    · exact (Close.const_mul _ (hS.inv_le (by positivity) (by linarith) hS0
        (le_refl _))).mono (by nlinarith)
  · intro hbal hPi' a v b hab hp hy
    have hd₀ := self_mem_Q0 hbal 2
    have hd₂ := sub_eS_sub_eT_mem_Q0 hbal a v
    have hqb := hPi'.pa _ hd₂ hd₂.1 b v
    have hqa := hPi'.pa _ hd₂ hd₂.1 a v
    have hyb := hPi'.pc _ hd₂ hd₂.1 a v b hab
    have hy' := hy _ hd₂ a v b hab
    unfold Close at hy'; rw [abs_of_nonneg hyb.1] at hy'
    have := opY_close_core (μ := μ₀) hx (by linarith) (by linarith) (hp _ hd₀ a)
      (hp _ hd₂ b) hqb.1
      (hy'.trans (by nlinarith [mul_le_mul_of_nonneg_left hyb.2 hξ.le])) hyb.2 (hp _ hd₂ a)
      hqa.1 hqa.2
    exact (this.mono (by nlinarith))

/-- `Ω⁽ˢ⁾`: sequences of `Ω₀` whose `L¹`-ball of radius `s` lies in `Ω₀`. -/
def Omega (Ω₀ : Set (BSeq ℓ n)) (s : ℕ) : Set (BSeq ℓ n) :=
  {d | d ∈ Ω₀ ∧ ∀ d', dist1 d d' ≤ s → d' ∈ Ω₀}

theorem Omega_subset (Ω₀ : Set (BSeq ℓ n)) (s : ℕ) : Omega Ω₀ s ⊆ Ω₀ := fun _ h => h.1

theorem Omega_mono {Ω₀ : Set (BSeq ℓ n)} {s t : ℕ} (h : s ≤ t) : Omega Ω₀ t ⊆ Omega Ω₀ s :=
  fun _ ⟨h1, h2⟩ => ⟨h1, fun d' hd' => h2 d' (hd'.trans (by exact_mod_cast h))⟩

theorem mem_Omega_of_dist1 {Ω₀ : Set (BSeq ℓ n)} {s t : ℕ} {d d' : BSeq ℓ n}
    (hd : d ∈ Omega Ω₀ (s + t)) (h : dist1 d d' ≤ t) : d' ∈ Omega Ω₀ s :=
  ⟨hd.2 d' (h.trans (by push_cast; linarith)), fun d'' h'' =>
    hd.2 d'' ((dist1_triangle d d' d'').trans (by push_cast; linarith))⟩

theorem Q0_subset_Omega {Ω₀ : Set (BSeq ℓ n)} {s t : ℕ} {d : BSeq ℓ n}
    (hd : d ∈ Omega Ω₀ (s + t)) : Q0 t d ⊆ Omega Ω₀ s := fun _ h => mem_Omega_of_dist1 hd h.2

theorem Q1_subset_Omega {Ω₀ : Set (BSeq ℓ n)} {s t : ℕ} {d : BSeq ℓ n}
    (hd : d ∈ Omega Ω₀ (s + t)) : Q1 t d ⊆ Omega Ω₀ s := fun _ h => mem_Omega_of_dist1 hd h.2

theorem opR_nonneg {μ₀ : ℝ} {D : Set (BSeq ℓ n)} {p : PFun ℓ n} {y : YFun ℓ n}
    (hPi : InPi μ₀ D p y) (hμ₀ : 0 ≤ μ₀) (hμ₁ : μ₀ ≤ 1 / 3) {d : BSeq ℓ n} (hSH : SH d)
    (hd : ∀ a, 1 ≤ d.1 a) (hQ : Q0 1 d ⊆ D) (a b : Fin ℓ) : 0 ≤ opR p y a b d := by
  have h2a : (0 : ℝ) ≤ d.1 a := by exact_mod_cast (hd a).trans' (by norm_num)
  have h2b : (0 : ℝ) ≤ d.1 b := by exact_mod_cast (hd b).trans' (by norm_num)
  by_cases hab : a = b
  · subst hab; simp only [opR, bad, if_true, sub_zero, div_one]; positivity
  have hba : b ≠ a := Ne.symm hab
  have hd₁ := sub_eS_mem_Q0 hSH b
  have hd₂ := sub_eS_mem_Q0 hSH a
  have hb₁ := bad_bounds (hPi.mono hQ) hμ₀ hd₁ hd₁.1 hab
    (by rw [sub_eS_fst_apply_of_ne _ hab]; exact hd a)
  have hb₂ := bad_bounds (hPi.mono hQ) hμ₀ hd₂ hd₂.1 hba
    (by rw [sub_eS_fst_apply_of_ne _ hba]; exact hd b)
  unfold opR
  exact div_nonneg (mul_nonneg (div_nonneg h2a h2b) (by linarith)) (by linarith)

/-- `χ⁽ˢ⁾((p,y),(p',y')) ≤ ξ` over balanced sequences of `Ω⁽ˢ⁾`. -/
def ChiLe (Ω₀ : Set (BSeq ℓ n)) (s : ℕ) (p p' : PFun ℓ n) (y y' : YFun ℓ n) (ξ : ℝ) : Prop :=
  (∀ d ∈ Omega Ω₀ s, Bal d → ∀ c w, Close (p c w d) (p' c w d) ξ) ∧
  (∀ d ∈ Omega Ω₀ s, Bal d → ∀ c w h, c ≠ h → Close (y c w h d) (y' c w h d) ξ)

/-- Contraction of `𝒞` (Lemma 5.3 of the graph paper, as used in §2.3 of the bipartite paper),
with explicit constants `C = 1/8000`, `K = 8000`. -/
theorem contraction_explicit (Ω₀ : Set (BSeq ℓ n)) (hΩ : ∀ d ∈ Ω₀, ∀ a, 1 ≤ d.1 a) {ξ μ₀ : ℝ}
    (hξ : 0 < ξ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1 / 3) (hμξ : μ₀ * ξ ≤ 1 / 8000) (s : ℕ)
    (p p' : PFun ℓ n) (y y' : YFun ℓ n) (hPi' : InPi μ₀ (Omega Ω₀ s) p' y')
    (hPi'' : InPi μ₀ (Omega Ω₀ (s + 2)) (opP p' (opR p' y')) y')
    (hχ : ChiLe Ω₀ s p p' y y' ξ) :
    ChiLe Ω₀ (s + 4) (opC p y).1 (opC p' y').1 (opC p y).2 (opC p' y').2 (8000 * μ₀ * ξ) := by
  have hx : 0 ≤ μ₀ * ξ := by positivity
  -- Step 1: `ℛ` on S-heavy sequences of `Ω⁽ˢ⁺¹⁾`.
  have hr : ∀ d₁ ∈ Omega Ω₀ (s + 1), SH d₁ →
      ∀ a b, Close (opR p y a b d₁) (opR p' y' a b d₁) (20 * μ₀ * ξ) := by
    intro d₁ hd₁ hSH a b
    have hQ : Q0 1 d₁ ⊆ Omega Ω₀ s := Q0_subset_Omega hd₁
    exact (lemma_2_8_explicit d₁ (hΩ _ (Omega_subset _ _ hd₁)) hξ hμ₀ hμ₁ (by linarith) p p' y y'
      (opR p y) (opR p' y')).1 hSH (hPi'.mono hQ)
      (fun d' hd' c w h hch => hχ.2 d' (hQ hd') hd'.1 c w h hch) a b
  -- Step 2: `𝒫` on balanced sequences of `Ω⁽ˢ⁺²⁾`.
  have hP : ∀ d₂ ∈ Omega Ω₀ (s + 2), Bal d₂ → ∀ a v,
      Close (opP p (opR p y) a v d₂) (opP p' (opR p' y') a v d₂) (400 * μ₀ * ξ) := by
    intro d₂ hd₂ hbal a v
    have hQ0 : Q0 2 d₂ ⊆ Omega Ω₀ s := Q0_subset_Omega hd₂
    have hQ1 : Q1 1 d₂ ⊆ Omega Ω₀ (s + 1) := Q1_subset_Omega hd₂
    have := (lemma_2_8_explicit d₂ (hΩ _ (Omega_subset _ _ hd₂)) (ξ := 20 * ξ) (by positivity)
      hμ₀ hμ₁ (by linarith) p p' y y' (opR p y) (opR p' y')).2.1 hbal (hPi'.mono hQ0) a v
      (fun d' hd' c => opR_nonneg hPi' hμ₀.le hμ₁ hd'.1 (hΩ _ (Omega_subset _ _ (hQ1 hd')))
        (Q0_subset_Omega (hQ1 hd')) c a)
      (fun d' hd' c => (hχ.1 d' (hQ0 hd') hd'.1 c v).mono (by linarith))
      (fun d' hd' c => (hr d' (hQ1 hd') hd'.1 c a).mono (le_of_eq (by ring)))
    exact this.mono (le_of_eq (by ring))
  -- Step 3: `𝒴` on balanced sequences of `Ω⁽ˢ⁺⁴⁾`.
  refine ⟨fun d hd hbal c w => (hP d (Omega_mono (by omega) hd) hbal c w).mono
    (by linarith), fun d₃ hd₃ hbal a v b hab => ?_⟩
  have hQ0 : Q0 2 d₃ ⊆ Omega Ω₀ (s + 2) := Q0_subset_Omega hd₃
  have := (lemma_2_8_explicit d₃ (hΩ _ (Omega_subset _ _ hd₃)) (ξ := 400 * ξ) (by positivity)
    hμ₀ hμ₁ (by linarith) (opP p (opR p y)) (opP p' (opR p' y')) y y' (opR p y)
    (opR p' y')).2.2 hbal (hPi''.mono hQ0) a v b hab
    (fun d' hd' c => (hP d' (hQ0 hd') hd'.1 c v).mono (le_of_eq (by ring)))
    (fun d' hd' c w h hch =>
      (hχ.2 d' (Omega_mono (by omega) (hQ0 hd')) hd'.1 c w h hch).mono (by linarith))
  exact this.mono (le_of_eq (by ring))

end LW.Bip
