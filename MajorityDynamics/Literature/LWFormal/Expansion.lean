import Mathlib.Tactic

set_option autoImplicit true

/-!
# Graded expansions with explicit remainders

`Valid η z x c b` says `x = ∑_{k<4} ∑_{j≤k} c k j z^j + O(η⁴)`, where the piece `c k j`
(weighted degree `k`, of which `j` comes from the summation variable `z`, `|z| ≤ η`) has size
`≤ b.B k j * η^(k-j)` and the remainder is `≤ b.R * η⁴`, valid for `0 < η ≤ b.η₀`.
This is the bookkeeping behind the Lemma 7.1 computation.
-/

open Finset

namespace LW.TM

/-- Pieces `c k j`. -/
abbrev Pc := ℕ → ℕ → ℝ

/-- Bounds: piece bounds `B k j`, remainder constant `R`, validity threshold `η₀`. -/
structure Bd where
  B : ℕ → ℕ → ℝ
  R : ℝ
  η₀ : ℝ

/-- Grade-`k` part `∑_{j≤k} c k j z^j`. -/
def grade (c : Pc) (z : ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), c k j * z ^ j

def val (c : Pc) (z : ℝ) : ℝ := ∑ k ∈ range 4, grade c z k

/-- `∑_{j≤k} B k j`. -/
def Bd.S (b : Bd) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), b.B k j

def Bd.all (b : Bd) : ℝ := ∑ k ∈ range 4, b.S k

def Valid (η z x : ℝ) (c : Pc) (b : Bd) : Prop :=
  (∀ k j, 0 ≤ b.B k j) ∧ 0 ≤ b.R ∧ 0 < b.η₀ ∧ b.η₀ ≤ 1 ∧
  (0 < η → η ≤ b.η₀ → |z| ≤ η →
    (∀ k < 4, ∀ j ≤ k, |c k j| ≤ b.B k j * η ^ (k - j)) ∧ |x - val c z| ≤ b.R * η ^ 4)

variable {η z x y : ℝ} {c d : Pc} {b b' : Bd}

theorem Valid.B_nonneg (h : Valid η z x c b) (k j : ℕ) : 0 ≤ b.B k j := h.1 k j
theorem Valid.R_nonneg (h : Valid η z x c b) : 0 ≤ b.R := h.2.1
theorem Valid.η₀_pos (h : Valid η z x c b) : 0 < b.η₀ := h.2.2.1
theorem Valid.η₀_le (h : Valid η z x c b) : b.η₀ ≤ 1 := h.2.2.2.1
theorem Valid.S_nonneg (h : Valid η z x c b) (k : ℕ) : 0 ≤ b.S k :=
  sum_nonneg fun j _ => h.B_nonneg k j
theorem Valid.all_nonneg (h : Valid η z x c b) : 0 ≤ b.all := sum_nonneg fun k _ => h.S_nonneg k

section bounds
variable (h : Valid η z x c b) (hη : 0 < η) (hη₀ : η ≤ b.η₀) (hz : |z| ≤ η)
include h hη hη₀ hz

theorem Valid.piece {k j : ℕ} (hk : k < 4) (hj : j ≤ k) : |c k j| ≤ b.B k j * η ^ (k - j) :=
  (h.2.2.2.2 hη hη₀ hz).1 k hk j hj

theorem Valid.rem : |x - val c z| ≤ b.R * η ^ 4 := (h.2.2.2.2 hη hη₀ hz).2

omit hη hz in
theorem Valid.η_le_one : η ≤ 1 := hη₀.trans h.η₀_le

theorem Valid.grade_le {k : ℕ} (hk : k < 4) : |grade c z k| ≤ b.S k * η ^ k := by
  unfold grade Bd.S
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
  rw [abs_mul, abs_pow]
  calc |c k j| * |z| ^ j ≤ b.B k j * η ^ (k - j) * η ^ j :=
        mul_le_mul (h.piece hη hη₀ hz hk hj) (pow_le_pow_left₀ (abs_nonneg _) hz j)
          (by positivity) (mul_nonneg (h.B_nonneg k j) (by positivity))
    _ = b.B k j * η ^ k := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj]

theorem Valid.val_le : |val c z| ≤ b.all := by
  unfold val Bd.all
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  refine (h.grade_le hη hη₀ hz (mem_range.1 hk)).trans ?_
  have := h.S_nonneg k
  have : η ^ k ≤ 1 := pow_le_one₀ hη.le (h.η_le_one hη₀)
  nlinarith

theorem Valid.abs_le : |x| ≤ b.all + b.R := by
  have h1 := h.rem hη hη₀ hz
  have h2 := h.val_le hη hη₀ hz
  have : η ^ 4 ≤ 1 := pow_le_one₀ hη.le (h.η_le_one hη₀)
  have := h.R_nonneg
  calc |x| = |(x - val c z) + val c z| := by ring_nf
    _ ≤ |x - val c z| + |val c z| := abs_add_le _ _
    _ ≤ b.all + b.R := by nlinarith

end bounds

/-! ### Elementary constructors -/

/-- Pieces with a single entry. -/
def Pc.single (g j : ℕ) (a : ℝ) : Pc := fun k l => if k = g ∧ l = j then a else 0

def Bd.single (g j : ℕ) (A : ℝ) : Bd := ⟨fun k l => if k = g ∧ l = j then A else 0, 0, 1⟩

theorem grade_single {g j : ℕ} {a : ℝ} (hj : j ≤ g) (k : ℕ) :
    grade (Pc.single g j a) z k = if k = g then a * z ^ j else 0 := by
  unfold grade Pc.single
  split_ifs with hk
  · subst hk
    rw [sum_eq_single j (fun l _ hl => by simp [hl]) (fun h => absurd (mem_range.2 (by omega)) h)]
    simp
  · exact sum_eq_zero fun l _ => by simp [hk]

theorem val_single {g j : ℕ} {a : ℝ} (hg : g < 4) (hj : j ≤ g) :
    val (Pc.single g j a) z = a * z ^ j := by
  unfold val
  simp_rw [grade_single hj]
  rw [sum_ite_eq' (range 4) g]
  simp [hg]

theorem Valid.single {g j : ℕ} (hg : g < 4) (hj : j ≤ g) {a A : ℝ} (hA : 0 ≤ A)
    (ha : |a| ≤ A * η ^ (g - j)) :
    Valid η z (a * z ^ j) (Pc.single g j a) (Bd.single g j A) := by
  refine ⟨fun k l => ?_, le_rfl, one_pos, le_rfl, fun _ _ _ => ⟨fun k _ l _ => ?_, ?_⟩⟩
  · unfold Bd.single; dsimp only; split_ifs <;> simp [hA]
  · unfold Pc.single Bd.single; dsimp only
    split_ifs with hkl
    · obtain ⟨rfl, rfl⟩ := hkl; exact ha
    · simp
  · rw [val_single hg hj]; simp [Bd.single]

theorem Valid.const {a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) :
    Valid η z a (Pc.single 0 0 a) (Bd.single 0 0 A) := by
  simpa using Valid.single (η := η) (z := z) (by norm_num : 0 < 4) le_rfl hA (by simpa using ha)

/-- A `z`-free leaf of weighted degree `g`. -/
theorem Valid.leaf (g : ℕ) (hg : g < 4) {a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A * η ^ g) :
    Valid η z a (Pc.single g 0 a) (Bd.single g 0 A) := by
  simpa using Valid.single (η := η) (z := z) hg (Nat.zero_le g) hA (by simpa using ha)

/-- The variable `z` itself. -/
theorem Valid.var : Valid η z z (Pc.single 1 1 1) (Bd.single 1 1 1) := by
  simpa using Valid.single (η := η) (z := z) (a := 1) (by norm_num : 1 < 4) le_rfl zero_le_one
    (by simp)

/-- A quantity that is entirely remainder. -/
theorem Valid.small {R : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R * η ^ 4) :
    Valid η z x (fun _ _ => 0) ⟨fun _ _ => 0, R, 1⟩ := by
  refine ⟨fun _ _ => le_rfl, hR, one_pos, le_rfl, fun _ _ _ => ⟨fun _ _ _ _ => by simp, ?_⟩⟩
  simpa [val, grade] using hx

/-! ### Linear operations -/

def Pc.add (c d : Pc) : Pc := fun k j => c k j + d k j
def Pc.neg (c : Pc) : Pc := fun k j => -c k j
def Pc.smul (a : ℝ) (c : Pc) : Pc := fun k j => a * c k j

def Bd.add (b b' : Bd) : Bd := ⟨fun k j => b.B k j + b'.B k j, b.R + b'.R, min b.η₀ b'.η₀⟩
def Bd.smul (A : ℝ) (b : Bd) : Bd := ⟨fun k j => A * b.B k j, A * b.R, b.η₀⟩

theorem grade_add (c d : Pc) (z : ℝ) (k : ℕ) :
    grade (Pc.add c d) z k = grade c z k + grade d z k := by
  simp [grade, Pc.add, add_mul, sum_add_distrib]

theorem val_add (c d : Pc) (z : ℝ) : val (Pc.add c d) z = val c z + val d z := by
  simp [val, grade_add, sum_add_distrib]

theorem grade_neg (c : Pc) (z : ℝ) (k : ℕ) : grade (Pc.neg c) z k = -grade c z k := by
  simp [grade, Pc.neg, sum_neg_distrib]

theorem val_neg (c : Pc) (z : ℝ) : val (Pc.neg c) z = -val c z := by
  simp [val, grade_neg, sum_neg_distrib]

theorem grade_smul (a : ℝ) (c : Pc) (z : ℝ) (k : ℕ) :
    grade (Pc.smul a c) z k = a * grade c z k := by
  simp [grade, Pc.smul, mul_sum, mul_assoc]

theorem val_smul (a : ℝ) (c : Pc) (z : ℝ) : val (Pc.smul a c) z = a * val c z := by
  simp [val, grade_smul, mul_sum]

theorem Valid.add (hx : Valid η z x c b) (hy : Valid η z y d b') :
    Valid η z (x + y) (Pc.add c d) (Bd.add b b') := by
  refine ⟨fun k j => add_nonneg (hx.B_nonneg k j) (hy.B_nonneg k j),
    add_nonneg hx.R_nonneg hy.R_nonneg, lt_min hx.η₀_pos hy.η₀_pos,
    (min_le_left _ _).trans hx.η₀_le, fun hη hη₀ hz => ?_⟩
  have h1 := hx.2.2.2.2 hη ((le_min_iff.1 hη₀).1) hz
  have h2 := hy.2.2.2.2 hη ((le_min_iff.1 hη₀).2) hz
  refine ⟨fun k hk j hj => ?_, ?_⟩
  · simp only [Pc.add, Bd.add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (h1.1 k hk j hj) (h2.1 k hk j hj))
  · rw [val_add]
    calc |x + y - (val c z + val d z)| = |(x - val c z) + (y - val d z)| := by ring_nf
      _ ≤ |x - val c z| + |y - val d z| := abs_add_le _ _
      _ ≤ (Bd.add b b').R * η ^ 4 := by simp only [Bd.add, add_mul]; exact add_le_add h1.2 h2.2

theorem Valid.neg (hx : Valid η z x c b) : Valid η z (-x) (Pc.neg c) b := by
  refine ⟨hx.B_nonneg, hx.R_nonneg, hx.η₀_pos, hx.η₀_le, fun hη hη₀ hz => ?_⟩
  have h1 := hx.2.2.2.2 hη hη₀ hz
  refine ⟨fun k hk j hj => by simpa [Pc.neg] using h1.1 k hk j hj, ?_⟩
  rw [val_neg, ← abs_neg]; convert h1.2 using 2; ring

theorem Valid.sub (hx : Valid η z x c b) (hy : Valid η z y d b') :
    Valid η z (x - y) (Pc.add c (Pc.neg d)) (Bd.add b b') :=
  sub_eq_add_neg x y ▸ hx.add hy.neg

theorem Valid.smul (hx : Valid η z x c b) {a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) :
    Valid η z (a * x) (Pc.smul a c) (Bd.smul A b) := by
  refine ⟨fun k j => mul_nonneg hA (hx.B_nonneg k j), mul_nonneg hA hx.R_nonneg, hx.η₀_pos,
    hx.η₀_le, fun hη hη₀ hz => ?_⟩
  have h1 := hx.2.2.2.2 hη hη₀ hz
  refine ⟨fun k hk j hj => ?_, ?_⟩
  · simp only [Pc.smul, Bd.smul, abs_mul, mul_assoc]
    exact mul_le_mul ha (h1.1 k hk j hj) (abs_nonneg _) hA
  · rw [val_smul, ← mul_sub, abs_mul]
    simp only [Bd.smul, mul_assoc]
    exact mul_le_mul ha h1.2 (abs_nonneg _) hA

/-- Replace the pieces by equal ones (used to normalise pieces to explicit closed forms). -/
theorem Valid.congr (hx : Valid η z x c b) (hc : ∀ k < 4, ∀ j ≤ k, c k j = d k j) :
    Valid η z x d b := by
  refine ⟨hx.B_nonneg, hx.R_nonneg, hx.η₀_pos, hx.η₀_le, fun hη hη₀ hz => ?_⟩
  have h1 := hx.2.2.2.2 hη hη₀ hz
  refine ⟨fun k hk j hj => hc k hk j hj ▸ h1.1 k hk j hj, ?_⟩
  have : val d z = val c z := by
    unfold val grade
    refine sum_congr rfl fun k hk => sum_congr rfl fun j hj => ?_
    rw [hc k (mem_range.1 hk) j (Nat.lt_succ_iff.1 (mem_range.1 hj))]
  rw [this]; exact h1.2

theorem Valid.congr_val (hx : Valid η z x c b) (hxy : x = y) : Valid η z y c b := hxy ▸ hx

/-- Weaken bounds. -/
theorem Valid.weaken (hx : Valid η z x c b) (hB : ∀ k j, b.B k j ≤ b'.B k j) (hR : b.R ≤ b'.R)
    (hη : 0 < b'.η₀) (hη' : b'.η₀ ≤ b.η₀) : Valid η z x c b' := by
  refine ⟨fun k j => (hx.B_nonneg k j).trans (hB k j), hx.R_nonneg.trans hR, hη,
    hη'.trans hx.η₀_le, fun hη hη₀ hz => ?_⟩
  have h1 := hx.2.2.2.2 hη (hη₀.trans hη') hz
  refine ⟨fun k hk j hj => (h1.1 k hk j hj).trans (by gcongr; exact hB k j), h1.2.trans ?_⟩
  gcongr

/-- Add an `O(η⁴)` quantity to a valid expansion. -/
theorem Valid.add_small (hx : Valid η z x c b) {r R : ℝ} (hR : 0 ≤ R) (hr : |r| ≤ R * η ^ 4) :
    Valid η z (x + r) c ⟨b.B, b.R + R, b.η₀⟩ := by
  refine ⟨hx.B_nonneg, add_nonneg hx.R_nonneg hR, hx.η₀_pos, hx.η₀_le, fun hη hη₀ hz => ?_⟩
  have h1 := hx.2.2.2.2 hη hη₀ hz
  refine ⟨h1.1, ?_⟩
  calc |x + r - val c z| = |(x - val c z) + r| := by ring_nf
    _ ≤ |x - val c z| + |r| := abs_add_le _ _
    _ ≤ (b.R + R) * η ^ 4 := by rw [add_mul]; exact add_le_add h1.2 hr

/-! ### Products -/

def Pc.mul (c d : Pc) : Pc := fun k j =>
  if k < 4 then
    ∑ i ∈ range (k + 1), ∑ l ∈ range (j + 1),
      if l ≤ i ∧ j - l ≤ k - i then c i l * d (k - i) (j - l) else 0
  else 0

def Bd.mul (b b' : Bd) : Bd :=
  ⟨fun k j => ∑ i ∈ range (k + 1), ∑ l ∈ range (j + 1),
      if l ≤ i ∧ j - l ≤ k - i then b.B i l * b'.B (k - i) (j - l) else 0,
    (∑ i ∈ range 4, ∑ i' ∈ range 4, if 4 ≤ i + i' then b.S i * b'.S i' else 0)
      + b.all * b'.R + b.R * b'.all + b.R * b'.R,
    min b.η₀ b'.η₀⟩

theorem val_mul (c d : Pc) (z : ℝ) :
    val (Pc.mul c d) z = ∑ k ∈ range 4, ∑ i ∈ range (k + 1), grade c z i * grade d z (k - i) := by
  simp only [val, grade, Pc.mul, sum_range_succ, sum_range_zero]
  norm_num
  ring

theorem mul_sub_val_mul (c d : Pc) (z x y : ℝ) :
    x * y - val (Pc.mul c d) z =
      (∑ i ∈ range 4, ∑ i' ∈ range 4, if 4 ≤ i + i' then grade c z i * grade d z i' else 0)
        + val c z * (y - val d z) + (x - val c z) * val d z
        + (x - val c z) * (y - val d z) := by
  rw [val_mul]
  simp only [val, sum_range_succ, sum_range_zero]
  norm_num
  ring

theorem Valid.mul (hx : Valid η z x c b) (hy : Valid η z y d b') :
    Valid η z (x * y) (Pc.mul c d) (Bd.mul b b') := by
  have hS := hx.S_nonneg; have hS' := hy.S_nonneg
  have hA := hx.all_nonneg; have hA' := hy.all_nonneg
  have hR := hx.R_nonneg; have hR' := hy.R_nonneg
  refine ⟨fun k j => ?_, ?_, lt_min hx.η₀_pos hy.η₀_pos, (min_le_left _ _).trans hx.η₀_le,
    fun hη hη₀ hz => ?_⟩
  · simp only [Bd.mul]
    exact sum_nonneg fun i _ => sum_nonneg fun l _ => by
      split_ifs <;> [exact mul_nonneg (hx.B_nonneg _ _) (hy.B_nonneg _ _); exact le_rfl]
  · simp only [Bd.mul]
    have : 0 ≤ ∑ i ∈ range 4, ∑ i' ∈ range 4, if 4 ≤ i + i' then b.S i * b'.S i' else 0 :=
      sum_nonneg fun i _ => sum_nonneg fun i' _ => by
        split_ifs <;> [exact mul_nonneg (hS i) (hS' i'); exact le_rfl]
    positivity
  have hη₁ : η ≤ b.η₀ := (le_min_iff.1 hη₀).1
  have hη₂ : η ≤ b'.η₀ := (le_min_iff.1 hη₀).2
  have hη1 : η ≤ 1 := hx.η_le_one hη₁
  refine ⟨fun k hk j hj => ?_, ?_⟩
  · simp only [Pc.mul, Bd.mul, sum_mul, if_pos hk]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
    have hi := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hl := Nat.lt_succ_iff.1 (mem_range.1 hl)
    split_ifs with hc
    · rw [abs_mul]
      have e : η ^ (k - j) = η ^ (i - l) * η ^ (k - i - (j - l)) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      calc |c i l| * |d (k - i) (j - l)|
          ≤ b.B i l * η ^ (i - l) * (b'.B (k - i) (j - l) * η ^ (k - i - (j - l))) :=
            mul_le_mul (hx.piece hη hη₁ hz (by omega) hc.1) (hy.piece hη hη₂ hz (by omega) hc.2)
              (abs_nonneg _) (mul_nonneg (hx.B_nonneg _ _) (by positivity))
        _ = _ := by ring
    · simp
  · rw [mul_sub_val_mul]
    have h1 := hx.rem hη hη₁ hz
    have h2 := hy.rem hη hη₂ hz
    have h3 := hx.val_le hη hη₁ hz
    have h4 := hy.val_le hη hη₂ hz
    have hη4 : 0 ≤ η ^ 4 := by positivity
    have hη8 : η ^ 4 * η ^ 4 ≤ η ^ 4 := by
      have : η ^ 4 ≤ 1 := pow_le_one₀ hη.le hη1
      nlinarith
    have hsum : |∑ i ∈ range 4, ∑ i' ∈ range 4,
        if 4 ≤ i + i' then grade c z i * grade d z i' else 0| ≤
        (∑ i ∈ range 4, ∑ i' ∈ range 4, if 4 ≤ i + i' then b.S i * b'.S i' else 0) * η ^ 4 := by
      rw [sum_mul]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
      rw [sum_mul]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i' hi' => ?_)
      split_ifs with hii
      · rw [abs_mul]
        calc |grade c z i| * |grade d z i'| ≤ b.S i * η ^ i * (b'.S i' * η ^ i') :=
              mul_le_mul (hx.grade_le hη hη₁ hz (mem_range.1 hi))
                (hy.grade_le hη hη₂ hz (mem_range.1 hi')) (abs_nonneg _)
                (mul_nonneg (hS i) (by positivity))
          _ = b.S i * b'.S i' * η ^ (i + i') := by rw [pow_add]; ring
          _ ≤ b.S i * b'.S i' * η ^ 4 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1 hii)
                (mul_nonneg (hS i) (hS' i'))
      · simp
    simp only [Bd.mul]
    calc _ ≤ |∑ i ∈ range 4, ∑ i' ∈ range 4, if 4 ≤ i + i' then grade c z i * grade d z i' else 0|
          + |val c z * (y - val d z)| + |(x - val c z) * val d z|
          + |(x - val c z) * (y - val d z)| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
          simp only [abs_mul]
          have e1 : |val c z| * |y - val d z| ≤ b.all * (b'.R * η ^ 4) :=
            mul_le_mul h3 h2 (abs_nonneg _) hA
          have e2 : |x - val c z| * |val d z| ≤ b.R * η ^ 4 * b'.all :=
            mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
          have e3 : |x - val c z| * |y - val d z| ≤ b.R * η ^ 4 * (b'.R * η ^ 4) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          have e4 : b.R * η ^ 4 * (b'.R * η ^ 4) ≤ b.R * b'.R * η ^ 4 := by
            have := mul_le_mul_of_nonneg_left hη8 (mul_nonneg hR hR')
            linarith [this]
          nlinarith [hsum]

/-! ### Inverses -/

/-- Pieces of `x - c 0 0`. -/
def Pc.tail (c : Pc) : Pc := fun k j => if k = 0 then 0 else c k j
def Bd.tail (b : Bd) : Bd := ⟨fun k j => if k = 0 then 0 else b.B k j, b.R, b.η₀⟩

theorem grade_zero (c : Pc) (z : ℝ) : grade c z 0 = c 0 0 := by simp [grade]

theorem val_tail (c : Pc) (z : ℝ) : val (Pc.tail c) z = val c z - c 0 0 := by
  simp [val, grade, Pc.tail, sum_range_succ]; ring

theorem Valid.tail (hx : Valid η z x c b) : Valid η z (x - c 0 0) (Pc.tail c) (Bd.tail b) := by
  refine ⟨fun k j => ?_, hx.R_nonneg, hx.η₀_pos, hx.η₀_le, fun hη hη₀ hz => ?_⟩
  · simp only [Bd.tail]; split_ifs <;> simp [hx.B_nonneg]
  have h1 := hx.2.2.2.2 hη hη₀ hz
  refine ⟨fun k hk j hj => ?_, ?_⟩
  · simp only [Pc.tail, Bd.tail]
    split_ifs
    · simp
    · exact h1.1 k hk j hj
  · rw [val_tail]; simp only [Bd.tail]; convert h1.2 using 2; ring

/-- `1 - W + W² - W³`. -/
def Pc.geom (W : Pc) : Pc :=
  Pc.add (Pc.add (Pc.single 0 0 1) (Pc.neg W))
    (Pc.add (Pc.mul W W) (Pc.neg (Pc.mul (Pc.mul W W) W)))

def Bd.geom (bW : Bd) : Bd :=
  Bd.add (Bd.add (Bd.single 0 0 1) bW) (Bd.add (Bd.mul bW bW) (Bd.mul (Bd.mul bW bW) bW))

theorem Valid.geom {w : ℝ} {W : Pc} {bW : Bd} (hw : Valid η z w W bW) :
    Valid η z (1 - w + w * w - w * w * w) (Pc.geom W) (Bd.geom bW) :=
  (((Valid.const zero_le_one (by simp)).add hw.neg).add
    ((hw.mul hw).add ((hw.mul hw).mul hw).neg)).congr_val (by ring)

noncomputable def Pc.inv (c : Pc) : Pc := Pc.smul (1 / c 0 0) (Pc.geom (Pc.smul (1 / c 0 0) (Pc.tail c)))

noncomputable def Bd.inv (b : Bd) (L : ℝ) : Bd :=
  ⟨(Bd.smul (1 / L) (Bd.geom (Bd.smul (1 / L) (Bd.tail b)))).B,
    (Bd.smul (1 / L) (Bd.geom (Bd.smul (1 / L) (Bd.tail b)))).R
      + 2 * ((b.all + b.R) / L) ^ 4 / L,
    min (Bd.geom (Bd.smul (1 / L) (Bd.tail b))).η₀ (L / (2 * (b.all + b.R + 1)))⟩

/-- `|x - c 0 0| ≤ (all + R) η`. -/
theorem Valid.tail_le (hx : Valid η z x c b) (hη : 0 < η) (hη₀ : η ≤ b.η₀) (hz : |z| ≤ η) :
    |x - c 0 0| ≤ (b.all + b.R) * η := by
  have hη1 := hx.η_le_one hη₀
  have h1 := hx.rem hη hη₀ hz
  have g1 := hx.grade_le hη hη₀ hz (show 1 < 4 by norm_num)
  have g2 := hx.grade_le hη hη₀ hz (show 2 < 4 by norm_num)
  have g3 := hx.grade_le hη hη₀ hz (show 3 < 4 by norm_num)
  have hS := hx.S_nonneg
  have hv : val c z = c 0 0 + grade c z 1 + grade c z 2 + grade c z 3 := by
    simp [val, sum_range_succ, grade_zero]
  have hall : b.all = b.S 0 + b.S 1 + b.S 2 + b.S 3 := by simp [Bd.all, sum_range_succ]
  have e2 : η ^ 2 ≤ η := by nlinarith
  have e3 : η ^ 3 ≤ η := by nlinarith
  have e4 : η ^ 4 ≤ η := by nlinarith
  calc |x - c 0 0| = |(x - val c z) + grade c z 1 + grade c z 2 + grade c z 3| := by
        rw [hv]; ring_nf
    _ ≤ |x - val c z| + |grade c z 1| + |grade c z 2| + |grade c z 3| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (b.all + b.R) * η := by
        rw [hall]
        have := hS 0; have := hS 1; have := hS 2; have := hS 3; have := hx.R_nonneg
        nlinarith [mul_le_mul_of_nonneg_left e2 (hS 2), mul_le_mul_of_nonneg_left e3 (hS 3),
          mul_le_mul_of_nonneg_left e4 hx.R_nonneg]

theorem Valid.inv (hx : Valid η z x c b) {L : ℝ} (hL : 0 < L) (hc : L ≤ |c 0 0|) :
    Valid η z x⁻¹ (Pc.inv c) (Bd.inv b L) := by
  have hc0 : c 0 0 ≠ 0 := fun h => by rw [h, abs_zero] at hc; linarith
  have hinv : |1 / c 0 0| ≤ 1 / L := by
    rw [abs_div, abs_one]; exact one_div_le_one_div_of_le hL hc
  have hL' : (0 : ℝ) ≤ 1 / L := by positivity
  have hQ := (hx.tail.smul hL' hinv).geom.smul hL' hinv
  have hAR : 0 ≤ b.all + b.R := add_nonneg hx.all_nonneg hx.R_nonneg
  refine ⟨hQ.B_nonneg, ?_, lt_min hQ.η₀_pos (by positivity), (min_le_left _ _).trans hQ.η₀_le,
    fun hη hη₀ hz => ?_⟩
  · simp only [Bd.inv]
    have := hQ.R_nonneg
    positivity
  have hη₁ : η ≤ (Bd.geom (Bd.smul (1 / L) (Bd.tail b))).η₀ := (le_min_iff.1 hη₀).1
  have hη₂ : η ≤ L / (2 * (b.all + b.R + 1)) := (le_min_iff.1 hη₀).2
  have hη₃ : η ≤ b.η₀ := by
    refine hη₁.trans ?_
    simp [Bd.geom, Bd.add, Bd.mul, Bd.single, Bd.smul, Bd.tail]
  have h1 := hQ.2.2.2.2 hη hη₁ hz
  refine ⟨h1.1, ?_⟩
  set w := 1 / c 0 0 * (x - c 0 0) with hw
  have hu := hx.tail_le hη hη₃ hz
  have hwle : |w| ≤ (b.all + b.R) / L * η := by
    rw [hw, abs_mul]
    calc |1 / c 0 0| * |x - c 0 0| ≤ 1 / L * ((b.all + b.R) * η) :=
          mul_le_mul hinv hu (abs_nonneg _) hL'
      _ = _ := by ring
  have hwhalf : |w| ≤ 1 / 2 := by
    refine hwle.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    have : (b.all + b.R) * η ≤ (b.all + b.R) * (L / (2 * (b.all + b.R + 1))) :=
      mul_le_mul_of_nonneg_left hη₂ hAR
    have : (b.all + b.R) * (L / (2 * (b.all + b.R + 1))) ≤ 1 / 2 * L := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have h1w : 1 / 2 ≤ 1 + w := by linarith [(_root_.abs_le.1 hwhalf).1]
  have hxw : x = c 0 0 * (1 + w) := by rw [hw]; field_simp; ring
  have hx0 : x ≠ 0 := by rw [hxw]; exact mul_ne_zero hc0 (by linarith)
  have hid : x⁻¹ = 1 / c 0 0 * (1 - w + w * w - w * w * w) + 1 / c 0 0 * (w ^ 4 / (1 + w)) := by
    rw [hxw]; field_simp; ring
  have hr : |1 / c 0 0 * (w ^ 4 / (1 + w))| ≤ 2 * ((b.all + b.R) / L) ^ 4 / L * η ^ 4 := by
    rw [abs_mul, abs_div (w ^ 4), abs_of_pos (by linarith : 0 < 1 + w), abs_pow]
    have hw4 : |w| ^ 4 ≤ ((b.all + b.R) / L * η) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hwle 4
    have : |w| ^ 4 / (1 + w) ≤ 2 * ((b.all + b.R) / L * η) ^ 4 := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ ((b.all + b.R) / L * η) ^ 4 := by positivity
      nlinarith
    calc |1 / c 0 0| * (|w| ^ 4 / (1 + w)) ≤ 1 / L * (2 * ((b.all + b.R) / L * η) ^ 4) :=
          mul_le_mul hinv this (by positivity) hL'
      _ = _ := by ring
  rw [hid]
  calc |1 / c 0 0 * (1 - w + w * w - w * w * w) + 1 / c 0 0 * (w ^ 4 / (1 + w)) - val (Pc.inv c) z|
      = |(1 / c 0 0 * (1 - w + w * w - w * w * w) - val (Pc.inv c) z)
          + 1 / c 0 0 * (w ^ 4 / (1 + w))| := by ring_nf
    _ ≤ |1 / c 0 0 * (1 - w + w * w - w * w * w) - val (Pc.inv c) z|
          + |1 / c 0 0 * (w ^ 4 / (1 + w))| := abs_add_le _ _
    _ ≤ (Bd.inv b L).R * η ^ 4 := by
        simp only [Bd.inv, add_mul]
        exact add_le_add h1.2 hr

/-! ### Finite sums and averaging over the summation variable -/

def Pc.sumOver {ι : Type*} (s : Finset ι) (cf : ι → Pc) : Pc := fun k j => ∑ i ∈ s, cf i k j

def Bd.sumOver {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (bf : ι → Bd) : Bd :=
  ⟨fun k j => ∑ i ∈ s, (bf i).B k j, ∑ i ∈ s, (bf i).R, s.inf' hs fun i => (bf i).η₀⟩

theorem val_sumOver {ι : Type*} (s : Finset ι) (cf : ι → Pc) (z : ℝ) :
    val (Pc.sumOver s cf) z = ∑ i ∈ s, val (cf i) z := by
  simp only [val, grade, Pc.sumOver, sum_mul]
  rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]

theorem Valid.sumOver {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℝ} {cf : ι → Pc}
    {bf : ι → Bd} (h : ∀ i ∈ s, Valid η z (f i) (cf i) (bf i)) :
    Valid η z (∑ i ∈ s, f i) (Pc.sumOver s cf) (Bd.sumOver s hs bf) := by
  obtain ⟨i₀, hi₀⟩ := id hs
  refine ⟨fun k j => sum_nonneg fun i hi => (h i hi).B_nonneg k j,
    sum_nonneg fun i hi => (h i hi).R_nonneg, ?_, ?_, fun hη hη₀ hz => ?_⟩
  · exact (lt_inf'_iff hs).2 fun i hi => (h i hi).η₀_pos
  · exact (inf'_le _ hi₀).trans (h i₀ hi₀).η₀_le
  have hη' : ∀ i ∈ s, η ≤ (bf i).η₀ := fun i hi => hη₀.trans (inf'_le _ hi)
  refine ⟨fun k hk j hj => ?_, ?_⟩
  · simp only [Pc.sumOver, Bd.sumOver, sum_mul]
    exact (abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun i hi => (h i hi).piece hη (hη' i hi) hz hk hj)
  · rw [val_sumOver, ← sum_sub_distrib]
    simp only [Bd.sumOver, sum_mul]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (h i hi).rem hη (hη' i hi) hz)

/-- A single piece whose bound is only known for `η ≤ η₀`. -/
theorem Valid.single' {g j : ℕ} (hg : g < 4) (hj : j ≤ g) {a A η₀ : ℝ} (hA : 0 ≤ A)
    (h₀ : 0 < η₀) (h₁ : η₀ ≤ 1) (ha : 0 < η → η ≤ η₀ → |a| ≤ A * η ^ (g - j)) :
    Valid η z (a * z ^ j) (Pc.single g j a)
      ⟨fun k l => if k = g ∧ l = j then A else 0, 0, η₀⟩ := by
  refine ⟨fun k l => ?_, le_rfl, h₀, h₁, fun hη hη₀ _ => ⟨fun k _ l _ => ?_, ?_⟩⟩
  · dsimp only; split_ifs <;> simp [hA]
  · unfold Pc.single; dsimp only
    split_ifs with hkl
    · obtain ⟨rfl, rfl⟩ := hkl; exact ha hη hη₀
    · simp
  · rw [val_single hg hj]; simp

/-- Pieces of `∑_{k<4} ∑_{j≤k} c k j * P j`, where `P j` has pieces `cP j`. -/
def Pc.avg (c : Pc) (cP : ℕ → Pc) : Pc :=
  Pc.sumOver (range 4) fun k => Pc.sumOver (range (k + 1)) fun j =>
    Pc.mul (Pc.single (k - j) 0 (c k j)) (cP j)

def Bd.avg (b : Bd) (bP : ℕ → Bd) : Bd :=
  let b' := Bd.sumOver (range 4) (by simp) fun k => Bd.sumOver (range (k + 1)) (by simp) fun j =>
    Bd.mul ⟨fun k' l => if k' = k - j ∧ l = 0 then b.B k j else 0, 0, b.η₀⟩ (bP j)
  ⟨b'.B, b'.R + b.R, min b'.η₀ b.η₀⟩

theorem sum_val_eq {ι : Type*} (V : Finset ι) (ε : ι → ℝ) (c : Pc) {n : ℝ} (hn : n ≠ 0)
    {P : ℕ → ℝ} (hP : ∀ j < 4, P j = (∑ v ∈ V, ε v ^ j) / n) :
    (∑ v ∈ V, val c (ε v)) / n = ∑ k ∈ range 4, ∑ j ∈ range (k + 1), c k j * P j := by
  have e : ∀ j < 4, ∑ v ∈ V, ε v ^ j = n * P j := fun j hj => by
    rw [hP j hj]; field_simp
  simp only [val, grade, sum_range_succ, sum_range_zero, zero_add, sum_add_distrib, ← mul_sum]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
  field_simp

/-- Averaging a `z`-expansion over `z = ε v`, `v ∈ V`, `|V| ≤ n`: the result has pieces
`∑_{k,j} c k j * P j` with `P j = (∑_v ε v ^ j)/n`. -/
theorem Valid.avg {ι : Type*} {V : Finset ι} (hne : V.Nonempty) {ε F : ι → ℝ}
    (hε : ∀ v ∈ V, |ε v| ≤ η) (hF : ∀ v ∈ V, Valid η (ε v) (F v) c b) {n : ℝ} (hn : 0 < n)
    (hV : (V.card : ℝ) ≤ n) {P : ℕ → ℝ} (hP : ∀ j < 4, P j = (∑ v ∈ V, ε v ^ j) / n)
    {cP : ℕ → Pc} {bP : ℕ → Bd} (hPv : ∀ j < 4, Valid η 0 (P j) (cP j) (bP j)) :
    Valid η 0 ((∑ v ∈ V, F v) / n) (Pc.avg c cP) (Bd.avg b bP) := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hb := hF v₀ hv₀
  have hsingle : ∀ k < 4, ∀ j ≤ k, Valid η 0 (c k j) (Pc.single (k - j) 0 (c k j))
      ⟨fun k' l => if k' = k - j ∧ l = 0 then b.B k j else 0, 0, b.η₀⟩ := fun k hk j hj =>
    (Valid.single' (by omega) (Nat.zero_le _) (hb.B_nonneg k j) hb.η₀_pos hb.η₀_le
      fun hη hη₀ => by simpa using hb.piece hη hη₀ (hε v₀ hv₀) hk hj).congr_val (by simp)
  have hsum := Valid.sumOver (η := η) (z := 0) (f := fun k => ∑ j ∈ range (k + 1), c k j * P j)
    (s := range 4) (by simp) fun k hk => Valid.sumOver (by simp) fun j hj =>
      (hsingle k (mem_range.1 hk) j (Nat.lt_succ_iff.1 (mem_range.1 hj))).mul
        (hPv j (by have := mem_range.1 hk; have := mem_range.1 hj; omega))
  refine ⟨hsum.B_nonneg, add_nonneg hsum.R_nonneg hb.R_nonneg, lt_min hsum.η₀_pos hb.η₀_pos,
    (min_le_left _ _).trans hsum.η₀_le, fun hη hη₀ hz => ?_⟩
  have h1 := hsum.2.2.2.2 hη (le_min_iff.1 hη₀).1 hz
  refine ⟨h1.1, ?_⟩
  have hsplit : (∑ v ∈ V, F v) / n = ∑ k ∈ range 4, ∑ j ∈ range (k + 1), c k j * P j
      + (∑ v ∈ V, (F v - val c (ε v))) / n := by
    rw [← sum_val_eq V ε c hn.ne' hP, sum_sub_distrib]; ring
  have hrem : |(∑ v ∈ V, (F v - val c (ε v))) / n| ≤ b.R * η ^ 4 := by
    rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
    calc |∑ v ∈ V, (F v - val c (ε v))| ≤ ∑ v ∈ V, |F v - val c (ε v)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ V, b.R * η ^ 4 := sum_le_sum fun v hv =>
          (hF v hv).rem hη (le_min_iff.1 hη₀).2 (hε v hv)
      _ = V.card * (b.R * η ^ 4) := by simp
      _ ≤ b.R * η ^ 4 * n := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hV (by have := hb.R_nonneg; positivity)
  rw [hsplit]
  calc _ = |(∑ k ∈ range 4, ∑ j ∈ range (k + 1), c k j * P j - val (Pc.avg c cP) 0)
        + (∑ v ∈ V, (F v - val c (ε v))) / n| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ (Bd.avg b bP).R * η ^ 4 := by
        simp only [Bd.avg, add_mul]
        exact add_le_add h1.2 hrem

/-- Four-moment form of `Valid.avg`. -/
theorem Valid.avg4 {ι : Type*} {V : Finset ι} (hne : V.Nonempty) {ε F : ι → ℝ}
    (hε : ∀ v ∈ V, |ε v| ≤ η) (hF : ∀ v ∈ V, Valid η (ε v) (F v) c b) {n : ℝ} (hn : 0 < n)
    (hV : (V.card : ℝ) ≤ n) {P₀ P₁ P₂ P₃ : ℝ}
    (h₀ : P₀ = (∑ v ∈ V, ε v ^ 0) / n) (h₁ : P₁ = (∑ v ∈ V, ε v ^ 1) / n)
    (h₂ : P₂ = (∑ v ∈ V, ε v ^ 2) / n) (h₃ : P₃ = (∑ v ∈ V, ε v ^ 3) / n)
    {c₀ c₁ c₂ c₃ : Pc} {b₀ b₁ b₂ b₃ : Bd}
    (v₀ : Valid η 0 P₀ c₀ b₀) (v₁ : Valid η 0 P₁ c₁ b₁)
    (v₂ : Valid η 0 P₂ c₂ b₂) (v₃ : Valid η 0 P₃ c₃ b₃) :
    Valid η 0 ((∑ v ∈ V, F v) / n)
      (Pc.avg c fun j => if j = 0 then c₀ else if j = 1 then c₁ else if j = 2 then c₂ else c₃)
      (Bd.avg b fun j => if j = 0 then b₀ else if j = 1 then b₁ else if j = 2 then b₂ else b₃) :=
  Valid.avg hne hε hF hn hV
    (P := fun j => if j = 0 then P₀ else if j = 1 then P₁ else if j = 2 then P₂ else P₃)
    (fun j hj => by interval_cases j <;> simp [h₀, h₁, h₂, h₃])
    (fun j hj => by interval_cases j <;> simpa)

/-- Lower bound from the constant piece: `x ≥ L/2` for small `η`. -/
theorem Valid.lower (hx : Valid η z x c b) {L : ℝ} (hL : L ≤ c 0 0) (hη : 0 < η)
    (hη₀ : η ≤ min b.η₀ (L / (2 * (b.all + b.R + 1)))) (hz : |z| ≤ η) : L / 2 ≤ x := by
  have h1 := hx.tail_le hη (hη₀.trans (min_le_left _ _)) hz
  have h2 := hη₀.trans (min_le_right _ _)
  have hA := hx.all_nonneg; have hR := hx.R_nonneg
  have hL0 : 0 < L := by
    by_contra h; push Not at h
    have : L / (2 * (b.all + b.R + 1)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  have h3 : (b.all + b.R) * η ≤ L / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (b.all + b.R + 1))] at h2
    nlinarith
  have := (_root_.abs_le.1 h1).1
  linarith

/-! ### Explicit pieces -/

/-- Explicit pieces `c k j` (`j ≤ k < 4`). -/
def Pc.mk (c00 c10 c11 c20 c21 c22 c30 c31 c32 c33 : ℝ) : Pc := fun k j =>
  if k = 0 then (if j = 0 then c00 else 0)
  else if k = 1 then (if j = 0 then c10 else if j = 1 then c11 else 0)
  else if k = 2 then (if j = 0 then c20 else if j = 1 then c21 else if j = 2 then c22 else 0)
  else if k = 3 then
    (if j = 0 then c30 else if j = 1 then c31 else if j = 2 then c32 else if j = 3 then c33 else 0)
  else 0

/-- Explicit pieces without `z`-dependence. -/
def Pc.mk0 (c0 c1 c2 c3 : ℝ) : Pc := Pc.mk c0 c1 0 c2 0 0 c3 0 0 0

/-! ### Closed forms on explicit pieces -/

section mk
variable (a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 b00 b10 b11 b20 b21 b22 b30 b31 b32 b33 : ℝ)

theorem Pc.mk_00 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 0 0 = a00 := rfl
theorem Pc.mk_10 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 1 0 = a10 := rfl
theorem Pc.mk_11 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 1 1 = a11 := rfl
theorem Pc.mk_20 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 2 0 = a20 := rfl
theorem Pc.mk_21 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 2 1 = a21 := rfl
theorem Pc.mk_22 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 2 2 = a22 := rfl
theorem Pc.mk_30 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 3 0 = a30 := rfl
theorem Pc.mk_31 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 3 1 = a31 := rfl
theorem Pc.mk_32 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 3 2 = a32 := rfl
theorem Pc.mk_33 : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 3 3 = a33 := rfl

theorem Pc.mk_of_le {k j : ℕ} (hk : 4 ≤ k) : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 k j = 0 := by
  unfold Pc.mk; split_ifs <;> first | rfl | omega

theorem Pc.mk_of_lt {k j : ℕ} (hk : k < j) : Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33 k j = 0 := by
  unfold Pc.mk; split_ifs <;> first | rfl | omega

theorem Pc.single_00 : Pc.single 0 0 a00 = Pc.mk a00 0 0 0 0 0 0 0 0 0 := by
  funext k j; unfold Pc.single Pc.mk; split_ifs <;> first | rfl | omega
theorem Pc.single_10 : Pc.single 1 0 a00 = Pc.mk 0 a00 0 0 0 0 0 0 0 0 := by
  funext k j; unfold Pc.single Pc.mk; split_ifs <;> first | rfl | omega
theorem Pc.single_11 : Pc.single 1 1 a00 = Pc.mk 0 0 a00 0 0 0 0 0 0 0 := by
  funext k j; unfold Pc.single Pc.mk; split_ifs <;> first | rfl | omega
theorem Pc.single_20 : Pc.single 2 0 a00 = Pc.mk 0 0 0 a00 0 0 0 0 0 0 := by
  funext k j; unfold Pc.single Pc.mk; split_ifs <;> first | rfl | omega
theorem Pc.single_30 : Pc.single 3 0 a00 = Pc.mk 0 0 0 0 0 0 a00 0 0 0 := by
  funext k j; unfold Pc.single Pc.mk; split_ifs <;> first | rfl | omega

theorem Pc.tail_mk : Pc.tail (Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33) = Pc.mk 0 a10 a11 a20 a21 a22 a30 a31 a32 a33 := by
  funext k j; unfold Pc.tail Pc.mk; split_ifs <;> rfl

theorem Pc.mk_add : Pc.add (Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33) (Pc.mk b00 b10 b11 b20 b21 b22 b30 b31 b32 b33) =
    Pc.mk (a00 + b00) (a10 + b10) (a11 + b11) (a20 + b20) (a21 + b21) (a22 + b22) (a30 + b30) (a31 + b31) (a32 + b32) (a33 + b33) := by
  funext k j; unfold Pc.add Pc.mk; split_ifs <;> simp

theorem Pc.mk_neg : Pc.neg (Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33) = Pc.mk (-a00) (-a10) (-a11) (-a20) (-a21) (-a22) (-a30) (-a31) (-a32) (-a33) := by
  funext k j; unfold Pc.neg Pc.mk; split_ifs <;> simp

theorem Pc.mk_smul (r : ℝ) : Pc.smul r (Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33) = Pc.mk (r * a00) (r * a10) (r * a11) (r * a20) (r * a21) (r * a22) (r * a30) (r * a31) (r * a32) (r * a33) := by
  funext k j; unfold Pc.smul Pc.mk; split_ifs <;> simp

theorem Pc.mk_mul : Pc.mul (Pc.mk a00 a10 a11 a20 a21 a22 a30 a31 a32 a33) (Pc.mk b00 b10 b11 b20 b21 b22 b30 b31 b32 b33) =
    Pc.mk (a00 * b00) (a00 * b10 + a10 * b00) (a00 * b11 + a11 * b00) (a00 * b20 + a10 * b10 + a20 * b00) (a00 * b21 + a10 * b11 + a11 * b10 + a21 * b00) (a00 * b22 + a11 * b11 + a22 * b00) (a00 * b30 + a10 * b20 + a20 * b10 + a30 * b00) (a00 * b31 + a10 * b21 + a11 * b20 + a20 * b11 + a21 * b10 + a31 * b00) (a00 * b32 + a10 * b22 + a11 * b21 + a21 * b11 + a22 * b10 + a32 * b00) (a00 * b33 + a11 * b22 + a22 * b11 + a33 * b00) := by
  funext k j
  by_cases hk : k < 4
  · by_cases hj : j ≤ k
    · interval_cases k <;> interval_cases j <;> simp [Pc.mul, Pc.mk, sum_range_succ] <;> ring
    · rw [Pc.mk_of_lt (hk := by omega)]
      simp only [Pc.mul, if_pos hk]
      refine sum_eq_zero fun i hi => sum_eq_zero fun l hl => ?_
      rw [if_neg]; simp only [mem_range] at hi hl; omega
  · rw [Pc.mk_of_le (hk := by omega)]; simp [Pc.mul, hk]

theorem Pc.sumOver_range_zero (f : ℕ → Pc) : Pc.sumOver (range 0) f = Pc.mk 0 0 0 0 0 0 0 0 0 0 := by
  funext k j; simp [Pc.sumOver, Pc.mk]

theorem Pc.sumOver_range_succ (f : ℕ → Pc) (n : ℕ) :
    Pc.sumOver (range (n + 1)) f = Pc.add (Pc.sumOver (range n) f) (f n) := by
  funext k j; simp [Pc.sumOver, Pc.add, sum_range_succ]

end mk

/-- Normalise pieces: reduce `∀ k < 4, ∀ j ≤ k, c k j = d k j` to explicit field identities, by
first collapsing the pieces into a single `Pc.mk`. -/
macro "pieces" : tactic => `(tactic|
  (simp only [Pc.inv, Pc.geom, Pc.avg, Pc.mk0, Pc.sumOver_range_succ, Pc.sumOver_range_zero,
     Pc.tail_mk, Pc.single_00, Pc.single_10, Pc.single_11, Pc.single_20, Pc.single_30,
     Pc.mk_add, Pc.mk_neg, Pc.mk_smul, Pc.mk_mul, Pc.mk_00, Pc.mk_10, Pc.mk_11, Pc.mk_20,
     Pc.mk_21, Pc.mk_22, Pc.mk_30, Pc.mk_31, Pc.mk_32, Pc.mk_33, Nat.reduceEqDiff, Nat.reduceSub,
     Nat.reduceAdd, ite_true, ite_false, mul_zero, zero_mul, add_zero, zero_add, neg_zero,
     mul_one, one_mul, sub_zero, zero_sub, ← sub_eq_add_neg]
   intro k hk j hj
   interval_cases k <;> interval_cases j <;>
   simp only [Pc.mk_00, Pc.mk_10, Pc.mk_11, Pc.mk_20, Pc.mk_21, Pc.mk_22, Pc.mk_30, Pc.mk_31,
     Pc.mk_32, Pc.mk_33] <;> (try field_simp) <;> ring_nf))

/-- If all pieces vanish, `x = O(η⁴)`. -/
theorem Valid.bound (hx : Valid η z x c b) (hc : ∀ k < 4, ∀ j ≤ k, c k j = 0) (hη : 0 < η)
    (hη₀ : η ≤ b.η₀) (hz : |z| ≤ η) : |x| ≤ b.R * η ^ 4 := by
  have h1 := hx.rem hη hη₀ hz
  have : val c z = 0 := by
    unfold val grade
    exact sum_eq_zero fun k hk => sum_eq_zero fun j hj => by
      rw [hc k (mem_range.1 hk) j (Nat.lt_succ_iff.1 (mem_range.1 hj))]; simp
  simpa [this] using h1

end LW.TM
