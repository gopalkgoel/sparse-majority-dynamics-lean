import MajorityDynamics.Literature.LWFormal.Bip.Conc
import MajorityDynamics.Literature.LWFormal.Bip.HRatioSeq
import MajorityDynamics.Literature.LWFormal.Final

set_option autoImplicit true

/-!
# The auxiliary graph on `𝔇` for the bipartite case

`𝔇` as a finset of integer sequence pairs, the two edge types (`S`-steps and `T`-steps), and the
two-phase walk: `≤ ℓ s^φ` `S`-steps followed by `≤ n t^φ` `T`-steps connect any two points.
-/

namespace LW.Bip

open Finset Real

variable {ℓ n : ℕ}

def toSeq' (x : (Fin ℓ → ℕ) × (Fin n → ℕ)) : BSeq ℓ n := toSeq x.1 x.2

theorem toSeq'_injective : Function.Injective (toSeq' (ℓ := ℓ) (n := n)) := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  simp only [toSeq', toSeq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext (funext fun a => ?_) (funext fun v => ?_)
  · have := congrFun h1 a; exact_mod_cast this
  · have := congrFun h2 v; exact_mod_cast this

@[simp] theorem toN_toSeq_fst (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : toN (toSeq s t).1 = s := by
  funext i; simp [toN, toSeq]

@[simp] theorem toN_toSeq_snd (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : toN (toSeq s t).2 = t := by
  funext i; simp [toN, toSeq]

theorem toSeq'_toN {u : BSeq ℓ n} (h1 : ∀ a, 0 ≤ u.1 a) (h2 : ∀ v, 0 ≤ u.2 v) :
    toSeq' (toN u.1, toN u.2) = u :=
  Prod.ext (toZ_toN h1) (toZ_toN h2)

theorem HB_toSeq' (m : ℕ) (x : (Fin ℓ → ℕ) × (Fin n → ℕ)) :
    HB ℓ n m (toSeq' x) = probB ℓ n m x.1 x.2 * Htilde x.1 x.2 := by
  simp only [HB, toSeq', toN_toSeq_fst, toN_toSeq_snd]

theorem Dset_swap {φ : ℝ} {m : ℕ} {d : BSeq ℓ n} :
    d.swap ∈ Dset φ n ℓ m ↔ d ∈ Dset φ ℓ n m := by
  simp only [Dset, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap]; tauto

/-- Entries of `d ∈ 𝔇` are bounded by `n` resp. `ℓ`. -/
theorem Dset_bounds {φ : ℝ} (hφ : φ ≤ 1) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B) {d : BSeq ℓ n}
    (hd : d ∈ Dset φ ℓ n m) : (∀ a, d.1 a ≤ n) ∧ ∀ v, d.2 v ≤ ℓ := by
  obtain ⟨hℓ, hn, hm, hmℓn, -, -, -, hD4, hT4, hlog⟩ := hS.bounds
  obtain ⟨-, -, -, -, hsdev, htdev⟩ := hd
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hD1 : (1 : ℝ) ≤ m / ℓ := (one_le_rpow (by linarith) (by norm_num)).trans hD4
  have hT1 : (1 : ℝ) ≤ m / n := by
    have : (1 : ℝ) ≤ log n ^ (4 : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num)]
      calc (1 : ℝ) * 16 ≤ 35000 ^ (4 : ℝ) := by
            rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
        _ ≤ log n ^ (4 : ℝ) := rpow_le_rpow (by norm_num) hlog (by norm_num)
    exact this.trans hT4
  have hDφ : (m / ℓ : ℝ) ^ φ ≤ m / ℓ := by
    have := rpow_le_rpow_of_exponent_le hD1 hφ; rwa [rpow_one] at this
  have hTφ : (m / n : ℝ) ^ φ ≤ m / n := by
    have := rpow_le_rpow_of_exponent_le hT1 hφ; rwa [rpow_one] at this
  have hDn : 2 * (m / ℓ : ℝ) ≤ n := by rw [mul_div_assoc', div_le_iff₀ hℓ0]; linarith
  have hTℓ : 2 * (m / n : ℝ) ≤ ℓ := by rw [mul_div_assoc', div_le_iff₀ hn0]; linarith
  refine ⟨fun a => ?_, fun v => ?_⟩
  · have := (abs_le.1 (hsdev a)).2
    have : (d.1 a : ℝ) ≤ n := by linarith
    exact_mod_cast this
  · have := (abs_le.1 (htdev v)).2
    have : (d.2 v : ℝ) ≤ ℓ := by linarith
    exact_mod_cast this

theorem mem_DsetB_iff {φ : ℝ} (hφ : φ ≤ 1) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {x : (Fin ℓ → ℕ) × (Fin n → ℕ)} : x ∈ DsetB φ ℓ n m ↔ InD φ ℓ n m x.1 x.2 := by
  simp only [DsetB, mem_product, mem_SprS, mem_OmS, InD]
  constructor
  · rintro ⟨⟨⟨-, h1⟩, h3⟩, ⟨⟨-, h2⟩, h4⟩⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨hb1, hb2⟩ := Dset_bounds hφ hS (toSeq_mem_Dset ⟨h1, h2, h3, h4⟩)
    simp only [toSeq, Nat.cast_le] at hb1 hb2
    exact ⟨⟨⟨hb1, h1⟩, h3⟩, ⟨⟨hb2, h2⟩, h4⟩⟩

/-- `𝔇` as a finset of integer sequence pairs. -/
noncomputable def DsetZ (φ : ℝ) (ℓ n m : ℕ) : Finset (BSeq ℓ n) := (DsetB φ ℓ n m).image toSeq'

noncomputable def WsetZ (φ : ℝ) (ℓ n m : ℕ) : Finset (BSeq ℓ n) := (WsetB φ ℓ n m).image toSeq'

def OmegaZ (ℓ n m : ℕ) : Finset (BSeq ℓ n) := (OmegaB ℓ n m).image toSeq'

theorem InD_toN {φ : ℝ} {m : ℕ} {u : BSeq ℓ n} (hu : u ∈ Dset φ ℓ n m) :
    InD φ ℓ n m (toN u.1) (toN u.2) := by
  obtain ⟨h1, h2, hM1, hM2, hsdev, htdev⟩ := hu
  refine ⟨?_, ?_, fun a => by rw [toN_cast h1]; exact hsdev a,
    fun v => by rw [toN_cast h2]; exact htdev v⟩
  · have : ∑ a, ((toN u.1 a : ℕ) : ℤ) = (m : ℤ) := by
      rw [← hM1]; exact sum_congr rfl fun a _ => Int.toNat_of_nonneg (h1 a)
    exact_mod_cast this
  · have : ∑ v, ((toN u.2 v : ℕ) : ℤ) = (m : ℤ) := by
      rw [← hM2]; exact sum_congr rfl fun v _ => Int.toNat_of_nonneg (h2 v)
    exact_mod_cast this

theorem mem_DsetZ {φ : ℝ} (hφ : φ ≤ 1) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B) {u : BSeq ℓ n} :
    u ∈ DsetZ φ ℓ n m ↔ u ∈ Dset φ ℓ n m := by
  unfold DsetZ
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact toSeq_mem_Dset ((mem_DsetB_iff hφ hS).1 hx)
  · intro hu
    exact ⟨(toN u.1, toN u.2), (mem_DsetB_iff hφ hS).2 (InD_toN hu), toSeq'_toN hu.1 hu.2.1⟩

theorem WsetZ_subset_DsetZ {φ : ℝ} {m : ℕ} : WsetZ φ ℓ n m ⊆ DsetZ φ ℓ n m :=
  image_subset_image WsetB_subset_DsetB

theorem DsetZ_subset_OmegaZ {φ : ℝ} {m : ℕ} : DsetZ φ ℓ n m ⊆ OmegaZ ℓ n m :=
  image_subset_image DsetB_subset_OmegaB

/-- `S`-adjacency: `u = d - e_a`, `v = d - e_b` for some `d` and `a, b` on the left side. -/
def AdjS (u v : BSeq ℓ n) : Prop := ∃ d a b, u = d - eS a ∧ v = d - eS b

/-- `T`-adjacency: `u = d - e_x`, `v = d - e_y` for some `d` and `x, y` on the right side. -/
def AdjT (u v : BSeq ℓ n) : Prop := ∃ d x y, u = d - eT x ∧ v = d - eT y

theorem stepS_mem_Dset {φ : ℝ} {m : ℕ} {u v : BSeq ℓ n} (hu : u ∈ Dset φ ℓ n m)
    (hv : v ∈ Dset φ ℓ n m) {a b : Fin ℓ} (ha : v.1 a < u.1 a) (hb : u.1 b < v.1 b) :
    (u.1 - e a + e b, u.2) ∈ Dset φ ℓ n m := by
  obtain ⟨hu0, hu0', huM, huM', huD, huD'⟩ := hu
  obtain ⟨hv0, -, -, -, hvD, -⟩ := hv
  have hab : a ≠ b := by rintro rfl; omega
  have hval : ∀ i, (u.1 - e a + e b) i = u.1 i ∨
      ((u.1 - e a + e b) i = u.1 i - 1 ∧ v.1 i ≤ u.1 i - 1) ∨
      ((u.1 - e a + e b) i = u.1 i + 1 ∧ u.1 i + 1 ≤ v.1 i) := by
    intro i
    simp only [Pi.add_apply, Pi.sub_apply, e_apply]
    by_cases hia : i = a
    · subst hia; right; left; simp [hab]; omega
    · by_cases hib : i = b
      · subst hib; right; right; simp [hia]; omega
      · left; simp [hia, hib]
  have hbetween : ∀ i, (u.1 i ≤ (u.1 - e a + e b) i ∧ (u.1 - e a + e b) i ≤ v.1 i) ∨
      (v.1 i ≤ (u.1 - e a + e b) i ∧ (u.1 - e a + e b) i ≤ u.1 i) := by
    intro i; rcases hval i with h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] <;> omega
  refine ⟨fun i => ?_, hu0', ?_, huM', fun i => ?_, huD'⟩
  · show 0 ≤ (u.1 - e a + e b) i
    have := hbetween i; have := hu0 i; have := hv0 i; omega
  · show M1 (u.1 - e a + e b) = m
    simp only [M1, Pi.add_apply, Pi.sub_apply, sum_add_distrib, sum_sub_distrib, e_apply,
      sum_ite_eq', mem_univ, if_true]
    unfold M1 at huM; omega
  · show |((u.1 - e a + e b) i : ℝ) - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ
    have h2 := abs_le.1 (huD i); have h3 := abs_le.1 (hvD i)
    rw [abs_le]
    rcases hbetween i with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      have := (Int.cast_le (R := ℝ)).2 h <;> have := (Int.cast_le (R := ℝ)).2 h' <;>
      constructor <;> linarith

/-- Two points of `𝔇` with the same right degrees are joined by `≤ ℓ s^φ` `S`-steps. -/
theorem diam_S {φ : ℝ} (_hφ₀ : 0 ≤ φ) (hφ : φ ≤ 1) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {u v : BSeq ℓ n} (hu : u ∈ DsetZ φ ℓ n m) (hv : v ∈ DsetZ φ ℓ n m) (huv : u.2 = v.2) :
    ∃ r : ℕ, (r : ℝ) ≤ ℓ * (m / ℓ : ℝ) ^ φ ∧ HasWalk AdjS (DsetZ φ ℓ n m) r u v := by
  have key : ∀ k : ℕ, ∀ u v : BSeq ℓ n, u ∈ DsetZ φ ℓ n m → v ∈ DsetZ φ ℓ n m → u.2 = v.2 →
      LW.dist1 u.1 v.1 ≤ 2 * k → HasWalk AdjS (DsetZ φ ℓ n m) k u v := by
    intro k
    induction k with
    | zero =>
      intro u v hu hv huv hd
      have h0 : LW.dist1 u.1 v.1 = 0 :=
        le_antisymm (by simpa using hd) (sum_nonneg fun i _ => abs_nonneg _)
      rw [Prod.ext (dist1_eq_zero h0) huv]; exact HasWalk.zero _ hv
    | succ k ih =>
      intro u v hu hv huv hd
      by_cases hne : u = v
      · subst hne; exact (HasWalk.zero _ hu).mono (Nat.zero_le _)
      have hu' := (mem_DsetZ hφ hS).1 hu
      have hv' := (mem_DsetZ hφ hS).1 hv
      have hne1 : u.1 ≠ v.1 := fun h => hne (Prod.ext h huv)
      obtain ⟨a, b, ha, hb⟩ := exists_step hne1 (by rw [hu'.2.2.1, hv'.2.2.1])
      have hw := (mem_DsetZ hφ hS).2 (stepS_mem_Dset hu' hv' ha hb)
      have hadj : AdjS u (u.1 - e a + e b, u.2) :=
        ⟨(u.1 + e b, u.2), b, a, Prod.ext (by show u.1 = u.1 + e b - e b; abel)
          (by show u.2 = u.2 - 0; simp),
          Prod.ext (by show u.1 - e a + e b = u.1 + e b - e a; abel) (by show u.2 = u.2 - 0; simp)⟩
      exact HasWalk.cons hu hadj (ih _ _ hw hv huv
        (by rw [dist1_step ha hb]; push_cast at hd ⊢; omega))
  have hu' := (mem_DsetZ hφ hS).1 hu
  have hv' := (mem_DsetZ hφ hS).1 hv
  obtain ⟨-, -, huM, -, huD, -⟩ := hu'
  obtain ⟨-, -, hvM, -, hvD, -⟩ := hv'
  obtain ⟨t, ht⟩ := dist1_even (huM.trans hvM.symm)
  refine ⟨(LW.dist1 u.1 v.1).toNat / 2, ?_, key _ u v hu hv huv (by omega)⟩
  have hd : ((LW.dist1 u.1 v.1 : ℤ) : ℝ) ≤ 2 * (ℓ * (m / ℓ : ℝ) ^ φ) := by
    unfold LW.dist1; push_cast
    calc ∑ i, |(u.1 i : ℝ) - v.1 i| ≤ ∑ i : Fin ℓ, 2 * (m / ℓ : ℝ) ^ φ := by
          refine sum_le_sum fun i _ => ?_
          have := huD i; have := hvD i
          calc |(u.1 i : ℝ) - v.1 i| = |((u.1 i : ℝ) - m / ℓ) - ((v.1 i : ℝ) - m / ℓ)| := by
                ring_nf
            _ ≤ _ := (abs_sub _ _).trans (by linarith)
      _ = 2 * (ℓ * (m / ℓ : ℝ) ^ φ) := by simp; ring
  have h2 : (((LW.dist1 u.1 v.1).toNat / 2 : ℕ) : ℝ) ≤ (LW.dist1 u.1 v.1 : ℝ) / 2 := by
    have h3 : (((LW.dist1 u.1 v.1).toNat / 2 : ℕ) : ℝ) ≤ ((LW.dist1 u.1 v.1).toNat : ℝ) / 2 := by
      have h5 : (LW.dist1 u.1 v.1).toNat / 2 * 2 ≤ (LW.dist1 u.1 v.1).toNat :=
        Nat.div_mul_le_self _ _
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast h5
    have h4 : (((LW.dist1 u.1 v.1).toNat : ℕ) : ℤ) = LW.dist1 u.1 v.1 :=
      Int.toNat_of_nonneg (sum_nonneg fun i _ => abs_nonneg _)
    have h4' : ((LW.dist1 u.1 v.1).toNat : ℝ) = ((LW.dist1 u.1 v.1 : ℤ) : ℝ) := by
      exact_mod_cast h4
    rw [← h4']; exact h3
  linarith

/-- Transport an `S`-walk on the transposed problem to a `T`-walk. -/
theorem hasWalk_swap {φ : ℝ} (hφ : φ ≤ 1) {m r : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {u v : BSeq ℓ n} (h : HasWalk AdjS (DsetZ φ n ℓ m) r u.swap v.swap) :
    HasWalk AdjT (DsetZ φ ℓ n m) r u v := by
  obtain ⟨k, hk, p, h0, hl, hW, hE⟩ := h
  refine ⟨k, hk, fun i => (p i).swap, by show (p 0).swap = u; rw [h0, Prod.swap_swap],
    by show (p (Fin.last k)).swap = v; rw [hl, Prod.swap_swap], fun i => ?_, fun i => ?_⟩
  · show (p i).swap ∈ DsetZ φ ℓ n m
    rw [mem_DsetZ hφ hS, ← Dset_swap, Prod.swap_swap]
    exact (mem_DsetZ hφ hS.swap).1 (hW i)
  · obtain ⟨d, a, b, h1, h2⟩ := hE i
    exact ⟨d.swap, a, b, by show (p i.castSucc).swap = _; rw [h1, swap_sub_eS],
      by show (p i.succ).swap = _; rw [h2, swap_sub_eS]⟩

/-- Two points of `𝔇` with the same left degrees are joined by `≤ n t^φ` `T`-steps. -/
theorem diam_T {φ : ℝ} (hφ₀ : 0 ≤ φ) (hφ : φ ≤ 1) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {u v : BSeq ℓ n} (hu : u ∈ DsetZ φ ℓ n m) (hv : v ∈ DsetZ φ ℓ n m) (huv : u.1 = v.1) :
    ∃ r : ℕ, (r : ℝ) ≤ n * (m / n : ℝ) ^ φ ∧ HasWalk AdjT (DsetZ φ ℓ n m) r u v := by
  have hu' : u.swap ∈ DsetZ φ n ℓ m :=
    (mem_DsetZ hφ hS.swap).2 (Dset_swap.2 ((mem_DsetZ hφ hS).1 hu))
  have hv' : v.swap ∈ DsetZ φ n ℓ m :=
    (mem_DsetZ hφ hS.swap).2 (Dset_swap.2 ((mem_DsetZ hφ hS).1 hv))
  obtain ⟨r, hr, hw⟩ := diam_S hφ₀ hφ hS.swap hu' hv' huv
  exact ⟨r, hr, hasWalk_swap hφ hS hw⟩

/-- Any two points of `𝔇` are joined by `≤ ℓ s^φ` `S`-steps followed by `≤ n t^φ` `T`-steps. -/
theorem two_phase {φ : ℝ} (hφ₀ : 0 ≤ φ) (hφ : φ ≤ 1) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {u v : BSeq ℓ n} (hu : u ∈ DsetZ φ ℓ n m) (hv : v ∈ DsetZ φ ℓ n m) :
    ∃ w ∈ DsetZ φ ℓ n m, HasWalk AdjS (DsetZ φ ℓ n m) ⌊(ℓ * (m / ℓ : ℝ) ^ φ)⌋₊ u w ∧
      HasWalk AdjT (DsetZ φ ℓ n m) ⌊(n * (m / n : ℝ) ^ φ)⌋₊ w v := by
  have hu' := (mem_DsetZ hφ hS).1 hu
  have hv' := (mem_DsetZ hφ hS).1 hv
  have hw : (v.1, u.2) ∈ DsetZ φ ℓ n m :=
    (mem_DsetZ hφ hS).2 ⟨hv'.1, hu'.2.1, hv'.2.2.1, hu'.2.2.2.1, hv'.2.2.2.2.1, hu'.2.2.2.2.2⟩
  obtain ⟨r₁, hr₁, hw₁⟩ := diam_S hφ₀ hφ hS hu hw rfl
  obtain ⟨r₂, hr₂, hw₂⟩ := diam_T hφ₀ hφ hS hw hv rfl
  exact ⟨_, hw, hw₁.mono (Nat.le_floor hr₁), hw₂.mono (Nat.le_floor hr₂)⟩

end LW.Bip
