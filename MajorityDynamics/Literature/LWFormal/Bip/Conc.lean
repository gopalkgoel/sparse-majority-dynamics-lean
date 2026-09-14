import MajorityDynamics.Literature.LWFormal.Bip.Prob
import MajorityDynamics.Literature.LWFormal.Bip.Errors

set_option autoImplicit true

/-!
# Concentration for Theorem 1.1: the good set `W` and `E_{ℬ_m}(1_W H̃) = 1 + O(1/√ℓ + 1/√n)`

`ℬ_m(ℓ,n)` is the product of the two marginals of `𝒢(ℓ,n,m)`, so all estimates reduce to
one-sided statements about `𝒢(ℓ,n,m)` (and their transposes).
-/

namespace LW.Bip

open Finset Real

variable {ℓ n : ℕ}

/-! ### The underlying set `Ω` -/

/-- Left degree sequences of `𝒢(ℓ,n,m)`: entries `≤ n`, sum `m`. -/
def OmS (ℓ n m : ℕ) : Finset (Fin ℓ → ℕ) :=
  (Fintype.piFinset fun _ => range (n + 1)).filter fun s => ∑ a, s a = m

theorem mem_OmS {m : ℕ} {s : Fin ℓ → ℕ} : s ∈ OmS ℓ n m ↔ (∀ a, s a ≤ n) ∧ ∑ a, s a = m := by
  simp [OmS, Fintype.mem_piFinset]

theorem ldeg_mem_OmS {m : ℕ} {E : BGraph ℓ n} (hE : E ∈ Gm ℓ n m) : ldeg E ∈ OmS ℓ n m :=
  mem_OmS.2 ⟨ldeg_le E, by rw [sum_ldeg, mem_Gm.1 hE]⟩

theorem rdeg_mem_OmS {m : ℕ} {E : BGraph ℓ n} (hE : E ∈ Gm ℓ n m) : rdeg E ∈ OmS n ℓ m :=
  mem_OmS.2 ⟨rdeg_le E, by rw [sum_rdeg, mem_Gm.1 hE]⟩

theorem Gm_nonempty {m : ℕ} (hm : m ≤ ℓ * n) : (Gm ℓ n m).Nonempty :=
  card_pos.1 (by rw [card_Gm]; exact Nat.choose_pos hm)

theorem prob_not' {X : Type*} [DecidableEq X] (Ω : Finset X) (A : X → Prop) [DecidablePred A]
    [DecidablePred fun x => ¬ A x] (hΩ : Ω.Nonempty) : prob Ω (fun x => ¬ A x) = 1 - prob Ω A := by
  convert prob_not Ω A hΩ

theorem ldeg_tr' (E : BGraph ℓ n) : ldeg (tr E) = rdeg E := funext (ldeg_tr E)

theorem card_tr (E : BGraph ℓ n) : (tr E).card = E.card := by
  unfold tr; rw [Equiv.finsetCongr_apply, card_map]

/-- `Ω = 𝒟(ℬ_m(ℓ,n))`. -/
def OmegaB (ℓ n m : ℕ) : Finset ((Fin ℓ → ℕ) × (Fin n → ℕ)) := OmS ℓ n m ×ˢ OmS n ℓ m

/-- The degree pair of a bipartite graph. -/
def degPair (E : BGraph ℓ n) : (Fin ℓ → ℕ) × (Fin n → ℕ) := (ldeg E, rdeg E)

theorem degPair_mem {m : ℕ} {E : BGraph ℓ n} (hE : E ∈ Gm ℓ n m) : degPair E ∈ OmegaB ℓ n m :=
  mem_product.2 ⟨ldeg_mem_OmS hE, rdeg_mem_OmS hE⟩

theorem probG_eq (m : ℕ) (x : (Fin ℓ → ℕ) × (Fin n → ℕ)) :
    probG ℓ n m x.1 x.2 = prob (Gm ℓ n m) (degPair · = x) := by
  unfold probG prob; congr 2
  exact congrArg Finset.card (filter_congr fun E _ => by simp [degPair, Prod.ext_iff])

theorem sum_probG {m : ℕ} (hm : m ≤ ℓ * n) : ∑ x ∈ OmegaB ℓ n m, probG ℓ n m x.1 x.2 = 1 := by
  rw [sum_congr rfl fun x _ => probG_eq m x]
  exact sum_prob_eq_one _ degPair _ (Gm_nonempty hm) fun E hE => degPair_mem hE

/-! ### `ℬ_m` as the product of the two marginals -/

theorem card_Gm_filter_ldeg (m : ℕ) (s : Fin ℓ → ℕ) (hs : ∑ a, s a = m) :
    ((Gm ℓ n m).filter (ldeg · = s)).card = ∏ a, n.choose (s a) := by
  have key : ∏ a, n.choose (s a) =
      (Fintype.piFinset fun a => (univ : Finset (Fin n)).powersetCard (s a)).card := by
    rw [Fintype.card_piFinset]
    exact prod_congr rfl fun a _ => by rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [key]
  refine card_bij (fun E _ => lnbrs E) ?_ ?_ ?_
  · intro E hE
    rw [Fintype.mem_piFinset]
    intro a
    rw [mem_powersetCard, card_lnbrs, (mem_filter.1 hE).2]
    exact ⟨subset_univ _, rfl⟩
  · intro E _ F _ h
    ext ⟨a, v⟩
    have := congrFun h a
    rw [Finset.ext_iff] at this
    simpa [lnbrs] using this v
  · intro F hF
    rw [Fintype.mem_piFinset] at hF
    set E : BGraph ℓ n := univ.filter fun p => p.2 ∈ F p.1 with hEdef
    have hl : ∀ a, lnbrs E a = F a := fun a => by ext v; simp [lnbrs, hEdef]
    have hdeg : ldeg E = s := funext fun a => by
      rw [← card_lnbrs, hl, (mem_powersetCard.1 (hF a)).2]
    refine ⟨E, mem_filter.2 ⟨mem_Gm.2 ?_, hdeg⟩, funext hl⟩
    rw [← sum_ldeg, hdeg, hs]

theorem prob_ldeg_eq (m : ℕ) {s : Fin ℓ → ℕ} (hs : ∑ a, s a = m) :
    prob (Gm ℓ n m) (ldeg · = s) = (∏ a, (n.choose (s a) : ℝ)) / (ℓ * n).choose m := by
  rw [prob, card_Gm_filter_ldeg m s hs, card_Gm]; push_cast; rfl

theorem prob_rdeg_eq (m : ℕ) {t : Fin n → ℕ} (ht : ∑ v, t v = m) :
    prob (Gm ℓ n m) (rdeg · = t) = (∏ v, (ℓ.choose (t v) : ℝ)) / (ℓ * n).choose m := by
  have h := prob_tr (m := m) (fun F : BGraph n ℓ => ldeg F = t)
  rw [prob_ldeg_eq m ht, mul_comm n ℓ] at h
  rw [← h]
  unfold prob; congr 2
  exact congrArg Finset.card (filter_congr fun E _ => by rw [ldeg_tr'])

theorem probB_eq {m : ℕ} {s : Fin ℓ → ℕ} {t : Fin n → ℕ} (hs : ∑ a, s a = m)
    (ht : ∑ v, t v = m) :
    probB ℓ n m s t = prob (Gm ℓ n m) (ldeg · = s) * prob (Gm ℓ n m) (rdeg · = t) := by
  rw [prob_ldeg_eq m hs, prob_rdeg_eq m ht, probB]; ring

/-- `E_{ℬ_m}(1_{A×B} f(s) g(t))` factorises into the two marginals of `𝒢(ℓ,n,m)`. -/
theorem sum_probB_mul (m : ℕ) {A : Finset (Fin ℓ → ℕ)} {B : Finset (Fin n → ℕ)}
    (hA : A ⊆ OmS ℓ n m) (hB : B ⊆ OmS n ℓ m) (f : (Fin ℓ → ℕ) → ℝ) (g : (Fin n → ℕ) → ℝ) :
    ∑ x ∈ A ×ˢ B, probB ℓ n m x.1 x.2 * (f x.1 * g x.2) =
      (∑ s ∈ A, prob (Gm ℓ n m) (ldeg · = s) * f s) *
        ∑ t ∈ B, prob (Gm ℓ n m) (rdeg · = t) * g t := by
  rw [sum_mul_sum, sum_product]
  refine sum_congr rfl fun s hs => sum_congr rfl fun t ht => ?_
  rw [probB_eq (mem_OmS.1 (hA hs)).2 (mem_OmS.1 (hB ht)).2]; ring

theorem sum_probB {m : ℕ} (hm : m ≤ ℓ * n) : ∑ x ∈ OmegaB ℓ n m, probB ℓ n m x.1 x.2 = 1 := by
  have := sum_probB_mul (ℓ := ℓ) (n := n) m subset_rfl subset_rfl (fun _ => 1) (fun _ => 1)
  simp only [mul_one] at this
  rw [OmegaB, this, sum_prob_eq_one _ _ _ (Gm_nonempty hm) fun E hE => ldeg_mem_OmS hE,
    sum_prob_eq_one _ _ _ (Gm_nonempty hm) fun E hE => rdeg_mem_OmS hE, one_mul]

theorem probB_nonneg (m : ℕ) (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : 0 ≤ probB ℓ n m s t := by
  unfold probB; positivity

theorem probB_pos {m : ℕ} (hm : m ≤ ℓ * n) {x : (Fin ℓ → ℕ) × (Fin n → ℕ)}
    (hx : x ∈ OmegaB ℓ n m) : 0 < probB ℓ n m x.1 x.2 := by
  obtain ⟨hs, ht⟩ := mem_product.1 hx
  unfold probB
  refine mul_pos (mul_pos (pow_pos (inv_pos.2 (by exact_mod_cast Nat.choose_pos hm)) 2)
    (prod_pos fun a _ => ?_)) (prod_pos fun v _ => ?_)
  · exact_mod_cast Nat.choose_pos ((mem_OmS.1 hs).1 a)
  · exact_mod_cast Nat.choose_pos ((mem_OmS.1 ht).1 v)

/-- Transporting a left-side sum to the right side by transposition. -/
theorem sum_rdeg_eq_sum_ldeg (m : ℕ) (f : (Fin n → ℕ) → ℝ) :
    ∑ E ∈ Gm ℓ n m, f (rdeg E) = ∑ F ∈ Gm n ℓ m, f (ldeg F) :=
  sum_equiv tr (fun E => by rw [mem_Gm, mem_Gm, card_tr]) fun E _ => by rw [ldeg_tr']

/-! ### The factor `X(s) = 1 - σ²(s)/(s̄(1-μ))` of `H̃` -/

/-- `X(s) = 1 - σ²(s)/(s̄(1-μ))` with `μ = m/(ℓn)`. -/
noncomputable def XS (ℓ n m : ℕ) (s : Fin ℓ → ℕ) : ℝ :=
  1 - var s / (mean s * (1 - m / (ℓ * n)))

theorem Htilde_eq {m : ℕ} {s : Fin ℓ → ℕ} {t : Fin n → ℕ} (hs : ∑ a, s a = m)
    (ht : ∑ v, t v = m) : Htilde s t = exp (-(1 / 2) * XS ℓ n m s * XS n ℓ m t) := by
  unfold Htilde XS muN
  have h1 : ∑ a, (s a : ℝ) = m := by exact_mod_cast hs
  have h2 : ∑ v, (t v : ℝ) = m := by exact_mod_cast ht
  rw [h1, h2]; congr 1; ring

theorem mean_ldeg {m : ℕ} {E : BGraph ℓ n} (hE : E ∈ Gm ℓ n m) : mean (ldeg E) = m / ℓ := by
  unfold mean; congr 1; exact_mod_cast (sum_ldeg E).trans (mem_Gm.1 hE)

theorem var_ldeg {m : ℕ} {E : BGraph ℓ n} (hE : E ∈ Gm ℓ n m) :
    var (ldeg E) = FS ℓ m (ldeg E) / ℓ := by
  unfold var FS; rw [mean_ldeg hE]

theorem mean_of_mem_OmS {m : ℕ} {s : Fin ℓ → ℕ} (hs : s ∈ OmS ℓ n m) : mean s = m / ℓ := by
  unfold mean; congr 1; exact_mod_cast (mem_OmS.1 hs).2

theorem var_nonneg {k : ℕ} (d : Fin k → ℕ) : 0 ≤ var d := by unfold var; positivity

theorem XS_eq {m : ℕ} (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmN : m + 1 ≤ ℓ * n)
    {E : BGraph ℓ n} (hE : E ∈ Gm ℓ n m) :
    XS ℓ n m (ldeg E) =
      1 - (ℓ - 1) * n / (ℓ * n - 1) * (FS ℓ m (ldeg E) / cB ℓ n m) := by
  unfold XS cB
  rw [var_ldeg hE, mean_ldeg hE]
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmN' : (m : ℝ) + 1 ≤ ℓ * n := by exact_mod_cast hmN
  have e : (1 : ℝ) - m / (ℓ * n) = (ℓ * n - m) / (ℓ * n) := by field_simp
  rw [e]
  have h1 : (ℓ : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (ℓ : ℝ) * n - 1 ≠ 0 := by nlinarith
  have h3 : (ℓ : ℝ) * n - m ≠ 0 := by linarith
  have h4 : (ℓ : ℝ) ≠ 0 := by linarith
  have h5 : (n : ℝ) ≠ 0 := by linarith
  have h6 : (m : ℝ) ≠ 0 := by linarith
  field_simp

theorem abs_XS_le {m : ℕ} (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmN : m + 1 ≤ ℓ * n)
    {E : BGraph ℓ n} (hE : E ∈ Gm ℓ n m) :
    |XS ℓ n m (ldeg E)| ≤ 1 / ℓ + |FS ℓ m (ldeg E) / cB ℓ n m - 1| := by
  rw [XS_eq hℓ hn hm hmN hE]
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set κ : ℝ := (ℓ - 1) * n / (ℓ * n - 1) with hκ
  set ρ : ℝ := FS ℓ m (ldeg E) / cB ℓ n m - 1 with hρ
  have hden : 0 < (ℓ : ℝ) * n - 1 := by nlinarith
  have hκ0 : 0 ≤ κ := div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one hden]; nlinarith
  have hκ2 : 1 - κ ≤ 1 / ℓ := by
    have : 1 - κ = (n - 1) / (ℓ * n - 1) := by rw [hκ]; field_simp; ring
    rw [this, div_le_div_iff₀ hden (by linarith)]; nlinarith
  have e : 1 - κ * (FS ℓ m (ldeg E) / cB ℓ n m) = (1 - κ) - κ * ρ := by rw [hρ]; ring
  rw [e]
  calc |(1 - κ) - κ * ρ| ≤ |1 - κ| + |κ * ρ| := abs_sub _ _
    _ = (1 - κ) + κ * |ρ| := by rw [abs_of_nonneg (by linarith), abs_mul, abs_of_nonneg hκ0]
    _ ≤ 1 / ℓ + 1 * |ρ| := by gcongr
    _ = _ := by ring

theorem sum_abs_XS_le (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) {m : ℕ} (hm : 4 ≤ m) (hN : 6 ≤ ℓ * n)
    (hmN : m + 1 ≤ ℓ * n) :
    ∑ E ∈ Gm ℓ n m, |XS ℓ n m (ldeg E)| ≤ 4 * ((Gm ℓ n m).card : ℝ) / √ℓ := by
  obtain ⟨-, -, h3⟩ := rho_moments ℓ n m hℓ hn hm hN hmN
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hs : √(ℓ : ℝ) ≤ ℓ := sqrt_le_self_iff.2 (Or.inr (by linarith))
  have hs0 : 0 < √(ℓ : ℝ) := sqrt_pos.2 (by linarith)
  have h1 : (1 : ℝ) / ℓ ≤ 1 / √ℓ := one_div_le_one_div_of_le hs0 hs
  calc ∑ E ∈ Gm ℓ n m, |XS ℓ n m (ldeg E)|
      ≤ ∑ E ∈ Gm ℓ n m, (1 / ℓ + |FS ℓ m (ldeg E) / cB ℓ n m - 1|) :=
        sum_le_sum fun E hE => abs_XS_le hℓ hn (by omega) hmN hE
    _ = ((Gm ℓ n m).card : ℝ) * (1 / ℓ) + ∑ E ∈ Gm ℓ n m, |FS ℓ m (ldeg E) / cB ℓ n m - 1| := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ((Gm ℓ n m).card : ℝ) * (1 / √ℓ) + 3 * ((Gm ℓ n m).card : ℝ) / √ℓ := by gcongr
    _ = _ := by ring

/-- `E_{𝒢}|X(s)| ≤ 4/√ℓ`, as a sum over the left marginal. -/
theorem sum_prob_abs_XS_le (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) {m : ℕ} (hm : 4 ≤ m) (hN : 6 ≤ ℓ * n)
    (hmN : m + 1 ≤ ℓ * n) {A : Finset (Fin ℓ → ℕ)} (hA : A ⊆ OmS ℓ n m) :
    ∑ s ∈ A, prob (Gm ℓ n m) (ldeg · = s) * |XS ℓ n m s| ≤ 4 / √ℓ := by
  have hcard : (0 : ℝ) < (Gm ℓ n m).card := by
    exact_mod_cast card_pos.2 (Gm_nonempty (by omega))
  calc ∑ s ∈ A, prob (Gm ℓ n m) (ldeg · = s) * |XS ℓ n m s|
      ≤ ∑ s ∈ OmS ℓ n m, prob (Gm ℓ n m) (ldeg · = s) * |XS ℓ n m s| :=
        sum_le_sum_of_subset_of_nonneg hA fun s _ _ =>
          mul_nonneg (prob_nonneg _ _) (abs_nonneg _)
    _ = (∑ E ∈ Gm ℓ n m, |XS ℓ n m (ldeg E)|) / (Gm ℓ n m).card :=
        sum_prob_mul _ _ _ _ fun E hE => ldeg_mem_OmS hE
    _ ≤ 4 * ((Gm ℓ n m).card : ℝ) / √ℓ / (Gm ℓ n m).card :=
        div_le_div_of_nonneg_right (sum_abs_XS_le hℓ hn hm hN hmN) hcard.le
    _ = 4 / √ℓ := by field_simp

/-- The right-side version, by transposition. -/
theorem sum_prob_abs_XT_le (hℓ : 1 ≤ ℓ) (hn : 2 ≤ n) {m : ℕ} (hm : 4 ≤ m) (hN : 6 ≤ ℓ * n)
    (hmN : m + 1 ≤ ℓ * n) {B : Finset (Fin n → ℕ)} (hB : B ⊆ OmS n ℓ m) :
    ∑ t ∈ B, prob (Gm ℓ n m) (rdeg · = t) * |XS n ℓ m t| ≤ 4 / √n := by
  have hcard : (0 : ℝ) < (Gm ℓ n m).card := by
    exact_mod_cast card_pos.2 (Gm_nonempty (by omega))
  have hcard' : ((Gm n ℓ m).card : ℝ) = (Gm ℓ n m).card := by
    rw [card_Gm, card_Gm, mul_comm]
  calc ∑ t ∈ B, prob (Gm ℓ n m) (rdeg · = t) * |XS n ℓ m t|
      ≤ ∑ t ∈ OmS n ℓ m, prob (Gm ℓ n m) (rdeg · = t) * |XS n ℓ m t| :=
        sum_le_sum_of_subset_of_nonneg hB fun t _ _ =>
          mul_nonneg (prob_nonneg _ _) (abs_nonneg _)
    _ = (∑ E ∈ Gm ℓ n m, |XS n ℓ m (rdeg E)|) / (Gm ℓ n m).card :=
        sum_prob_mul _ _ _ _ fun E hE => rdeg_mem_OmS hE
    _ = (∑ F ∈ Gm n ℓ m, |XS n ℓ m (ldeg F)|) / (Gm n ℓ m).card := by
        rw [sum_rdeg_eq_sum_ldeg m fun t => |XS n ℓ m t|, hcard']
    _ ≤ 4 * ((Gm n ℓ m).card : ℝ) / √n / (Gm n ℓ m).card :=
        div_le_div_of_nonneg_right
          (sum_abs_XS_le hn hℓ hm (by rw [mul_comm]; exact hN) (by rw [mul_comm]; exact hmN))
          (by rw [hcard']; exact hcard.le)
    _ = 4 / √n := by rw [hcard']; field_simp

/-! ### The good set `W` -/

open Classical in
/-- `φ`-spread left sequences. -/
noncomputable def SprS (φ : ℝ) (ℓ n m : ℕ) : Finset (Fin ℓ → ℕ) :=
  (OmS ℓ n m).filter fun s => ∀ a, |(s a : ℝ) - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ

open Classical in
/-- Good left sequences: `φ`-spread with `σ²(s) ≤ 2 s̄`. -/
noncomputable def GoodS (φ : ℝ) (ℓ n m : ℕ) : Finset (Fin ℓ → ℕ) :=
  (SprS φ ℓ n m).filter fun s => var s ≤ 2 * mean s

theorem mem_SprS {φ : ℝ} {m : ℕ} {s : Fin ℓ → ℕ} :
    s ∈ SprS φ ℓ n m ↔ s ∈ OmS ℓ n m ∧ ∀ a, |(s a : ℝ) - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ := by
  unfold SprS; exact mem_filter

theorem mem_GoodS {φ : ℝ} {m : ℕ} {s : Fin ℓ → ℕ} :
    s ∈ GoodS φ ℓ n m ↔ s ∈ SprS φ ℓ n m ∧ var s ≤ 2 * mean s := by
  unfold GoodS; exact mem_filter

theorem GoodS_subset_SprS {φ : ℝ} {m : ℕ} : GoodS φ ℓ n m ⊆ SprS φ ℓ n m :=
  fun _ h => (mem_GoodS.1 h).1

theorem SprS_subset_OmS {φ : ℝ} {m : ℕ} : SprS φ ℓ n m ⊆ OmS ℓ n m :=
  fun _ h => (mem_SprS.1 h).1

/-- `𝔇 = 𝔇_S × 𝔇_T`. -/
noncomputable def DsetB (φ : ℝ) (ℓ n m : ℕ) : Finset ((Fin ℓ → ℕ) × (Fin n → ℕ)) :=
  SprS φ ℓ n m ×ˢ SprS φ n ℓ m

/-- `W = W_S × W_T ⊆ 𝔇`. -/
noncomputable def WsetB (φ : ℝ) (ℓ n m : ℕ) : Finset ((Fin ℓ → ℕ) × (Fin n → ℕ)) :=
  GoodS φ ℓ n m ×ˢ GoodS φ n ℓ m

theorem WsetB_subset_DsetB {φ : ℝ} {m : ℕ} : WsetB φ ℓ n m ⊆ DsetB φ ℓ n m :=
  product_subset_product GoodS_subset_SprS GoodS_subset_SprS

theorem DsetB_subset_OmegaB {φ : ℝ} {m : ℕ} : DsetB φ ℓ n m ⊆ OmegaB ℓ n m :=
  product_subset_product SprS_subset_OmS SprS_subset_OmS

/-! ### `P_𝒢(s ∈ W_S) ≥ 1 - 5/√ℓ` -/

theorem Sizes.two_le_ℓ {m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) : (2 : ℝ) ≤ ℓ := by
  linarith [h.basic.1]

theorem Sizes.two_le_n {m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) : (2 : ℝ) ≤ n := by
  linarith [h.basic.2.1]

theorem Sizes.two_mul_le {m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) : 2 * m ≤ ℓ * n := by
  have := h.mu_le
  have hℓ : (1 : ℝ) ≤ ℓ := by linarith [h.two_le_ℓ]
  have hn : (1 : ℝ) ≤ n := by linarith [h.two_le_n]
  have : (2 * m : ℝ) ≤ ℓ * n := by
    rw [div_le_iff₀ (by positivity)] at this; nlinarith
  exact_mod_cast this

theorem Sizes.four_le_m {m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) : 4 ≤ m := by
  have hℓ : (1 : ℝ) ≤ ℓ := by linarith [h.two_le_ℓ]
  have h1 := h.s_ge
  have hl : (35000 : ℝ) ≤ max (log ℓ) (log n) := h.B_ge.trans (h.logℓ.trans (le_max_left _ _))
  have : (4 : ℝ) ≤ max (log ℓ) (log n) ^ K := by
    have := rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ max (log ℓ) (log n))
      (by linarith [h.K_ge] : (1 : ℝ) ≤ K)
    rw [rpow_one] at this; linarith
  have : (4 : ℝ) ≤ m / ℓ := this.trans h1
  rw [le_div_iff₀ (by linarith)] at this
  exact_mod_cast (by nlinarith : (4 : ℝ) ≤ m)

theorem Sizes.six_le {m : ℕ} {K B : ℝ} (h : Sizes ℓ n m K B) : 6 ≤ ℓ * n := by
  have hℓ : 3 ≤ ℓ := by exact_mod_cast (by linarith [h.basic.1] : (3 : ℝ) ≤ ℓ)
  have hn : 2 ≤ n := by exact_mod_cast h.two_le_n
  exact Nat.mul_le_mul hℓ hn

theorem prob_var_gt_le {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B) :
    prob (Gm ℓ n m) (fun E => ¬ var (ldeg E) ≤ 2 * mean (ldeg E)) ≤ 4 / √ℓ := by
  have hℓ : 2 ≤ ℓ := by exact_mod_cast hS.two_le_ℓ
  have hn : 1 ≤ n := by exact_mod_cast (by linarith [hS.two_le_n] : (1 : ℝ) ≤ n)
  have hm := hS.four_le_m
  have hmN : m + 1 ≤ ℓ * n := by have := hS.two_mul_le; omega
  have hcard : (0 : ℝ) < (Gm ℓ n m).card := by
    exact_mod_cast card_pos.2 (Gm_nonempty (by omega))
  have key : ∀ E ∈ Gm ℓ n m, ¬ var (ldeg E) ≤ 2 * mean (ldeg E) → 1 ≤ |XS ℓ n m (ldeg E)| := by
    intro E hE h
    push Not at h
    unfold XS
    rw [mean_ldeg hE] at h ⊢
    have hμ := hS.mu_le
    have hμ0 : 0 ≤ (m : ℝ) / (ℓ * n) := by positivity
    have hmean : 0 < (m : ℝ) / ℓ := by
      have : (4 : ℝ) ≤ m := by exact_mod_cast hm
      positivity
    have h2 : 2 < var (ldeg E) / (m / ℓ * (1 - m / (ℓ * n))) := by
      rw [lt_div_iff₀ (mul_pos hmean (by linarith))]
      nlinarith
    rw [abs_of_neg (by linarith)]; linarith
  have h1 : (((Gm ℓ n m).filter fun E => ¬ var (ldeg E) ≤ 2 * mean (ldeg E)).card : ℝ) ≤
      ∑ E ∈ Gm ℓ n m, |XS ℓ n m (ldeg E)| := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    push_cast
    exact (sum_le_sum fun E hE => key E (mem_filter.1 hE).1 (mem_filter.1 hE).2).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => abs_nonneg _)
  rw [prob, div_le_iff₀ hcard]
  calc _ ≤ _ := h1
    _ ≤ 4 * ((Gm ℓ n m).card : ℝ) / √ℓ := sum_abs_XS_le hℓ hn hm hS.six_le hmN
    _ = 4 / √ℓ * (Gm ℓ n m).card := by ring

theorem prob_spread_ge {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ ≤ 1) {m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) (hK : 2 / (2 * φ - 1) ≤ K) :
    1 - 1 / (ℓ : ℝ) ^ 2 ≤
      prob (Gm ℓ n m) (fun E => ∀ a, |(ldeg E a : ℝ) - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ) := by
  have hℓ : 2 ≤ ℓ := by exact_mod_cast hS.two_le_ℓ
  have hn : 1 ≤ n := by exact_mod_cast (by linarith [hS.two_le_n] : (1 : ℝ) ≤ n)
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog : (35000 : ℝ) ≤ log ℓ := hS.B_ge.trans hS.logℓ
  have hD : log ℓ ^ (2 / (2 * φ - 1)) ≤ (m / ℓ : ℝ) := by
    calc log ℓ ^ (2 / (2 * φ - 1)) ≤ log ℓ ^ K :=
          rpow_le_rpow_of_exponent_le (by linarith) hK
      _ ≤ max (log ℓ) (log n) ^ K := rpow_le_rpow (by linarith) (le_max_left _ _) (by linarith [hS.K_ge])
      _ ≤ m / ℓ := hS.s_ge
  have hDℓ : (m / ℓ : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
    have := hS.mu_le
    have hn' : (1 : ℝ) ≤ n := by linarith [hS.two_le_n]
    have hℓn := hS.ℓn
    rw [div_le_iff₀ (by positivity)] at this ⊢
    nlinarith
  have hℓ4 : 4 ≤ ℓ := by exact_mod_cast (by linarith [hS.basic.1] : (4 : ℝ) ≤ ℓ)
  obtain ⟨ht6, htD, hδ⟩ := tail_numeric hφ₁ hφ₂ (n := ℓ) (D := m / ℓ) hℓ4 (by linarith) hD hDℓ
  have hne := Gm_nonempty (m := m) (ℓ := ℓ) (n := n) (by have := hS.two_mul_le; omega)
  have h := prob_forall_ge (Gm ℓ n m) hne (n := ℓ) ldeg (m / ℓ) ((m / ℓ : ℝ) ^ φ)
    (2 * (m / ℓ + 1) * exp (-((m / ℓ : ℝ) ^ φ) ^ 2 / (32 * (m / ℓ))))
    (fun a => ldeg_tail ℓ n m hℓ hn hS.two_mul_le a ht6 htD)
  linarith

theorem prob_good_ge {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ ≤ 1) {m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) (hK : 2 / (2 * φ - 1) ≤ K) :
    1 - 5 / √ℓ ≤ prob (Gm ℓ n m) (fun E => ldeg E ∈ GoodS φ ℓ n m) := by
  have hℓ' : (2 : ℝ) ≤ ℓ := hS.two_le_ℓ
  have hs : √(ℓ : ℝ) ≤ ℓ := sqrt_le_self_iff.2 (Or.inr (by linarith))
  have hs0 : 0 < √(ℓ : ℝ) := sqrt_pos.2 (by linarith)
  have h1 : (1 : ℝ) / ℓ ^ 2 ≤ 1 / √ℓ :=
    one_div_le_one_div_of_le hs0 (hs.trans (le_self_pow₀ (by linarith) two_ne_zero))
  have hA := prob_spread_ge hφ₁ hφ₂ hS hK
  have hB := prob_var_gt_le hS
  have hsub : prob (Gm ℓ n m) (fun E => ∀ a, |(ldeg E a : ℝ) - m / ℓ| ≤ (m / ℓ : ℝ) ^ φ) ≤
      prob (Gm ℓ n m) (fun E => ldeg E ∈ GoodS φ ℓ n m) +
        prob (Gm ℓ n m) (fun E => ¬ var (ldeg E) ≤ 2 * mean (ldeg E)) := by
    refine le_trans (prob_mono _ ?_) (prob_or_le _ _ _)
    intro E hE h
    by_cases hv : var (ldeg E) ≤ 2 * mean (ldeg E)
    · exact Or.inl (mem_GoodS.2 ⟨mem_SprS.2 ⟨ldeg_mem_OmS hE, h⟩, hv⟩)
    · exact Or.inr hv
  have : 5 / √(ℓ : ℝ) = 4 / √ℓ + 1 / √ℓ := by ring
  linarith

/-- The right-side version, by transposition. -/
theorem prob_good_ge' {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ ≤ 1) {m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) (hK : 2 / (2 * φ - 1) ≤ K) :
    1 - 5 / √n ≤ prob (Gm ℓ n m) (fun E => rdeg E ∈ GoodS φ n ℓ m) := by
  have h := prob_good_ge hφ₁ hφ₂ hS.swap hK
  rw [← prob_tr (m := m) (fun F : BGraph n ℓ => ldeg F ∈ GoodS φ n ℓ m)] at h
  refine h.trans (le_of_eq ?_)
  unfold prob; congr 2
  exact congrArg Finset.card (filter_congr fun E _ => by rw [ldeg_tr'])

/-! ### `E_{ℬ_m}(1_W H̃) = 1 + O(1/√ℓ + 1/√n)` -/

theorem abs_exp_sub_one_le_two {z : ℝ} (hz : |z| ≤ 2) : |exp z - 1| ≤ exp 2 * |z| := by
  have he : 1 ≤ exp 2 := one_le_exp (by norm_num)
  rcases le_or_gt 0 z with h | h
  · have h1 := add_one_le_exp (-z)
    rw [exp_neg] at h1
    have hez := exp_pos z
    have : exp z - 1 ≤ z * exp z := by
      have := mul_le_mul_of_nonneg_right h1 hez.le
      rw [inv_mul_cancel₀ hez.ne'] at this
      linarith
    rw [abs_of_nonneg h, abs_of_nonneg (by linarith [add_one_le_exp z])]
    calc exp z - 1 ≤ z * exp z := this
      _ ≤ z * exp 2 := mul_le_mul_of_nonneg_left (exp_le_exp.2 (by rw [abs_of_nonneg h] at hz; linarith)) h
      _ = _ := mul_comm _ _
  · have h1 := add_one_le_exp z
    have h2 : exp z ≤ 1 := by have := exp_le_exp.2 h.le; rwa [exp_zero] at this
    rw [abs_of_neg h, abs_of_nonpos (by linarith)]
    nlinarith

theorem XS_bounds {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B) {s : Fin ℓ → ℕ} (hs : s ∈ OmS ℓ n m)
    (hv : var s ≤ 2 * mean s) : |XS ℓ n m s| ≤ 2 := by
  have hm : (4 : ℝ) ≤ m := by exact_mod_cast hS.four_le_m
  have hℓ : (2 : ℝ) ≤ ℓ := hS.two_le_ℓ
  have hμ := hS.mu_le
  have hμ0 : 0 ≤ (m : ℝ) / (ℓ * n) := by positivity
  unfold XS
  rw [mean_of_mem_OmS hs] at hv ⊢
  have hmean : 0 < (m : ℝ) / ℓ := by positivity
  have hpos : 0 < (m : ℝ) / ℓ * (1 - m / (ℓ * n)) := mul_pos hmean (by linarith)
  have h0 : 0 ≤ var s / (m / ℓ * (1 - m / (ℓ * n))) := div_nonneg (var_nonneg s) hpos.le
  have h3 : var s / (m / ℓ * (1 - m / (ℓ * n))) ≤ 3 := by
    rw [div_le_iff₀ hpos]; nlinarith
  rw [abs_le]; constructor <;> linarith

theorem abs_Htilde_sub_one_le {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {x : (Fin ℓ → ℕ) × (Fin n → ℕ)} (hx : x ∈ WsetB φ ℓ n m) :
    |Htilde x.1 x.2 - 1| ≤ 4 * (|XS ℓ n m x.1| * |XS n ℓ m x.2|) := by
  obtain ⟨hs, ht⟩ := mem_product.1 hx
  obtain ⟨hs', hvs⟩ := mem_GoodS.1 hs
  obtain ⟨ht', hvt⟩ := mem_GoodS.1 ht
  have hsO := SprS_subset_OmS hs'
  have htO := SprS_subset_OmS ht'
  rw [Htilde_eq (mem_OmS.1 hsO).2 (mem_OmS.1 htO).2]
  have hXs := XS_bounds hS hsO hvs
  have hXt := XS_bounds hS.swap htO hvt
  have he : exp 2 ≤ 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hz : |-(1 / 2) * XS ℓ n m x.1 * XS n ℓ m x.2| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [abs_nonneg (XS ℓ n m x.1), abs_nonneg (XS n ℓ m x.2)]
  calc |exp (-(1 / 2) * XS ℓ n m x.1 * XS n ℓ m x.2) - 1|
      ≤ exp 2 * |-(1 / 2) * XS ℓ n m x.1 * XS n ℓ m x.2| := abs_exp_sub_one_le_two hz
    _ = exp 2 * (1 / 2) * (|XS ℓ n m x.1| * |XS n ℓ m x.2|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring
    _ ≤ 8 * (1 / 2) * (|XS ℓ n m x.1| * |XS n ℓ m x.2|) := by gcongr
    _ = _ := by ring

theorem Htilde_pos (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : 0 < Htilde s t := exp_pos _

/-- `P_{ℬ_m}(W) ≥ 1 - 5/√ℓ - 5/√n`. -/
theorem probB_W_ge {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ ≤ 1) {m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) (hK : 2 / (2 * φ - 1) ≤ K) :
    1 - (5 / √ℓ + 5 / √n) ≤ ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 := by
  have hne := Gm_nonempty (m := m) (ℓ := ℓ) (n := n) (by have := hS.two_mul_le; omega)
  have h := sum_probB_mul (ℓ := ℓ) (n := n) m (A := GoodS φ ℓ n m) (B := GoodS φ n ℓ m)
    (GoodS_subset_SprS.trans SprS_subset_OmS) (GoodS_subset_SprS.trans SprS_subset_OmS)
    (fun _ => 1) (fun _ => 1)
  simp only [mul_one] at h
  rw [WsetB, h, ← prob_mem_eq_sum, ← prob_mem_eq_sum]
  have hp := prob_good_ge hφ₁ hφ₂ hS hK
  have hq := prob_good_ge' hφ₁ hφ₂ hS hK
  have hp1 := prob_le_one (Gm ℓ n m) (fun E => ldeg E ∈ GoodS φ ℓ n m)
  have hq1 := prob_le_one (Gm ℓ n m) (fun E => rdeg E ∈ GoodS φ n ℓ m)
  nlinarith

theorem probB_W_le {φ : ℝ} {m : ℕ} (hm : m ≤ ℓ * n) :
    ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 ≤ 1 := by
  rw [← sum_probB hm]
  exact sum_le_sum_of_subset_of_nonneg (WsetB_subset_DsetB.trans DsetB_subset_OmegaB)
    fun x _ _ => probB_nonneg _ _ _

/-- `P_𝒢(𝔇 \ W)`-type bound on the graph side: `P_{𝒟(𝒢)}(W) ≥ 1 - 5/√ℓ - 5/√n`. -/
theorem probG_W_ge {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ ≤ 1) {m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) (hK : 2 / (2 * φ - 1) ≤ K) :
    1 - (5 / √ℓ + 5 / √n) ≤ ∑ x ∈ WsetB φ ℓ n m, probG ℓ n m x.1 x.2 := by
  have hne := Gm_nonempty (m := m) (ℓ := ℓ) (n := n) (by have := hS.two_mul_le; omega)
  rw [sum_congr rfl fun x _ => probG_eq m x, ← prob_mem_eq_sum]
  have hp := prob_good_ge hφ₁ hφ₂ hS hK
  have hq := prob_good_ge' hφ₁ hφ₂ hS hK
  have h1 : prob (Gm ℓ n m) (fun E => ¬ degPair E ∈ WsetB φ ℓ n m) ≤
      prob (Gm ℓ n m) (fun E => ¬ ldeg E ∈ GoodS φ ℓ n m) +
        prob (Gm ℓ n m) (fun E => ¬ rdeg E ∈ GoodS φ n ℓ m) := by
    refine le_trans (prob_mono _ ?_) (prob_or_le _ _ _)
    intro E _ h
    by_contra hc
    push Not at hc
    exact h (mem_product.2 ⟨hc.1, hc.2⟩)
  rw [prob_not' _ _ hne, prob_not' _ _ hne, prob_not' _ _ hne] at h1
  linarith

/-- `E_{ℬ_m}(1_W H̃) = 1 + O(1/√ℓ + 1/√n)`. -/
theorem expect_W {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ ≤ 1) {m : ℕ} {K B : ℝ}
    (hS : Sizes ℓ n m K B) (hK : 2 / (2 * φ - 1) ≤ K) :
    |∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * Htilde x.1 x.2 - 1| ≤
      50 * (1 / √ℓ + 1 / √n) := by
  have hℓ : 2 ≤ ℓ := by exact_mod_cast hS.two_le_ℓ
  have hn : 2 ≤ n := by exact_mod_cast hS.two_le_n
  have hm := hS.four_le_m
  have hmN : m + 1 ≤ ℓ * n := by have := hS.two_mul_le; omega
  have hsub : GoodS φ ℓ n m ⊆ OmS ℓ n m := GoodS_subset_SprS.trans SprS_subset_OmS
  have hsub' : GoodS φ n ℓ m ⊆ OmS n ℓ m := GoodS_subset_SprS.trans SprS_subset_OmS
  set PW := ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 with hPW
  have hPW1 := probB_W_ge hφ₁ hφ₂ hS hK
  have hPW2 := probB_W_le (φ := φ) (by omega : m ≤ ℓ * n)
  have hsℓ : 0 < √(ℓ : ℝ) := sqrt_pos.2 (by exact_mod_cast (by omega : 0 < ℓ))
  have hsn : 0 < √(n : ℝ) := sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  -- the fluctuation term
  have hfl : |∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * (Htilde x.1 x.2 - 1)| ≤
      64 / (√ℓ * √n) := by
    calc |∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * (Htilde x.1 x.2 - 1)|
        ≤ ∑ x ∈ WsetB φ ℓ n m, |probB ℓ n m x.1 x.2 * (Htilde x.1 x.2 - 1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ WsetB φ ℓ n m,
            probB ℓ n m x.1 x.2 * (4 * (|XS ℓ n m x.1| * |XS n ℓ m x.2|)) := by
          refine sum_le_sum fun x hx => ?_
          rw [abs_mul, abs_of_nonneg (probB_nonneg _ _ _)]
          exact mul_le_mul_of_nonneg_left (abs_Htilde_sub_one_le hS hx) (probB_nonneg _ _ _)
      _ = 4 * ((∑ s ∈ GoodS φ ℓ n m, prob (Gm ℓ n m) (ldeg · = s) * |XS ℓ n m s|) *
            ∑ t ∈ GoodS φ n ℓ m, prob (Gm ℓ n m) (rdeg · = t) * |XS n ℓ m t|) := by
          rw [WsetB, ← sum_probB_mul m hsub hsub', mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ 4 * (4 / √ℓ * (4 / √n)) := by
          gcongr
          · exact sum_nonneg fun s _ => mul_nonneg (prob_nonneg _ _) (abs_nonneg _)
          · exact sum_prob_abs_XS_le hℓ (by omega) hm hS.six_le hmN hsub
          · exact sum_prob_abs_XT_le (by omega) hn hm hS.six_le hmN hsub'
      _ = 64 / (√ℓ * √n) := by field_simp; norm_num
  have hamgm : 64 / (√ℓ * √n) ≤ 32 * (1 / √ℓ + 1 / √n) := by
    rw [div_le_iff₀ (mul_pos hsℓ hsn)]
    have h1 : 1 ≤ √(ℓ : ℝ) := by
      rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ ℓ))
    have h2 : 1 ≤ √(n : ℝ) := by
      rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
    have : (1 / √ℓ + 1 / √n) * (√ℓ * √n) = √n + √ℓ := by field_simp
    rw [mul_assoc, this]
    nlinarith [sq_nonneg (√(ℓ : ℝ) - √n)]
  have hsplit : ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * Htilde x.1 x.2 - 1 =
      (∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * (Htilde x.1 x.2 - 1)) + (PW - 1) := by
    have : ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * (Htilde x.1 x.2 - 1) =
        ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * Htilde x.1 x.2 -
          ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun x _ => by ring
    rw [this, hPW]; ring
  rw [hsplit]
  have hPWabs : |PW - 1| ≤ 5 / √ℓ + 5 / √n := by
    rw [abs_le]; constructor <;> linarith
  calc |(∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * (Htilde x.1 x.2 - 1)) + (PW - 1)|
      ≤ |∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * (Htilde x.1 x.2 - 1)| + |PW - 1| :=
        abs_add_le _ _
    _ ≤ 32 * (1 / √ℓ + 1 / √n) + (5 / √ℓ + 5 / √n) := by linarith
    _ ≤ 50 * (1 / √ℓ + 1 / √n) := by
        have : 0 ≤ 1 / √(ℓ : ℝ) := by positivity
        have : 0 ≤ 1 / √(n : ℝ) := by positivity
        have e1 : 5 / √(ℓ : ℝ) = 5 * (1 / √ℓ) := by ring
        have e2 : 5 / √(n : ℝ) = 5 * (1 / √n) := by ring
        rw [e1, e2]; nlinarith

end LW.Bip
