import MajorityDynamics.Literature.LWFormal.Approx
import MajorityDynamics.Literature.LWFormal.SecondMoment
import MajorityDynamics.Literature.LWFormal.HRatio
import MajorityDynamics.Literature.LWFormal.Shift

set_option autoImplicit true

/-!
# Assembly of Theorem 1.4: Lemma 2.1, the spaces `𝒮`, `𝒮'`, and the remaining estimates of §7
-/

namespace LW

open Finset Real Filter

variable {n : ℕ}

/-- A walk `u = p 0, …, p k = v` of length `k ≤ r` inside `W` along `E`. -/
def HasWalk {X : Type*} (E : X → X → Prop) (W : Finset X) (r : ℕ) (u v : X) : Prop :=
  ∃ k ≤ r, ∃ p : Fin (k + 1) → X, p 0 = u ∧ p (Fin.last k) = v ∧ (∀ i, p i ∈ W) ∧
    ∀ i : Fin k, E (p i.castSucc) (p i.succ)

/-- A function whose increments along edges of `W` are at most `δ` varies by at most `rδ`
along a walk of length `≤ r`. -/
theorem HasWalk.abs_sub_le {X : Type*} {E : X → X → Prop} {W : Finset X} {r : ℕ} {u v : X}
    (h : HasWalk E W r u v) (g : X → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ x ∈ W, ∀ y ∈ W, E x y → |g x - g y| ≤ δ) : |g u - g v| ≤ r * δ := by
  obtain ⟨k, hk, p, h0, hl, hW, hE⟩ := h
  have key : ∀ j (hj : j ≤ k), |g (p 0) - g (p ⟨j, by omega⟩)| ≤ j * δ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hg _ (hW _) _ (hW _) (hE ⟨j, by omega⟩)
      simp only [Fin.castSucc_mk, Fin.succ_mk] at h2
      calc |g (p 0) - g (p ⟨j + 1, _⟩)|
          = |(g (p 0) - g (p ⟨j, by omega⟩)) + (g (p ⟨j, by omega⟩) - g (p ⟨j + 1, _⟩))| := by
            ring_nf
        _ ≤ j * δ + δ := (abs_add_le _ _).trans (add_le_add h1 h2)
        _ = (j + 1 : ℕ) * δ := by push_cast; ring
  have := key k le_rfl
  rw [h0] at this
  rw [show (Fin.last k) = ⟨k, by omega⟩ from rfl] at hl
  rw [hl] at this
  exact this.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hδ)

/-- `-log(1 - x) ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem neg_log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : -log (1 - x) ≤ 2 * x := by
  have hx : 0 < 1 - x := by linarith
  have := log_le_sub_one_of_pos (inv_pos.2 hx)
  rw [log_inv] at this
  have : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [inv_eq_one_div, div_sub_one hx.ne', div_le_iff₀ hx]; nlinarith
  linarith

/-- Lemma 2.1, with explicit constants: `P'(v) = e^{±(rδ + 2ε₀)} P(v)` on `W`; the walks may
use a larger set `W₂ ⊆ Ω` on which the edge estimate holds. -/
theorem lemma_2_1' {X : Type*} (Ω W W₂ : Finset X) (hWW₂ : W ⊆ W₂) (hW₂Ω : W₂ ⊆ Ω) (P P' : X → ℝ)
    (hP : ∀ x ∈ Ω, 0 ≤ P x) (hP' : ∀ x ∈ Ω, 0 ≤ P' x)
    (hP1 : ∑ x ∈ Ω, P x = 1) (hP'1 : ∑ x ∈ Ω, P' x = 1)
    (hpos : ∀ v ∈ W₂, 0 < P v ∧ 0 < P' v)
    (ε₀ δ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hW : 1 - ε₀ ≤ ∑ v ∈ W, P v) (hW' : 1 - ε₀ ≤ ∑ v ∈ W, P' v)
    (E : X → X → Prop)
    (hedge : ∀ u ∈ W₂, ∀ v ∈ W₂, E u v → |log (P' u / P' v) - log (P u / P v)| ≤ δ)
    (r : ℕ) (hdiam : ∀ u ∈ W, ∀ v ∈ W, HasWalk E W₂ r u v) :
    ∀ v ∈ W, |log (P' v / P v)| ≤ r * δ + 2 * ε₀ := by
  intro v hv
  have hWΩ : W ⊆ Ω := hWW₂.trans hW₂Ω
  set g : X → ℝ := fun x => log (P' x / P x) with hg
  have hgE : ∀ x ∈ W₂, ∀ y ∈ W₂, E x y → |g x - g y| ≤ δ := fun x hx y hy hxy => by
    obtain ⟨hPx, hP'x⟩ := hpos x hx
    obtain ⟨hPy, hP'y⟩ := hpos y hy
    have := hedge x hx y hy hxy
    rw [log_div hP'x.ne' hP'y.ne', log_div hPx.ne' hPy.ne'] at this
    simp only [hg, log_div hP'x.ne' hPx.ne', log_div hP'y.ne' hPy.ne']
    convert this using 2; ring
  have hWne : W.Nonempty := ⟨v, hv⟩
  obtain ⟨u₀, hu₀, hmin⟩ := W.exists_min_image g hWne
  obtain ⟨u₁, hu₁, hmax⟩ := W.exists_max_image g hWne
  have hPW1 : ∑ x ∈ W, P x ≤ 1 := hP1 ▸ sum_le_sum_of_subset_of_nonneg hWΩ fun x hx _ => hP x hx
  have hP'W1 : ∑ x ∈ W, P' x ≤ 1 :=
    hP'1 ▸ sum_le_sum_of_subset_of_nonneg hWΩ fun x hx _ => hP' x hx
  have hε₀1 : 0 < 1 - ε₀ := by linarith
  have hexp : ∀ x ∈ W, P' x = P x * exp (g x) := fun x hx => by
    obtain ⟨hPx, hP'x⟩ := hpos x (hWW₂ hx)
    rw [hg]; simp only; rw [exp_log (div_pos hP'x hPx)]; field_simp
  have hL : -(2 * ε₀) ≤ g u₁ := by
    -- `P'(W) ≤ e^{g_max} P(W)`
    have : ∑ x ∈ W, P' x ≤ exp (g u₁) * ∑ x ∈ W, P x := by
      rw [mul_sum]
      exact sum_le_sum fun x hx => by
        rw [hexp x hx, mul_comm]
        exact mul_le_mul_of_nonneg_right (exp_le_exp.2 (hmax x hx)) (hP x (hWΩ hx))
    have h1 : 1 - ε₀ ≤ exp (g u₁) := by
      calc 1 - ε₀ ≤ ∑ x ∈ W, P' x := hW'
        _ ≤ exp (g u₁) * ∑ x ∈ W, P x := this
        _ ≤ exp (g u₁) * 1 := mul_le_mul_of_nonneg_left hPW1 (exp_pos _).le
        _ = _ := mul_one _
    have := (log_le_log_iff hε₀1 (exp_pos _)).2 h1
    rw [log_exp] at this
    linarith [neg_log_one_sub_le hε₀ hε₀']
  have hU : g u₀ ≤ 2 * ε₀ := by
    -- `e^{g_min} P(W) ≤ P'(W)`
    have : exp (g u₀) * ∑ x ∈ W, P x ≤ ∑ x ∈ W, P' x := by
      rw [mul_sum]
      exact sum_le_sum fun x hx => by
        rw [hexp x hx, mul_comm]
        exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (hmin x hx)) (hP x (hWΩ hx))
    have h1 : exp (g u₀) ≤ (1 - ε₀)⁻¹ := by
      rw [le_inv_comm₀ (exp_pos _) hε₀1, inv_eq_one_div, le_div_iff₀ (exp_pos _)]
      calc (1 - ε₀) * exp (g u₀) ≤ exp (g u₀) * ∑ x ∈ W, P x := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hW (exp_pos _).le
        _ ≤ ∑ x ∈ W, P' x := this
        _ ≤ 1 := hP'W1
    have := (log_le_log_iff (exp_pos _) (inv_pos.2 hε₀1)).2 h1
    rw [log_exp, log_inv] at this
    linarith [neg_log_one_sub_le hε₀ hε₀']
  have h₀ := (hdiam v hv u₀ hu₀).abs_sub_le g hδ hgE
  have h₁ := (hdiam v hv u₁ hu₁).abs_sub_le g hδ hgE
  rw [abs_le] at h₀ h₁ ⊢
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]

/-- Lemma 2.1 with the ideal measure given as an unnormalised positive weight `h` on `W₂` and
an abstract walk bound `ρ` (e.g. `r₁δ₁ + r₂δ₂` for two edge types) from any point of `W₂` into
`W`: `P'(v) = e^{±(ρ + 2ε₀)} h(v) / h(W)` on `W₂`. -/
theorem lemma_2_1_h {X : Type*} (Ω W W₂ : Finset X) (hWW₂ : W ⊆ W₂) (hW₂Ω : W₂ ⊆ Ω)
    (h P' : X → ℝ) (hP' : ∀ x ∈ Ω, 0 ≤ P' x) (hP'1 : ∑ x ∈ Ω, P' x = 1)
    (hpos : ∀ v ∈ W₂, 0 < h v ∧ 0 < P' v)
    (ε₀ ρ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1 / 2)
    (hW' : 1 - ε₀ ≤ ∑ v ∈ W, P' v)
    (hwalk : ∀ g : X → ℝ, (∀ x ∈ W₂, ∀ y ∈ W₂, g x - g y = log (P' x / P' y) - log (h x / h y)) →
      ∀ u ∈ W₂, ∀ v ∈ W, |g u - g v| ≤ ρ) :
    ∀ v ∈ W₂, |log (P' v / h v) + log (∑ x ∈ W, h x)| ≤ ρ + 2 * ε₀ := by
  intro v hv
  have hWΩ : W ⊆ Ω := hWW₂.trans hW₂Ω
  have hWne : W.Nonempty := by
    rw [nonempty_iff_ne_empty]; rintro rfl; simp at hW'; linarith
  set g : X → ℝ := fun x => log (P' x / h x) with hg
  set Z := ∑ x ∈ W, h x with hZ
  have hgE : ∀ x ∈ W₂, ∀ y ∈ W₂, g x - g y = log (P' x / P' y) - log (h x / h y) :=
    fun x hx y hy => by
      obtain ⟨hPx, hP'x⟩ := hpos x hx
      obtain ⟨hPy, hP'y⟩ := hpos y hy
      rw [log_div hP'x.ne' hP'y.ne', log_div hPx.ne' hPy.ne']
      simp only [hg, log_div hP'x.ne' hPx.ne', log_div hP'y.ne' hPy.ne']
      ring
  obtain ⟨u₀, hu₀, hmin⟩ := W.exists_min_image g hWne
  obtain ⟨u₁, hu₁, hmax⟩ := W.exists_max_image g hWne
  have hZpos : 0 < Z := sum_pos (fun x hx => (hpos x (hWW₂ hx)).1) hWne
  have hP'W1 : ∑ x ∈ W, P' x ≤ 1 :=
    hP'1 ▸ sum_le_sum_of_subset_of_nonneg hWΩ fun x hx _ => hP' x hx
  have hε₀1 : 0 < 1 - ε₀ := by linarith
  have hexp : ∀ x ∈ W, P' x = h x * exp (g x) := fun x hx => by
    obtain ⟨hPx, hP'x⟩ := hpos x (hWW₂ hx)
    rw [hg]; simp only; rw [exp_log (div_pos hP'x hPx)]; field_simp
  have hL : -(2 * ε₀) ≤ g u₁ + log Z := by
    have : ∑ x ∈ W, P' x ≤ exp (g u₁) * Z := by
      rw [hZ, mul_sum]
      exact sum_le_sum fun x hx => by
        rw [hexp x hx, mul_comm]
        exact mul_le_mul_of_nonneg_right (exp_le_exp.2 (hmax x hx)) (hpos x (hWW₂ hx)).1.le
    have h1 : 1 - ε₀ ≤ exp (g u₁) * Z := hW'.trans this
    have := (log_le_log_iff hε₀1 (by positivity)).2 h1
    rw [log_mul (exp_pos _).ne' hZpos.ne', log_exp] at this
    linarith [neg_log_one_sub_le hε₀ hε₀']
  have hU : g u₀ + log Z ≤ 2 * ε₀ := by
    have : exp (g u₀) * Z ≤ ∑ x ∈ W, P' x := by
      rw [hZ, mul_sum]
      exact sum_le_sum fun x hx => by
        rw [hexp x hx, mul_comm]
        exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (hmin x hx)) (hpos x (hWW₂ hx)).1.le
    have := (log_le_log_iff (by positivity) one_pos).2 (this.trans hP'W1)
    rw [log_mul (exp_pos _).ne' hZpos.ne', log_exp, log_one] at this
    linarith
  have h₀ := hwalk g hgE v hv u₀ hu₀
  have h₁ := hwalk g hgE v hv u₁ hu₁
  rw [abs_le] at h₀ h₁ ⊢
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]

/-- A walk of `≤ r₁` `E₁`-steps followed by `≤ r₂` `E₂`-steps bounds increments by
`r₁δ₁ + r₂δ₂`. -/
theorem two_type_walk_bound {X : Type*} {E₁ E₂ : X → X → Prop} {W₂ : Finset X} {r₁ r₂ : ℕ}
    {u v : X} (hw : ∃ w ∈ W₂, HasWalk E₁ W₂ r₁ u w ∧ HasWalk E₂ W₂ r₂ w v) (g : X → ℝ)
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hg₁ : ∀ x ∈ W₂, ∀ y ∈ W₂, E₁ x y → |g x - g y| ≤ δ₁)
    (hg₂ : ∀ x ∈ W₂, ∀ y ∈ W₂, E₂ x y → |g x - g y| ≤ δ₂) :
    |g u - g v| ≤ r₁ * δ₁ + r₂ * δ₂ := by
  obtain ⟨w, -, h1, h2⟩ := hw
  have := h1.abs_sub_le g hδ₁ hg₁
  have := h2.abs_sub_le g hδ₂ hg₂
  calc |g u - g v| = |(g u - g w) + (g w - g v)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

theorem lemma_2_1 {X : Type*} (Ω W : Finset X) (hWΩ : W ⊆ Ω) (P P' : X → ℝ)
    (hP : ∀ x ∈ Ω, 0 ≤ P x) (hP' : ∀ x ∈ Ω, 0 ≤ P' x)
    (hP1 : ∑ x ∈ Ω, P x = 1) (hP'1 : ∑ x ∈ Ω, P' x = 1)
    (hpos : ∀ v ∈ W, 0 < P v ∧ 0 < P' v)
    (ε₀ δ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hW : 1 - ε₀ ≤ ∑ v ∈ W, P v) (hW' : 1 - ε₀ ≤ ∑ v ∈ W, P' v)
    (E : X → X → Prop)
    (hedge : ∀ u ∈ W, ∀ v ∈ W, E u v → |log (P' u / P' v) - log (P u / P v)| ≤ δ)
    (r : ℕ) (hdiam : ∀ u ∈ W, ∀ v ∈ W, HasWalk E W r u v) :
    ∀ v ∈ W, |log (P' v / P v)| ≤ r * δ + 2 * ε₀ :=
  lemma_2_1' Ω W W subset_rfl hWΩ P P' hP hP' hP1 hP'1 hpos ε₀ δ hε₀ hε₀' hδ hW hW' E hedge r hdiam

/-- The common underlying set `Ω` of `ℬ_m(n)` and `𝒟(𝒢(n,m))`: `dᵢ ≤ n - 1`, `∑ dᵢ = 2m`. -/
def OmegaNM (n m : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => range n).filter fun d => ∑ i, d i = 2 * m

theorem mem_OmegaNM {n m : ℕ} {d : Fin n → ℕ} :
    d ∈ OmegaNM n m ↔ (∀ i, d i < n) ∧ ∑ i, d i = 2 * m := by
  simp [OmegaNM, Fintype.mem_piFinset]

/-- The pushforward of the uniform measure along `f : Ω → T` has total mass one. -/
theorem sum_prob_eq_one {X Y : Type*} [DecidableEq Y] (Ω : Finset X) (f : X → Y) (T : Finset Y)
    (hΩ : Ω.Nonempty) (hf : ∀ x ∈ Ω, f x ∈ T) : ∑ t ∈ T, prob Ω (f · = t) = 1 := by
  simp only [prob]
  rw [← sum_div, ← Nat.cast_sum, ← card_eq_sum_card_fiberwise hf, div_self]
  exact_mod_cast (card_pos.2 hΩ).ne'

theorem pairDeg_mem_OmegaNM {n m : ℕ} {S : Finset (Fin n × Fin n)} (hS : S ∈ Bm n m) :
    pairDeg S ∈ OmegaNM n m := by
  rw [Bm, mem_powersetCard] at hS
  refine mem_OmegaNM.2 ⟨fun i => ?_, by rw [← card_eq_sum_pairDeg, hS.2]⟩
  rw [← card_fibres]
  calc (fibres S i).card ≤ (univ.erase i).card :=
        card_le_card fun j hj => by
          have := hS.1 (mem_fibres.1 hj)
          simp only [allPairs, mem_filter, mem_univ, true_and] at this
          exact mem_erase.2 ⟨fun h => this (h ▸ rfl), mem_univ _⟩
    _ < n := by
        rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
        exact Nat.sub_lt (Fin.pos i) one_pos

theorem sum_probBinom (n m : ℕ) (hm : 2 * m ≤ n * (n - 1)) :
    ∑ d ∈ OmegaNM n m, probBinom n m d = 1 := by
  rw [sum_congr rfl fun d hd => probBinom_eq n m d (mem_OmegaNM.1 hd).2]
  refine sum_prob_eq_one _ _ _ (card_pos.1 ?_) fun S hS => pairDeg_mem_OmegaNM hS
  rw [card_Bm]; exact Nat.choose_pos hm

theorem degSeq_mem_OmegaNM {n m : ℕ} {E : Graph n} (hE : E ∈ Gnm n m) :
    degSeq E ∈ OmegaNM n m := by
  rw [Gnm_eq, mem_filter] at hE
  obtain ⟨-, hs, hc⟩ := hE
  refine mem_OmegaNM.2 ⟨fun i => ?_, by rw [degSeq, sum_deg_eq hs, hc]⟩
  rw [degSeq, ← card_nbrs hs]
  calc (nbrs E i).card ≤ (univ.erase i).card :=
        card_le_card fun j hj => by
          simp only [nbrs, mem_filter, mem_univ, true_and] at hj
          exact mem_erase.2 ⟨fun h => hs _ hj (by simp [h]), mem_univ _⟩
    _ < n := by
        rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
        exact Nat.sub_lt (Fin.pos i) one_pos

theorem sum_probGnm (n m : ℕ) (hm : 2 * m ≤ n * (n - 1)) :
    ∑ d ∈ OmegaNM n m, probGnm n m d = 1 := by
  refine sum_prob_eq_one _ _ _ (card_pos.1 ?_) fun E hE => degSeq_mem_OmegaNM hE
  rw [Gnm, card_powersetCard]
  exact Nat.choose_pos (by have := two_mul_card_allEdges n; omega)

def toZ (d : Fin n → ℕ) : Seq n := fun i => (d i : ℤ)

def toN (d : Seq n) : Fin n → ℕ := fun i => (d i).toNat

/-- `𝔇` as a finset of `ℕ`-sequences. -/
noncomputable def DsetN (α : ℝ) (n m : ℕ) : Finset (Fin n → ℕ) :=
  open Classical in (OmegaNM n m).filter fun d => toZ d ∈ Dset α n m

/-- `H(d) = P_{ℬ_m}(d) H̃(d)`, the conjectured formula, on integer sequences. -/
noncomputable def H (n m : ℕ) (d : Seq n) : ℝ := probBinom n m (toN d) * expFactor (toN d)

/-- `ξ = (log n)²/√n`. -/
noncomputable def xi (n : ℕ) : ℝ := log n ^ 2 / √n

theorem mem_DsetN {α : ℝ} {n m : ℕ} {d : Fin n → ℕ} :
    d ∈ DsetN α n m ↔ d ∈ OmegaNM n m ∧ toZ d ∈ Dset α n m := by
  classical
  unfold DsetN; exact mem_filter

theorem two_mul_le_of_eight_mul_le {n m : ℕ} (hn : 4 ≤ n) (hm : 8 * m ≤ n * n) :
    2 * m ≤ n * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 by omega]; nlinarith

/-- Theorem 6.3(a), abstractly: a union bound over the per-vertex hypergeometric tails. -/
theorem prob_Dset_of_tail {X : Type*} [DecidableEq X] {n m : ℕ} (Ω : Finset X) (hΩ : Ω.Nonempty)
    (f : X → Fin n → ℕ) (hf : ∀ x ∈ Ω, f x ∈ OmegaNM n m) {α : ℝ} (hα₁ : 1 / 2 < α)
    (hα₂ : α ≤ 1) (hn : 4 ≤ n) (hlog : 192 ≤ log n)
    (h1 : log n ^ (2 / (2 * α - 1)) ≤ 2 * m / n) (h2 : (2 * m / n : ℝ) ≤ n)
    (htail : ∀ i (t : ℝ), 6 ≤ t → t ≤ 2 * m / n →
      prob Ω (fun x => t < |(f x i : ℝ) - 2 * m / n|) ≤
        2 * (2 * m / n + 1) * exp (-t ^ 2 / (32 * (2 * m / n)))) :
    1 - 1 / (n : ℝ) ^ 2 ≤ ∑ d ∈ DsetN α n m, prob Ω (f · = d) := by
  obtain ⟨h6, htd, hnum⟩ := tail_numeric hα₁ hα₂ hn hlog h1
    (h2.trans (le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ n)) two_ne_zero))
  rw [← prob_mem_eq_sum]
  calc (1 : ℝ) - 1 / (n : ℝ) ^ 2
      ≤ 1 - n * (2 * (2 * m / n + 1) * exp (-((2 * m / n : ℝ) ^ α) ^ 2 / (32 * (2 * m / n)))) := by
        linarith
    _ ≤ prob Ω (fun x => ∀ i, |(f x i : ℝ) - 2 * m / n| ≤ (2 * m / n : ℝ) ^ α) :=
        prob_forall_ge Ω hΩ f _ _ _ fun i => htail i _ h6 htd
    _ ≤ prob Ω (fun x => f x ∈ DsetN α n m) := prob_mono Ω fun x hx h => ?_
  have hx := hf x hx
  rw [mem_DsetN]
  refine ⟨hx, fun i => Int.natCast_nonneg _, ?_, fun i => by simpa [toZ] using h i⟩
  have := (mem_OmegaNM.1 hx).2
  simp only [M1, toZ]; exact_mod_cast this

/-- The `(n, m)`-range needed for Theorem 6.3(a), for `n` large. -/
theorem eventually_tail (α : ℝ) {ω : ℕ → ℝ} (hω : Tendsto ω atTop atTop) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω (1 / 8) n m →
      4 ≤ n ∧ 192 ≤ log n ∧ 8 * m ≤ n * n ∧
        log n ^ (2 / (2 * α - 1)) ≤ 2 * m / n ∧ (2 * m / n : ℝ) ≤ n := by
  have hL : ∀ᶠ n : ℕ in atTop, (192 : ℝ) ≤ log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hω' : ∀ᶠ n : ℕ in atTop, 2 / (2 * α - 1) ≤ ω n := hω.eventually (eventually_ge_atTop _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_ge_atTop 4).and (hL.and hω'))
  refine ⟨N, fun n hn m hR => ?_⟩
  obtain ⟨hn4, hlog, hω⟩ := hN n hn
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hm : 8 * m ≤ n * n := by
    have h := hR.2
    rw [div_le_iff₀ (by linarith)] at h
    have : (8 * m : ℝ) ≤ n * n := by nlinarith
    exact_mod_cast this
  exact ⟨hn4, hlog, hm,
    (rpow_le_rpow_of_exponent_le (by linarith) hω).trans hR.1, hR.2.trans (by linarith)⟩

/-- Theorem 6.3(a) analogue for `𝒢(n,m)`: `P(𝔇) ≥ 1 - n⁻²`. -/
theorem prob_Dset_G :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω μ₀ n m →
          1 - 1 / (n : ℝ) ^ 2 ≤ ∑ d ∈ DsetN α n m, probGnm n m d := by
  refine ⟨1 / 8, by norm_num, fun α hα₁ hα₂ ω hω => ?_⟩
  obtain ⟨N, hN⟩ := eventually_tail α hω
  refine ⟨N, fun n hn m hR => ?_⟩
  obtain ⟨hn4, hlog, hm, h1, h2⟩ := hN n hn m hR
  have hΩ : (Gnm n m).Nonempty := by
    refine card_pos.1 ?_
    rw [Gnm, card_powersetCard]
    exact Nat.choose_pos (by have := two_mul_card_allEdges n
                             have := two_mul_le_of_eight_mul_le hn4 hm; omega)
  exact prob_Dset_of_tail (Gnm n m) hΩ degSeq (fun E hE => degSeq_mem_OmegaNM hE) hα₁
    (by linarith) hn4 hlog h1 h2 fun i t ht htμ => deg_tail_G n m hn4 hm i ht htμ

/-- Theorem 6.3(a) analogue for `ℬ_m(n)`: `P(𝔇) ≥ 1 - n⁻²`. -/
theorem prob_Dset_B :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω μ₀ n m →
          1 - 1 / (n : ℝ) ^ 2 ≤ ∑ d ∈ DsetN α n m, probBinom n m d := by
  refine ⟨1 / 8, by norm_num, fun α hα₁ hα₂ ω hω => ?_⟩
  obtain ⟨N, hN⟩ := eventually_tail α hω
  refine ⟨N, fun n hn m hR => ?_⟩
  obtain ⟨hn4, hlog, hm, h1, h2⟩ := hN n hn m hR
  have hΩ : (Bm n m).Nonempty := by
    refine card_pos.1 ?_
    rw [Bm, card_powersetCard, card_allPairs]
    exact Nat.choose_pos (two_mul_le_of_eight_mul_le hn4 hm)
  rw [sum_congr rfl fun d hd =>
    probBinom_eq n m d (mem_OmegaNM.1 (mem_DsetN.1 hd).1).2]
  exact prob_Dset_of_tail (Bm n m) hΩ pairDeg (fun S hS => pairDeg_mem_OmegaNM hS) hα₁
    (by linarith) hn4 hlog h1 h2 fun i t ht htμ => deg_tail_B n m hn4 hm i ht htμ

/-- (6.8): `E_{ℬ_m} H̃ = 1 + O(ξ)`. -/
theorem expect_Htilde :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
      ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω μ₀ n m →
        |∑ d ∈ OmegaNM n m, probBinom n m d * expFactor d - 1| ≤ C * xi n := by
  refine ⟨1 / 8, by norm_num, fun ω hω => ⟨18, ?_⟩⟩
  have hL : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hω' : ∀ᶠ n : ℕ in atTop, 0 ≤ ω n := hω.eventually (eventually_ge_atTop _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_ge_atTop 3).and (hL.and hω'))
  refine ⟨N, fun n hn m hR => ?_⟩
  obtain ⟨hn3, hlog, hω0⟩ := hN n hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have h1 : (1 : ℝ) ≤ 2 * m / n := (one_le_rpow hlog hω0).trans hR.1
  have hnm : (n : ℝ) ≤ 2 * m := by rwa [le_div_iff₀ (by linarith), one_mul] at h1
  have h16 : 16 * (m : ℝ) ≤ n * n := by
    have := hR.2; rw [div_le_iff₀ (by linarith)] at this; nlinarith
  have hm2 : 2 ≤ m := by
    have : n ≤ 2 * m := by exact_mod_cast hnm
    omega
  have hmN : 2 * m + 1 < n * (n - 1) := by
    have hn8 : (8 : ℝ) ≤ n := by nlinarith
    have : (2 * m + 1 : ℝ) < n * ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; nlinarith
    exact_mod_cast this
  rw [sum_congr rfl fun d hd => by rw [probBinom_eq n m d (mem_OmegaNM.1 hd).2],
    sum_prob_mul (Bm n m) pairDeg (OmegaNM n m) expFactor fun S hS => pairDeg_mem_OmegaNM hS]
  have h := abs_expect_expFactor_sub_one_le n m hn3 hm2 hmN
  rw [← sum_div] at h
  refine h.trans ?_
  unfold xi
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (one_le_pow₀ hlog) (sqrt_nonneg _)) (by norm_num)

/-! ### (6.10): the exact ratio `H(d - e_a)/H(d - e_b)` -/

theorem toN_cast {d : Seq n} (h : ∀ i, 0 ≤ d i) (i : Fin n) : ((toN d i : ℕ) : ℝ) = (d i : ℝ) := by
  rw [toN, ← Int.cast_natCast, Int.toNat_of_nonneg (h i)]

theorem avgDeg_toN {d : Seq n} (h : ∀ i, 0 ≤ d i) : avgDeg (toN d) = dbar d := by
  simp only [avgDeg, dbar, M1_cast, toN_cast h]

theorem gamma2_toN {d : Seq n} (h : ∀ i, 0 ≤ d i) (hn : (n : ℝ) ≠ 0) :
    gamma2 (toN d) = n * sigma2 d / ((n : ℝ) - 1) ^ 2 := by
  simp only [gamma2, avgDeg_toN h, toN_cast h, sigma2]
  rw [mul_div_cancel₀ _ hn]

theorem choose_pred_div (N : ℕ) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ((N.choose (k - 1) : ℕ) : ℝ) / N.choose k = k / ((N : ℝ) + 1 - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h0 : (N.choose (j + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkN).ne'
  have h1 : (N : ℝ) + 1 - ((j + 1 : ℕ) : ℝ) ≠ 0 := by
    have : (j + 1 : ℝ) ≤ N := by exact_mod_cast hkN
    push_cast; linarith
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq N j)
  push_cast [Nat.cast_sub (by omega : j ≤ N)] at h
  rw [Nat.add_sub_cancel, div_eq_div_iff h0 h1]
  push_cast
  linear_combination (-1 : ℝ) * h

/-- The exact ratio `H(d - e_a)/H(d - e_b)` for `∑ dᵢ = 2m + 1`, in the form of `hratio_real`. -/
theorem H_ratio_eq {m : ℕ} {d : Seq n} (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hmn : 2 * m < n * (n - 1))
    (hM : M1 d = 2 * m + 1) (hd1 : ∀ i, (1 : ℝ) ≤ d i) (hdn : ∀ i, (d i : ℝ) < n) (a b : Fin n) :
    H n m (d - e a) / H n m (d - e b) =
      (d a : ℝ) / d b * ((n - d b) / (n - d a)) *
        exp (Eexp n (2 * m / n) (d a) (d b) (∑ i, ((d i : ℝ) - 2 * m / n) ^ 2)) := by
  set D : ℝ := 2 * m / n with hD
  have hn0 : (n : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                   linarith
  have hD0 : D ≠ 0 := by rw [hD]; have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
                         positivity
  have hT : (n : ℝ) - 1 - D ≠ 0 := by
    have : (2 * m : ℝ) < n * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hmn
    rw [Nat.cast_pred (by omega)] at this
    have : D < n - 1 := by rw [hD, div_lt_iff₀ (by positivity)]; linarith
    linarith
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    have : (1 : ℝ) ≤ d i := hd1 i
    have : (1 : ℤ) ≤ d i := by exact_mod_cast this
    omega
  have hpos : ∀ (c i : Fin n), 0 ≤ (d - e c) i := fun c i => by
    have : (1 : ℤ) ≤ d i := by exact_mod_cast hd1 i
    rw [sub_e_apply]; split_ifs <;> omega
  have hk1 : ∀ i, 1 ≤ toN d i := fun i => by
    have : (1 : ℤ) ≤ d i := by exact_mod_cast hd1 i
    simp only [toN]; omega
  have hk : ∀ i, toN d i ≤ n - 1 := fun i => by
    have : d i < (n : ℤ) := by exact_mod_cast hdn i
    simp only [toN]; omega
  have hdbar : dbar d = D + 1 / n := by rw [dbar, hM, hD]; push_cast; ring
  -- the binomial ratio
  have hprod : ∀ c, ∏ i, ((n - 1).choose (toN (d - e c) i) : ℝ) =
      ((n - 1).choose (toN d c - 1) : ℝ) / (n - 1).choose (toN d c) *
        ∏ i, ((n - 1).choose (toN d i) : ℝ) := by
    intro c
    have hne : ∀ i, i ≠ c → toN (d - e c) i = toN d i := fun i hi => by
      simp only [toN, sub_e_apply_of_ne d hi]
    have hself : toN (d - e c) c = toN d c - 1 := by
      simp only [toN, sub_e_apply, if_true, Int.pred_toNat]
    have hrest : ∏ i ∈ univ.erase c, ((n - 1).choose (toN (d - e c) i) : ℝ) =
        ∏ i ∈ univ.erase c, ((n - 1).choose (toN d i) : ℝ) :=
      prod_congr rfl fun i hi => by rw [hne i (ne_of_mem_erase hi)]
    have h0 : ((n - 1).choose (toN d c) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (hk c)).ne'
    rw [← mul_prod_erase univ (fun i => ((n - 1).choose (toN (d - e c) i) : ℝ)) (mem_univ c),
      ← mul_prod_erase univ (fun i => ((n - 1).choose (toN d i) : ℝ)) (mem_univ c), hrest, hself]
    field_simp
  have hPB : probBinom n m (toN (d - e a)) / probBinom n m (toN (d - e b)) =
      (d a : ℝ) / d b * ((n - d b) / (n - d a)) := by
    have hC : (((n * (n - 1)).choose (2 * m) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hmn.le).ne'
    have hP : ∏ i, ((n - 1).choose (toN d i) : ℝ) ≠ 0 :=
      prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (Nat.choose_pos (hk i)).ne'
    have hcast : ∀ i, ((toN d i : ℕ) : ℝ) = d i := toN_cast hd0
    have hnda : (n : ℝ) - d a ≠ 0 := by linarith [hdn a]
    have hndb : (n : ℝ) - d b ≠ 0 := by linarith [hdn b]
    have hda0 : (d a : ℝ) ≠ 0 := by linarith [hd1 a]
    have hdb0 : (d b : ℝ) ≠ 0 := by linarith [hd1 b]
    unfold probBinom
    rw [hprod a, hprod b, choose_pred_div _ (hk1 a) (hk a), choose_pred_div _ (hk1 b) (hk b),
      Nat.cast_pred (by omega), sub_add_cancel, hcast, hcast]
    field_simp
  -- the exponential ratio
  have hEF : expFactor (toN (d - e a)) / expFactor (toN (d - e b)) =
      exp (Eexp n D (d a) (d b) (∑ i, ((d i : ℝ) - D) ^ 2)) := by
    have key : ∀ i, ((d i : ℝ) - D) ^ 2 =
        ((d i : ℝ) - dbar d) ^ 2 + 2 / n * ((d i : ℝ) - dbar d) + 1 / n ^ 2 := fun i => by
      rw [hdbar]; ring
    have hS2 : ∑ i, ((d i : ℝ) - D) ^ 2 = n * sigma2 d + 1 / n := by
      simp only [key, sum_add_distrib, ← mul_sum, sum_sub_dbar d hn0, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, sigma2]
      field_simp
      ring
    unfold expFactor
    rw [← exp_sub]
    congr 1
    simp only [density, avgDeg_toN (hpos a), avgDeg_toN (hpos b), gamma2_toN (hpos a) hn0,
      gamma2_toN (hpos b) hn0, dbar_sub_e, sigma2_sub_e _ _ hn0, hdbar, add_sub_cancel_right, hS2,
      Eexp]
    field_simp
    ring
  rw [H, H, mul_div_mul_comm, hPB, hEF]

/-- (6.10) with error `O(1/n²)`: `H(d - e_a)/H(d - e_b) = R^gr_{ab}(d)(1 + O(1/n²))` on `Q₁¹`. -/
theorem H_ratio :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ ω : ℕ → ℝ, Tendsto ω atTop atTop →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ m, Range ω μ₀ n m →
          ∀ d ∈ Q1D α n m, ∀ a b,
            Close (H n m (d - e a) / H n m (d - e b)) (Rgr a b d) (C / (n : ℝ) ^ 2) := by
  refine ⟨1 / 8, by norm_num, fun α hα₁ hα₂ ω hω => ⟨5000, ?_⟩⟩
  have hL : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hω' : ∀ᶠ n : ℕ in atTop, 5 ≤ ω n := hω.eventually (eventually_ge_atTop _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_ge_atTop 256).and (hL.and hω'))
  refine ⟨N, fun n hn m hR d hd a b => ?_⟩
  obtain ⟨hn256, hlog, hω5⟩ := hN n hn
  obtain ⟨c, hc0, hcM, hcdev⟩ := hd
  set D : ℝ := 2 * m / n with hD
  have hn' : (256 : ℝ) ≤ n := by exact_mod_cast hn256
  have hD32 : 32 ≤ D := by
    have h32 : (32 : ℝ) = 2 ^ ((5 : ℕ) : ℝ) := by rw [rpow_natCast]; norm_num
    calc (32 : ℝ) = 2 ^ ((5 : ℕ) : ℝ) := h32
      _ ≤ log n ^ ((5 : ℕ) : ℝ) := rpow_le_rpow (by norm_num) hlog (by norm_num)
      _ ≤ log n ^ ω n := rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hω5)
      _ ≤ D := hR.1
  have hD0 : 0 < D := by linarith
  have hDn : 8 * D ≤ n := by have := hR.2; linarith
  set s : ℝ := D ^ α with hs
  have hs1 : 1 ≤ s := one_le_rpow (by linarith) (by linarith)
  have hsD : 4 * s ≤ D := by
    have h4 : (4 : ℝ) ≤ D ^ (2 / 5 : ℝ) := by
      rw [show (2 / 5 : ℝ) = (5 / 2 : ℝ)⁻¹ by norm_num,
        le_rpow_inv_iff_of_pos (by norm_num) hD0.le (by norm_num)]
      calc (4 : ℝ) ^ (5 / 2 : ℝ) = (2 ^ ((2 : ℕ) : ℝ)) ^ (5 / 2 : ℝ) := by
            rw [rpow_natCast]; norm_num
        _ = 2 ^ ((5 : ℕ) : ℝ) := by rw [← rpow_mul (by norm_num)]; norm_num
        _ = 32 := by rw [rpow_natCast]; norm_num
        _ ≤ D := hD32
    calc 4 * s ≤ D ^ (1 - α) * D ^ α :=
          mul_le_mul_of_nonneg_right
            (h4.trans (rpow_le_rpow_of_exponent_le (by linarith) (by linarith))) (by positivity)
      _ = D := by rw [← rpow_add hD0]; simp
  have hs3 : s ^ 3 ≤ D ^ 2 := by
    calc s ^ 3 = D ^ (α * 3) := by rw [hs, ← rpow_natCast, ← rpow_mul hD0.le]; norm_num
      _ ≤ D ^ ((2 : ℕ) : ℝ) := rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
      _ = D ^ 2 := rpow_natCast D 2
  have hdev : ∀ i, |(d i : ℝ) - D| ≤ s + 1 := fun i => by
    have h := hcdev i
    rw [sub_e_apply] at h
    push_cast at h
    have h1 : |(d i : ℝ) - D| ≤
        |(d i : ℝ) - (if i = c then 1 else 0) - D| + |(if i = c then (1 : ℝ) else 0)| := by
      calc |(d i : ℝ) - D| = |((d i : ℝ) - (if i = c then 1 else 0) - D) + (if i = c then 1 else 0)| := by
            congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have h2 : |(if i = c then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    linarith
  have hd1 : ∀ i, (1 : ℝ) ≤ d i := fun i => by linarith [abs_le.1 (hdev i)]
  have hdn : ∀ i, (d i : ℝ) < n := fun i => by linarith [abs_le.1 (hdev i)]
  have hM : M1 d = 2 * m + 1 := by have := M1_sub_e d c; omega
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by
      have := hD32; rw [hD, le_div_iff₀ (by linarith)] at this; linarith
    exact_mod_cast this
  have hmn : 2 * m < n * (n - 1) := by
    have : (2 * m : ℝ) < n * ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_pred (by omega)]
      have : (2 * m : ℝ) = D * n := by rw [hD]; field_simp
      nlinarith
    exact_mod_cast this
  set S2 : ℝ := ∑ i, ((d i : ℝ) - D) ^ 2 with hS2def
  have hS2 : 0 ≤ S2 := sum_nonneg fun i _ => sq_nonneg _
  have hS2' : S2 ≤ n * (s + 1) ^ 2 := by
    calc S2 ≤ ∑ _i : Fin n, (s + 1) ^ 2 :=
          sum_le_sum fun i _ => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdev i) 2
      _ = n * (s + 1) ^ 2 := by simp
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hdbar : dbar d = D + 1 / n := by rw [dbar, hM, hD]; push_cast; ring
  have hσ : sigma2 d = (S2 - 1 / n) / n := by
    have key : ∀ i, ((d i : ℝ) - D) ^ 2 =
        ((d i : ℝ) - dbar d) ^ 2 + 2 / n * ((d i : ℝ) - dbar d) + 1 / n ^ 2 := fun i => by
      rw [hdbar]; ring
    rw [hS2def]
    simp only [key, sum_add_distrib, ← mul_sum, sum_sub_dbar d hn0, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, sigma2]
    field_simp
    ring
  have hRgr : Rgr a b d = rhoF ((d a - (D + 1 / n)) / (D + 1 / n)) ((d b - (D + 1 / n)) / (D + 1 / n))
      ((D + 1 / n) / (n - 1)) ((S2 - 1 / n) / n) (D + 1 / n) n := by
    simp only [Rgr, eps, mu, hdbar, hσ]
  rw [H_ratio_eq (by omega) hm1 hmn hM hd1 hdn a b, hRgr]
  exact hratio_real hn' hD32 hDn hs1 hsD hs3 (hdev a) (hdev b) hS2 hS2'

/-- Adjacency of the auxiliary graph `G`: `u = d - e_a`, `v = d - e_b`. -/
def Adj (u v : Seq n) : Prop := ∃ d a b, a ≠ b ∧ u = d - e a ∧ v = d - e b

/-- The vertex set `W = 𝔇 ∩ Ω` of `G`, as integer sequences. -/
noncomputable def Wset (α : ℝ) (n m : ℕ) : Finset (Seq n) := (DsetN α n m).image toZ

theorem mem_Wset {α : ℝ} {n m : ℕ} {u : Seq n} :
    u ∈ Wset α n m ↔ u ∈ Dset α n m ∧ ∀ i, u i < n := by
  classical
  simp only [Wset, DsetN, mem_image, mem_filter, mem_OmegaNM]
  constructor
  · rintro ⟨d, ⟨⟨hlt, -⟩, hD⟩, rfl⟩
    exact ⟨hD, fun i => by simp only [toZ]; exact_mod_cast hlt i⟩
  · rintro ⟨hD, hlt⟩
    have hZ : toZ (toN u) = u := by
      ext i; simp only [toZ, toN]; exact Int.toNat_of_nonneg (hD.1 i)
    refine ⟨toN u, ⟨⟨fun i => ?_, ?_⟩, hZ ▸ hD⟩, hZ⟩
    · have := hlt i; have := hD.1 i; unfold toN; omega
    · have := hD.2.1; unfold M1 at this
      have h : ∑ i, ((toN u i : ℕ) : ℤ) = 2 * m := by
        rw [← this]; exact sum_congr rfl fun i _ => Int.toNat_of_nonneg (hD.1 i)
      exact_mod_cast h

theorem HasWalk.zero {X : Type*} (E : X → X → Prop) {W : Finset X} {u : X} (hu : u ∈ W) :
    HasWalk E W 0 u u :=
  ⟨0, le_rfl, fun _ => u, rfl, rfl, fun _ => hu, fun i => i.elim0⟩

theorem HasWalk.mono {X : Type*} {E : X → X → Prop} {W : Finset X} {r r' : ℕ} {u v : X}
    (h : HasWalk E W r u v) (hr : r ≤ r') : HasWalk E W r' u v := by
  obtain ⟨k, hk, p, hp⟩ := h
  exact ⟨k, hk.trans hr, p, hp⟩

theorem HasWalk.cons {X : Type*} {E : X → X → Prop} {W : Finset X} {r : ℕ} {u u' v : X}
    (hu : u ∈ W) (huu' : E u u') (h : HasWalk E W r u' v) : HasWalk E W (r + 1) u v := by
  obtain ⟨k, hk, p, h0, hl, hW, hE⟩ := h
  refine ⟨k + 1, by omega, Fin.cons u p, by simp, ?_, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]; exact hl
  · intro i; refine Fin.cases hu (fun j => ?_) i; rw [Fin.cons_succ]; exact hW j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one]
      rw [show (1 : Fin (k + 2)) = Fin.succ 0 from rfl, Fin.cons_succ, h0]; exact huu'
    · rw [Fin.castSucc_succ, Fin.cons_succ, Fin.cons_succ]; exact hE j

theorem dist1_eq_zero {u v : Seq n} (h : dist1 u v = 0) : u = v := by
  have := (sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (u i - v i)).1 h
  ext i; have := this i (mem_univ i); rw [abs_eq_zero] at this; linarith

/-- One step of the walk: move a unit from a coordinate where `u > v` to one where `u < v`. -/
theorem dist1_step {u v : Seq n} {a b : Fin n} (ha : v a < u a) (hb : u b < v b) :
    dist1 (u - e a + e b) v = dist1 u v - 2 := by
  have hab : a ≠ b := by rintro rfl; omega
  have key : ∀ i, |(u - e a + e b) i - v i| =
      |u i - v i| - (if i = a then 1 else 0) - (if i = b then 1 else 0) := by
    intro i
    simp only [Pi.add_apply, Pi.sub_apply, e_apply]
    split_ifs with hia hib hib
    · exact absurd (hia.symm.trans hib) hab
    · have ha' : v i < u i := hia ▸ ha
      rw [abs_of_pos (by omega : (0 : ℤ) < u i - v i),
        abs_of_nonneg (by omega : (0 : ℤ) ≤ u i - 1 + 0 - v i)]; ring
    · have hb' : u i < v i := hib ▸ hb
      rw [abs_of_neg (by omega : u i - v i < (0 : ℤ)),
        abs_of_nonpos (by omega : u i - 0 + 1 - v i ≤ (0 : ℤ))]; ring
    · ring
  unfold dist1
  simp only [key, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]
  ring

theorem exists_step {u v : Seq n} (hne : u ≠ v) (hM : M1 u = M1 v) :
    ∃ a b, v a < u a ∧ u b < v b := by
  unfold M1 at hM
  have h1 : ∃ a, v a < u a := by
    by_contra h; push Not at h
    exact hne (funext fun i => (sum_eq_sum_iff_of_le fun i _ => h i).1 hM i (mem_univ i))
  have h2 : ∃ b, u b < v b := by
    by_contra h; push Not at h
    exact hne (funext fun i =>
      ((sum_eq_sum_iff_of_le fun i _ => h i).1 hM.symm i (mem_univ i)).symm)
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a, b, ha, hb⟩

theorem dist1_even {u v : Seq n} (hM : M1 u = M1 v) : Even (dist1 u v) := by
  have : ∀ i, |u i - v i| = (u i - v i) + 2 * (if u i - v i < 0 then -(u i - v i) else 0) := by
    intro i; split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.1 h)]; ring
  unfold dist1 M1 at *
  simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  exact ⟨∑ i, if u i - v i < 0 then -(u i - v i) else 0, by rw [hM]; ring⟩

theorem step_mem_Wset {α : ℝ} {n m : ℕ} {u v : Seq n} (hu : u ∈ Wset α n m)
    (hv : v ∈ Wset α n m) {a b : Fin n} (ha : v a < u a) (hb : u b < v b) :
    u - e a + e b ∈ Wset α n m := by
  rw [mem_Wset] at hu hv ⊢
  obtain ⟨⟨hu0, huM, huD⟩, hun⟩ := hu
  obtain ⟨⟨hv0, -, hvD⟩, hvn⟩ := hv
  have hab : a ≠ b := by rintro rfl; omega
  have hval : ∀ i, (u - e a + e b) i = u i ∨
      ((u - e a + e b) i = u i - 1 ∧ v i ≤ u i - 1) ∨
      ((u - e a + e b) i = u i + 1 ∧ u i + 1 ≤ v i) := by
    intro i
    simp only [Pi.add_apply, Pi.sub_apply, e_apply]
    by_cases hia : i = a
    · subst hia; right; left; simp [hab]; omega
    · by_cases hib : i = b
      · subst hib; right; right; simp [hia]; omega
      · left; simp [hia, hib]
  have hbetween : ∀ i, (u i ≤ (u - e a + e b) i ∧ (u - e a + e b) i ≤ v i) ∨
      (v i ≤ (u - e a + e b) i ∧ (u - e a + e b) i ≤ u i) := by
    intro i; rcases hval i with h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] <;> omega
  refine ⟨⟨fun i => ?_, ?_, fun i => ?_⟩, fun i => ?_⟩
  · have := hbetween i; have := hu0 i; have := hv0 i; omega
  · simp only [M1, Pi.add_apply, Pi.sub_apply, sum_add_distrib, sum_sub_distrib, e_apply,
      sum_ite_eq', mem_univ, if_true]
    unfold M1 at huM; omega
  · have h2 := abs_le.1 (huD i); have h3 := abs_le.1 (hvD i)
    rw [abs_le]
    rcases hbetween i with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      have := (Int.cast_le (R := ℝ)).2 h <;> have := (Int.cast_le (R := ℝ)).2 h' <;>
      constructor <;> linarith
  · have := hbetween i; have := hun i; have := hvn i; omega

/-- The diameter of `G` on `W` is at most `n d^α`. -/
theorem diam_Dset (α : ℝ) (_hα : 0 ≤ α) (n m : ℕ) (u v : Seq n)
    (hu : u ∈ Wset α n m) (hv : v ∈ Wset α n m) :
    ∃ r : ℕ, (r : ℝ) ≤ n * (2 * m / n : ℝ) ^ α ∧ HasWalk Adj (Wset α n m) r u v := by
  have key : ∀ k : ℕ, ∀ u v : Seq n, u ∈ Wset α n m → v ∈ Wset α n m → dist1 u v ≤ 2 * k →
      HasWalk Adj (Wset α n m) k u v := by
    intro k
    induction k with
    | zero =>
      intro u v hu hv hd
      have h0 : dist1 u v = 0 := le_antisymm (by simpa using hd) (sum_nonneg fun i _ => abs_nonneg _)
      rw [dist1_eq_zero h0]; exact HasWalk.zero _ hv
    | succ k ih =>
      intro u v hu hv hd
      by_cases hne : u = v
      · subst hne; exact (HasWalk.zero _ hu).mono (Nat.zero_le _)
      obtain ⟨a, b, ha, hb⟩ := exists_step hne
        (by rw [(mem_Wset.1 hu).1.2.1, (mem_Wset.1 hv).1.2.1])
      have hu' := step_mem_Wset hu hv ha hb
      have hadj : Adj u (u - e a + e b) := ⟨u + e b, b, a, fun h => by subst h; omega, by simp,
        by abel⟩
      exact HasWalk.cons hu hadj (ih _ _ hu' hv (by rw [dist1_step ha hb]; push_cast at hd ⊢; omega))
  obtain ⟨⟨hu0, -, huD⟩, -⟩ := mem_Wset.1 hu
  obtain ⟨⟨hv0, -, hvD⟩, -⟩ := mem_Wset.1 hv
  obtain ⟨t, ht⟩ := dist1_even ((mem_Wset.1 hu).1.2.1.trans (mem_Wset.1 hv).1.2.1.symm)
  refine ⟨(dist1 u v).toNat / 2, ?_, key _ u v hu hv (by omega)⟩
  have hd : ((dist1 u v : ℤ) : ℝ) ≤ 2 * (n * (2 * m / n : ℝ) ^ α) := by
    unfold dist1; push_cast
    calc ∑ i, |(u i : ℝ) - v i| ≤ ∑ i : Fin n, 2 * (2 * m / n : ℝ) ^ α := by
          refine sum_le_sum fun i _ => ?_
          have := huD i; have := hvD i
          calc |(u i : ℝ) - v i| = |((u i : ℝ) - 2 * m / n) - ((v i : ℝ) - 2 * m / n)| := by ring_nf
            _ ≤ _ := (abs_sub _ _).trans (by linarith)
      _ = 2 * (n * (2 * m / n : ℝ) ^ α) := by simp; ring
  have h2 : (((dist1 u v).toNat / 2 : ℕ) : ℝ) ≤ (dist1 u v : ℝ) / 2 := by
    have h3 : (((dist1 u v).toNat / 2 : ℕ) : ℝ) ≤ ((dist1 u v).toNat : ℝ) / 2 := by
      have h5 : (dist1 u v).toNat / 2 * 2 ≤ (dist1 u v).toNat := Nat.div_mul_le_self _ _
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast h5
    have h4 : (((dist1 u v).toNat : ℕ) : ℤ) = dist1 u v :=
      Int.toNat_of_nonneg (sum_nonneg fun i _ => abs_nonneg _)
    have h4' : ((dist1 u v).toNat : ℝ) = ((dist1 u v : ℤ) : ℝ) := by exact_mod_cast h4
    rw [← h4']; exact h3
  linarith

end LW
