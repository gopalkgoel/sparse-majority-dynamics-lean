import MajorityDynamics.Literature.LWFormal.Counting

set_option autoImplicit true

/-!
# Bipartite graphs: basic definitions

Bipartite graphs with parts `S = Fin ℓ` and `T = Fin n` are finite sets of pairs `(a, v)`.
Degree sequences are pairs `(s, t)` with `s : Fin ℓ → ℤ`, `t : Fin n → ℤ`.
-/

namespace LW.Bip

open Finset

variable {ℓ n : ℕ}

abbrev BGraph (ℓ n : ℕ) := Finset (Fin ℓ × Fin n)

/-- Degree of `a ∈ S`. -/
def ldeg (E : BGraph ℓ n) (a : Fin ℓ) : ℕ := (E.filter (·.1 = a)).card

/-- Degree of `v ∈ T`. -/
def rdeg (E : BGraph ℓ n) (v : Fin n) : ℕ := (E.filter (·.2 = v)).card

/-- Degree sequences `d = (s, t)`. -/
abbrev BSeq (ℓ n : ℕ) := Seq ℓ × Seq n

def HasDeg (E : BGraph ℓ n) (d : BSeq ℓ n) : Prop :=
  (∀ a, (ldeg E a : ℤ) = d.1 a) ∧ ∀ v, (rdeg E v : ℤ) = d.2 v

instance (d : BSeq ℓ n) : DecidablePred (HasDeg (ℓ := ℓ) (n := n) · d) :=
  fun _ => instDecidableAnd

/-- The set of bipartite graphs realising `d`. -/
def graphs (d : BSeq ℓ n) : Finset (BGraph ℓ n) := univ.filter (HasDeg · d)

/-- `𝒩(d)`. -/
def N (d : BSeq ℓ n) : ℕ := (graphs d).card

/-- `𝒢(ℓ, n, m)`: bipartite graphs with `m` edges. -/
def Gm (ℓ n m : ℕ) : Finset (BGraph ℓ n) := (univ : Finset (Fin ℓ × Fin n)).powersetCard m

/-- `P_{𝒟(𝒢(ℓ,n,m))}(s, t)`. -/
noncomputable def probG (ℓ n m : ℕ) (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : ℝ :=
  prob (Gm ℓ n m) fun E => ldeg E = s ∧ rdeg E = t

/-- `P_{ℬ_m(ℓ,n)}(s, t) = C(ℓn, m)⁻² ∏_a C(n, s_a) ∏_v C(ℓ, t_v)`. -/
noncomputable def probB (ℓ n m : ℕ) (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : ℝ :=
  ((ℓ * n).choose m : ℝ)⁻¹ ^ 2 * (∏ a, (n.choose (s a) : ℝ)) * ∏ v, (ℓ.choose (t v) : ℝ)

/-- Average of a sequence. -/
noncomputable def mean {k : ℕ} (d : Fin k → ℕ) : ℝ := (∑ i, (d i : ℝ)) / k

/-- `σ²(d) = k⁻¹ ∑ (dᵢ - d̄)²`. -/
noncomputable def var {k : ℕ} (d : Fin k → ℕ) : ℝ := (∑ i, ((d i : ℝ) - mean d) ^ 2) / k

/-- `μ(d) = M₁(d)/(2nℓ)`, with `M₁(d) = ∑ s_a + ∑ t_v`. -/
noncomputable def muN (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : ℝ :=
  (∑ a, (s a : ℝ) + ∑ v, (t v : ℝ)) / (2 * n * ℓ)

/-- The correction factor `H̃(d) = exp(-½ (1 - σ²(s)/(s(1-μ))) (1 - σ²(t)/(t(1-μ))))`. -/
noncomputable def Htilde (s : Fin ℓ → ℕ) (t : Fin n → ℕ) : ℝ :=
  Real.exp (-(1 / 2) * (1 - var s / (mean s * (1 - muN s t))) *
    (1 - var t / (mean t * (1 - muN s t))))

theorem ldeg_erase (E : BGraph ℓ n) {p : Fin ℓ × Fin n} (hp : p ∈ E) (a : Fin ℓ) :
    (ldeg (E.erase p) a : ℤ) = ldeg E a - if p.1 = a then 1 else 0 := by
  unfold ldeg
  rw [Finset.filter_erase]
  split_ifs with h
  · have := card_erase_add_one (s := E.filter (·.1 = a)) (mem_filter.2 ⟨hp, h⟩)
    push_cast [← this]; ring
  · rw [erase_eq_of_notMem (s := E.filter (·.1 = a)) (fun h' => h (mem_filter.1 h').2)]; simp

theorem rdeg_erase (E : BGraph ℓ n) {p : Fin ℓ × Fin n} (hp : p ∈ E) (v : Fin n) :
    (rdeg (E.erase p) v : ℤ) = rdeg E v - if p.2 = v then 1 else 0 := by
  unfold rdeg
  rw [Finset.filter_erase]
  split_ifs with h
  · have := card_erase_add_one (s := E.filter (·.2 = v)) (mem_filter.2 ⟨hp, h⟩)
    push_cast [← this]; ring
  · rw [erase_eq_of_notMem (s := E.filter (·.2 = v)) (fun h' => h (mem_filter.1 h').2)]; simp

theorem ldeg_insert (E : BGraph ℓ n) {p : Fin ℓ × Fin n} (hp : p ∉ E) (a : Fin ℓ) :
    (ldeg (insert p E) a : ℤ) = ldeg E a + if p.1 = a then 1 else 0 := by
  unfold ldeg
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hp (mem_filter.1 h').1)]; push_cast; ring
  · simp

theorem rdeg_insert (E : BGraph ℓ n) {p : Fin ℓ × Fin n} (hp : p ∉ E) (v : Fin n) :
    (rdeg (insert p E) v : ℤ) = rdeg E v + if p.2 = v then 1 else 0 := by
  unfold rdeg
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hp (mem_filter.1 h').1)]; push_cast; ring
  · simp

/-- Neighbourhood of `a ∈ S`. -/
def lnbrs (E : BGraph ℓ n) (a : Fin ℓ) : Finset (Fin n) := univ.filter fun v => (a, v) ∈ E

/-- Neighbourhood of `v ∈ T`. -/
def rnbrs (E : BGraph ℓ n) (v : Fin n) : Finset (Fin ℓ) := univ.filter fun a => (a, v) ∈ E

theorem card_lnbrs (E : BGraph ℓ n) (a : Fin ℓ) : (lnbrs E a).card = ldeg E a := by
  unfold lnbrs ldeg
  rw [← card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2 : Function.Injective
    fun v : Fin n => (a, v))]
  congr 1; ext ⟨b, w⟩
  simp only [mem_image, mem_filter, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨v, hv, rfl, rfl⟩; exact ⟨hv, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨w, h, rfl, rfl⟩

theorem card_rnbrs (E : BGraph ℓ n) (v : Fin n) : (rnbrs E v).card = rdeg E v := by
  unfold rnbrs rdeg
  rw [← card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1 : Function.Injective
    fun a : Fin ℓ => (a, v))]
  congr 1; ext ⟨b, w⟩
  simp only [mem_image, mem_filter, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨b, h, rfl, rfl⟩

end LW.Bip
