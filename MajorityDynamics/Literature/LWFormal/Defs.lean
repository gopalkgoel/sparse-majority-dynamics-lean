import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

set_option autoImplicit true

/-!
# Basic definitions

Graphs on `Fin n` are finite sets of unordered pairs without loops.  Degree sequences are
`Fin n → ℤ` so that `d - e_a` is always meaningful (a negative entry forces `N = 0`).
-/

namespace LW

open Finset

variable {n : ℕ}

abbrev Graph (n : ℕ) := Finset (Sym2 (Fin n))

def IsSimple (E : Graph n) : Prop := ∀ e ∈ E, ¬ e.IsDiag

def deg (E : Graph n) (v : Fin n) : ℕ := (E.filter (v ∈ ·)).card

def HasDegSeq (E : Graph n) (d : Fin n → ℤ) : Prop :=
  IsSimple E ∧ ∀ v, (deg E v : ℤ) = d v

instance : DecidablePred (IsSimple (n := n)) :=
  fun _ => inferInstanceAs (Decidable (∀ _, _))

instance (d : Fin n → ℤ) : DecidablePred (HasDegSeq (n := n) · d) :=
  fun _ => instDecidableAnd

/-- The set `𝒢(d)` of graphs realising `d`. -/
def graphs (d : Fin n → ℤ) : Finset (Graph n) := univ.filter (HasDegSeq · d)

/-- `𝒩(d) = g(d)`, the number of graphs with degree sequence `d`. -/
def N (d : Fin n → ℤ) : ℕ := (graphs d).card

/-- Number of simple graphs on `[n]` with exactly `m` edges, `C(n(n-1)/2, m)`. -/
def edgeGraphCount (n m : ℕ) : ℕ :=
  (univ.filter fun E : Graph n => IsSimple E ∧ E.card = m).card

/-- Uniform probability of an event on a finite sample space. -/
noncomputable def prob {α : Type*} (Ω : Finset α) (A : α → Prop) [DecidablePred A] : ℝ :=
  (Ω.filter A).card / Ω.card

/-- Expectation with respect to the uniform distribution on `Ω`. -/
noncomputable def expect {α : Type*} (Ω : Finset α) (f : α → ℝ) : ℝ := (∑ x ∈ Ω, f x) / Ω.card

/-- Edge set of `K_n`. -/
def allEdges (n : ℕ) : Finset (Sym2 (Fin n)) := univ.filter (¬ ·.IsDiag)

/-- `𝒢(n,m)`: simple graphs on `[n]` with `m` edges. -/
def Gnm (n m : ℕ) : Finset (Graph n) := (allEdges n).powersetCard m

def degSeq (E : Graph n) : Fin n → ℕ := deg E

/-- `P_{𝒟(𝒢(n,m))}(d)`: probability that a uniform `m`-edge graph has degree sequence `d`. -/
noncomputable def probGnm (n m : ℕ) (d : Fin n → ℕ) : ℝ := prob (Gnm n m) (degSeq · = d)

/-- `P_{ℬ_m}(d) = C(n(n-1), 2m)⁻¹ ∏ C(n-1, d_i)`. -/
noncomputable def probBinom (n m : ℕ) (d : Fin n → ℕ) : ℝ :=
  ((n * (n - 1)).choose (2 * m) : ℝ)⁻¹ * ∏ i, ((n - 1).choose (d i) : ℝ)

noncomputable def avgDeg (d : Fin n → ℕ) : ℝ := (∑ i, (d i : ℝ)) / n

/-- `μ = d/(n-1)`. -/
noncomputable def density (d : Fin n → ℕ) : ℝ := avgDeg d / (n - 1)

/-- `γ₂ = (n-1)⁻² ∑ (d_i - d)²`. -/
noncomputable def gamma2 (d : Fin n → ℕ) : ℝ :=
  (∑ i, ((d i : ℝ) - avgDeg d) ^ 2) / ((n : ℝ) - 1) ^ 2

/-- `exp(1/4 - γ₂²/(4μ²(1-μ)²))`. -/
noncomputable def expFactor (d : Fin n → ℕ) : ℝ :=
  Real.exp (1 / 4 - gamma2 d ^ 2 / (4 * density d ^ 2 * (1 - density d) ^ 2))

theorem deg_erase (E : Graph n) {e : Sym2 (Fin n)} (he : e ∈ E) (w : Fin n) :
    (deg (E.erase e) w : ℤ) = deg E w - if w ∈ e then 1 else 0 := by
  unfold deg
  rw [Finset.filter_erase]
  split_ifs with h
  · have := card_erase_add_one (s := E.filter (w ∈ ·)) (mem_filter.2 ⟨he, h⟩)
    push_cast [← this]; ring
  · rw [erase_eq_of_notMem (s := E.filter (w ∈ ·)) (fun h' => h (mem_filter.1 h').2)]; simp

theorem deg_insert (E : Graph n) {e : Sym2 (Fin n)} (he : e ∉ E) (w : Fin n) :
    (deg (insert e E) w : ℤ) = deg E w + if w ∈ e then 1 else 0 := by
  unfold deg
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => he (mem_filter.1 h').1)]; push_cast; ring
  · simp

/-- In a simple graph, the degree of `v` counts its neighbours. -/
theorem deg_eq_card_nbrs {G : Graph n} (hs : IsSimple G) (v : Fin n) :
    deg G v = ((univ.erase v).filter fun b => s(b, v) ∈ G).card := by
  unfold deg
  rw [← card_image_of_injective _ (fun x y h => Sym2.congr_left.1 h : Function.Injective
    fun b : Fin n => s(b, v))]
  congr 1
  ext f
  simp only [mem_image, mem_filter, mem_erase, mem_univ, and_true]
  constructor
  · rintro ⟨hf, hv⟩
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hv
    refine ⟨b, ⟨fun h => hs _ hf ?_, by rwa [Sym2.eq_swap]⟩, Sym2.eq_swap⟩
    simp [h]
  · rintro ⟨b, ⟨hbv, hb⟩, rfl⟩
    exact ⟨hb, Sym2.mem_mk_right _ _⟩

/-- Neighbours of `v` in a simple graph. -/
theorem deg_eq_card_filter {G : Graph n} (hs : IsSimple G) (v : Fin n) :
    deg G v = (univ.filter fun b => s(b, v) ∈ G).card := by
  rw [deg_eq_card_nbrs hs, filter_erase, erase_eq_of_notMem]
  simp only [mem_filter, mem_univ, true_and]
  exact fun h => hs _ h (by simp)

/-- Neighbourhood of `a` in `G`. -/
def nbrs (G : Graph n) (a : Fin n) : Finset (Fin n) := univ.filter fun y => s(a, y) ∈ G

theorem card_nbrs {G : Graph n} (hs : IsSimple G) (a : Fin n) : (nbrs G a).card = deg G a := by
  rw [deg_eq_card_filter hs, nbrs]; simp_rw [Sym2.eq_swap]

theorem ite_mem_sym2 {a v w : Fin n} (hav : a ≠ v) :
    (if w ∈ s(a, v) then (1 : ℤ) else 0) = (if w = a then 1 else 0) + if w = v then 1 else 0 := by
  simp only [Sym2.mem_iff]
  by_cases ha : w = a <;> by_cases hv : w = v <;> simp_all

end LW
