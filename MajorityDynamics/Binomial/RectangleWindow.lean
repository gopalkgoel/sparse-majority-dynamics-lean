import MajorityDynamics.Binomial.ExpansionTransfer

/-! # Canonical common lattice windows and their positive masses -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Binomial
variable {ι : Type*} [Fintype ι]

theorem rectangle_finite (c L : ι → ℝ) : (rectangle c L).Finite := by
  apply (Set.Finite.pi (fun i : ι => Set.finite_Iic ⌈c i + L i⌉₊)).subset
  intro a ha i _
  have h := (abs_le.mp (ha i)).2
  exact_mod_cast (show (a i : ℝ) ≤ ⌈c i + L i⌉₊ from
    (by linarith : (a i : ℝ) ≤ c i + L i).trans (Nat.le_ceil _))

def rectangleWindow (c L : ι → ℝ) : Finset (ι → ℕ) := (rectangle_finite c L).toFinset

@[simp] theorem mem_rectangleWindow (c L : ι → ℝ) (a : ι → ℕ) :
    a ∈ rectangleWindow c L ↔ a ∈ rectangle c L := Set.Finite.mem_toFinset _

@[simp] theorem coe_rectangleWindow (c L : ι → ℝ) :
    (rectangleWindow c L : Set (ι → ℕ)) = rectangle c L := Set.Finite.coe_toFinset _

theorem rectangleWindow_nonempty (c L : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hL : ∀ i, 1 ≤ L i) :
    (rectangleWindow c L).Nonempty := by
  refine ⟨fun i => ⌊c i⌋₊, ?_⟩
  rw [mem_rectangleWindow]
  exact fun i => (Nat.abs_floor_sub_le (hc i)).trans (hL i)

omit [Fintype ι] in
theorem rectangle_support (η : ι → ℕ) (c L : ι → ℝ)
    (hupper : ∀ i, c i + L i ≤ η i) {a : ι → ℕ} (ha : a ∈ rectangle c L) :
    ∀ i, a i ≤ η i := by
  intro i
  have h := (abs_le.mp (ha i)).2
  have hi := hupper i
  exact_mod_cast (show (a i : ℝ) ≤ η i by linarith)

theorem rectangle_mass_pos (η : ι → ℕ) (q : ι → Probability) (c L : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hL : ∀ i, 1 ≤ L i) (hupper : ∀ i, c i + L i ≤ η i) :
    0 < (law η q).real (rectangle c L) := by
  obtain ⟨a, ha⟩ := rectangleWindow_nonempty c L hc hL
  rw [mem_rectangleWindow] at ha
  have hp : 0 < (law η q).real {a} := by
    rw [law_singleton_ambient, Approximation.ambientMass_eq_prod_pointMass]
    exact Finset.prod_pos fun i _ => Approximation.pointMass_pos
      (rectangle_support η c L hupper ha i) (q i)
  exact hp.trans_le (measureReal_mono (Set.singleton_subset_iff.mpr ha))

end MajorityDynamics.Binomial
