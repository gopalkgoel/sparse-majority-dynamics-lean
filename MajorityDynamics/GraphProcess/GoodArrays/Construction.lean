import MajorityDynamics.GraphProcess.GoodArrays.Balanced
import MajorityDynamics.Combinatorics.ZeroSumCounting.Basic

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal Combinatorics.ZeroSumCounting
variable {V : Type*} [Fintype V] {n : ℕ}

abbrev Perturbations (y : Local.CoarseData V n) (T p : ℝ) :=
  (s t : History (n+1)) → {z : Fin (y.sizes s) → ℤ //
    z ∈ zeroSumVectors (y.sizes s)
      (radiusCoefficient n T * Real.sqrt (p*Fintype.card V))}

def shifted (y : Local.CoarseData V n) (T p : ℝ) (z : Perturbations y T p)
    (v : V) (t : History (n+1)) : ℤ :=
  balancedBlock y (y.part v) t ⟨v, rfl⟩ +
    (z (y.part v) t).val (blockFin y (y.part v) ⟨v, rfl⟩)

theorem shifted_block (y : Local.CoarseData V n) (T p : ℝ) (z : Perturbations y T p)
    (s t : History (n+1)) (v : BlockDecomposition.Block y.part s) :
    shifted y T p z v t = balancedBlock y s t v + (z s t).val (blockFin y s v) := by
  rcases v with ⟨v, hv⟩
  subst s
  rfl

theorem shifted_deviation (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) (z : Perturbations y T p)
    (s t : History (n+1)) (v : BlockDecomposition.Block y.part s) :
    |(shifted y T p z v t : ℝ) - EnumerationBounds.avg y s t| ≤
      window n T p (Fintype.card V) := by
  rw [shifted_block, Int.cast_add]
  have hs : 0 < y.sizes s := by exact_mod_cast hreg.size_pos s
  have hb := balancedBlock_deviation y s t hs v
  have hz := (mem_zeroSumVectors.mp (z s t).property).1 (blockFin y s v)
  calc
    _ = |((balancedBlock y s t v : ℝ) - EnumerationBounds.avg y s t) +
      ((z s t).val (blockFin y s v) : ℝ)| := by congr 1; ring
    _ ≤ |(balancedBlock y s t v : ℝ) - EnumerationBounds.avg y s t| +
      |((z s t).val (blockFin y s v) : ℝ)| := abs_add_le _ _
    _ ≤ 1 + radiusCoefficient n T * Real.sqrt (p*Fintype.card V) := add_le_add hb hz
    _ ≤ _ := hreg.radius

theorem shifted_bounds (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) (z : Perturbations y T p) (v : V) (t : History (n+1)) :
    0 ≤ shifted y T p z v t ∧ shifted y T p z v t ≤
      (Local.partSizes y.part t : ℤ) - if y.part v = t then 1 else 0 := by
  have hd := abs_le.mp (shifted_deviation y T p hreg z (y.part v) t ⟨v, rfl⟩)
  have hl := hreg.lower (y.part v) t
  have hu := hreg.upper (y.part v) t
  have hnonneg : (0 : ℝ) ≤ shifted y T p z v t := by linarith
  have hupper : (shifted y T p z v t : ℝ) ≤ (y.sizes t : ℝ)-1 := by linarith
  have hupperZ : shifted y T p z v t ≤ (y.sizes t : ℤ)-1 := by exact_mod_cast hupper
  constructor
  · exact_mod_cast hnonneg
  · change shifted y T p z v t ≤ (y.sizes t : ℤ) - _
    split_ifs <;> omega

def shiftedArray (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) (z : Perturbations y T p) : RowArray.Ambient y.part :=
  RowArray.ofLiteral ⟨shifted y T p z, shifted_bounds y T p hreg z⟩

@[simp] theorem values_shiftedArray (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) (z : Perturbations y T p) :
    RowArray.values (shiftedArray y T p hreg z) = shifted y T p z :=
  RowArray.values_ofLiteral _

theorem shiftedArray_totals (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) (z : Perturbations y T p) :
    RowArray.totals (shiftedArray y T p hreg z) = y.edge := by
  funext s t
  change (∑ v ∈ History.block y.part s, RowArray.values (shiftedArray y T p hreg z) v t) = _
  rw [Finset.sum_subtype (History.block y.part s) (fun v => History.mem_block y.part s v)
    (fun v => RowArray.values (shiftedArray y T p hreg z) v t), values_shiftedArray]
  simp_rw [shifted_block]
  rw [Finset.sum_add_distrib, balancedBlock_sum y s t (by exact_mod_cast hreg.size_pos s),
    (blockFin y s).sum_comp]
  rw [(mem_zeroSumVectors.mp (z s t).property).2, add_zero]

theorem shiftedArray_mem_E0 (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) (z : Perturbations y T p) :
    shiftedArray y T p hreg z ∈ E0 y T p := by
  simp only [E0, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨shiftedArray_totals y T p hreg z, ?_⟩
  intro s t v hv
  rw [values_shiftedArray]
  exact shifted_deviation y T p hreg z s t ⟨v, (History.mem_block _ _ _).mp hv⟩

theorem shiftedArray_injective (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) : Function.Injective (shiftedArray y T p hreg) := by
  intro z w h
  have he := congrArg RowArray.values h
  simp only [values_shiftedArray] at he
  funext s t
  apply Subtype.ext
  funext i
  let v := (blockFin y s).symm i
  have hv := congrFun (congrFun he v.val) t
  rw [shifted_block y T p z s t v, shifted_block y T p w s t v] at hv
  simpa only [v, Equiv.apply_symm_apply, add_left_cancel_iff] using hv

def perturbationEmbedding (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) : Perturbations y T p ↪ {d // d ∈ E0 y T p} where
  toFun z := ⟨shiftedArray y T p hreg z, shiftedArray_mem_E0 y T p hreg z⟩
  inj' _a _b h := shiftedArray_injective y T p hreg (congrArg Subtype.val h)

theorem product_card_le_E0 (y : Local.CoarseData V n) (T p : ℝ)
    (hreg : Regime y T p) :
    (∏ s : History (n+1), ∏ _t : History (n+1),
      (zeroSumVectors (y.sizes s)
        (radiusCoefficient n T * Real.sqrt (p*Fintype.card V))).card) ≤
      (E0 y T p).card := by
  have h := Fintype.card_le_of_embedding (perturbationEmbedding y T p hreg)
  simpa only [Perturbations, Fintype.card_pi, Fintype.card_coe] using h

end MajorityDynamics.GraphProcess.GoodArrays
