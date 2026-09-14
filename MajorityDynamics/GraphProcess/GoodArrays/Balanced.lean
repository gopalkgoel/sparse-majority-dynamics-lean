import MajorityDynamics.GraphProcess.GoodArrays.Basic
import Mathlib.Order.Interval.Finset.Fin

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal

/-- Quotient/remainder sequence, with the remainder entries incremented by one. -/
def balanced (a : ℕ) (m : ℤ) (i : Fin a) : ℤ :=
  m / a + if i.val < (m % a).toNat then 1 else 0

theorem balanced_sum (a : ℕ) (ha : 0 < a) (m : ℤ) :
    ∑ i, balanced a m i = m := by
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hr0 := Int.emod_nonneg m (ne_of_gt haZ)
  have hrlt := Int.emod_lt_of_pos m haZ
  have hr : (m % (a : ℤ)).toNat < a := by omega
  have he : (Finset.univ.filter fun i : Fin a => i.val < (m % (a : ℤ)).toNat) =
      Finset.Iio (⟨(m % (a : ℤ)).toNat, hr⟩ : Fin a) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  simp only [balanced, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, he, Fin.card_Iio]
  have hcast : ((m % (a : ℤ)).toNat : ℤ) = m % a := Int.toNat_of_nonneg hr0
  rw [hcast]
  exact Int.mul_ediv_add_emod m a

theorem balanced_deviation (a : ℕ) (ha : 0 < a) (m : ℤ) (i : Fin a) :
    |(balanced a m i : ℝ) - (m : ℝ)/a| ≤ 1 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hr0 : (0 : ℝ) ≤ (m % (a : ℤ) : ℤ) := by exact_mod_cast Int.emod_nonneg m (ne_of_gt haZ)
  have hrlt : ((m % (a : ℤ) : ℤ) : ℝ) < a := by exact_mod_cast Int.emod_lt_of_pos m haZ
  have he : (a : ℝ) * (m / (a : ℤ) : ℤ) + (m % (a : ℤ) : ℤ) = m := by
    exact_mod_cast Int.mul_ediv_add_emod m (a : ℤ)
  have hlo : ((m / (a : ℤ) : ℤ) : ℝ) ≤ (m : ℝ)/a := (le_div_iff₀ haR).mpr (by nlinarith)
  have hhi : (m : ℝ)/a < ((m / (a : ℤ) : ℤ) : ℝ) + 1 := (div_lt_iff₀ haR).mpr (by nlinarith)
  unfold balanced
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> linarith

variable {V : Type*} [Fintype V] {n : ℕ}

def blockFin (y : Local.CoarseData V n) (s : History (n+1)) :
    BlockDecomposition.Block y.part s ≃ Fin (y.sizes s) :=
  (Fintype.equivFin _).trans (finCongr (by rw [Fintype.card_subtype]; rfl))

def balancedBlock (y : Local.CoarseData V n) (s t : History (n+1))
    (v : BlockDecomposition.Block y.part s) : ℤ :=
  balanced (y.sizes s) (y.edge s t) (blockFin y s v)

theorem balancedBlock_sum (y : Local.CoarseData V n) (s t : History (n+1))
    (hs : 0 < y.sizes s) : ∑ v, balancedBlock y s t v = y.edge s t := by
  rw [show (∑ v, balancedBlock y s t v) = ∑ i, balanced (y.sizes s) (y.edge s t) i from
    (blockFin y s).sum_comp _]
  exact balanced_sum _ hs _

theorem balancedBlock_deviation (y : Local.CoarseData V n) (s t : History (n+1))
    (hs : 0 < y.sizes s) (v : BlockDecomposition.Block y.part s) :
    |(balancedBlock y s t v : ℝ) - EnumerationBounds.avg y s t| ≤ 1 :=
  balanced_deviation _ hs _ _

end MajorityDynamics.GraphProcess.GoodArrays
