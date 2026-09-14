import MajorityDynamics.GraphProcess.History.Main
import MajorityDynamics.Universal.ResponseBasic

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.DayOne
open Universal History Probability.RandomOpinionsReduction
variable {V : Type*} [Fintype V]

theorem initial_history_iff (G : SimpleGraph V) (c : V → Bool) (v : V) (s : Universal.History 1) :
    actualHistory G c 1 v = s ↔ c v = last s := by
  rw [actualHistory_eq_iff]
  simp [Fin.forall_fin_one, coloringOnDayV, last]

theorem initial_sizes (G : SimpleGraph V) (c : V → Bool) (s : Universal.History 1) :
    Local.partSizes (actualHistory G c 1) s =
      (Finset.univ.filter fun v => c v = last s).card := by
  classical
  unfold Local.partSizes
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact initial_history_iff G c v s

theorem initial_sizes_le_card (G : SimpleGraph V) (c : V → Bool) (s : Universal.History 1) :
    Local.partSizes (actualHistory G c 1) s ≤ Fintype.card V := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

theorem initial_sizes_floor_error (G : SimpleGraph V) (c : V → Bool)
    {N : ℕ} (hV : Fintype.card V = N) {τ : ℝ} (hτ : 0 ≤ τ)
    (hc : (Finset.univ.filter fun v => c v = false).card = N/2 + ⌊τ*Real.sqrt N⌋₊)
    (s : Universal.History 1) :
    |(Local.partSizes (actualHistory G c 1) s : ℝ) - (N/2 : ℕ) -
      τ * Real.sqrt N * ε 0 s| ≤ 2 := by
  classical
  have hx : 0 ≤ τ * Real.sqrt N := mul_nonneg hτ (Real.sqrt_nonneg _)
  have hf := Nat.floor_le hx
  have hfl := Nat.lt_floor_add_one (τ * Real.sqrt N)
  have hrem : N/2*2 ≤ N ∧ N ≤ N/2*2+1 := by omega
  have hrem' : ((N/2:ℕ):ℝ)*2 ≤ (N:ℝ) ∧ (N:ℝ) ≤ ((N/2:ℕ):ℝ)*2+1 := by
    exact_mod_cast hrem
  rw [initial_sizes, ε_zero]
  cases hs : last s
  · simp only [sign_false, mul_one, hc, Nat.cast_add]
    rw [abs_le]
    constructor <;> linarith
  · have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun v => c v = false)
    have hnot : (Finset.univ.filter fun v => ¬ c v = false) =
        (Finset.univ.filter fun v => c v = true) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases c v <;> simp
    rw [hnot, Finset.card_univ, hV, hc] at hsum
    have hsum' : ((N/2:ℕ):ℝ) + (⌊τ * Real.sqrt N⌋₊ : ℝ) +
        ((Finset.univ.filter fun v => c v = true).card : ℝ) = N := by
      exact_mod_cast hsum
    simp only [sign_true, mul_neg_one]
    rw [abs_le]
    constructor <;> linarith

end MajorityDynamics.GraphProcess.DayOne
