import MajorityDynamics.Binomial.GaussianCellError

/-! # Coverage and tails of the common Gaussian cell window -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation
variable {d : ℕ}

def gaussianCellWindow (p : Probability) (η : Fin d → ℕ) (L : ℝ) : Set (Fin d → ℝ) :=
  ⋃ a ∈ rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => L), gaussianCell p η a

theorem gaussianCellWindow_measurable (p : Probability) (η : Fin d → ℕ) (L : ℝ) :
    MeasurableSet (gaussianCellWindow p η L) :=
  Finset.measurableSet_biUnion _ (fun a _ => gaussianCell_measurable p η a)

theorem gaussianCellWindow_coordinate_bound (p : Probability) (η : Fin d → ℕ) (L : ℝ)
    {x : Fin d → ℝ} (hx : x ∈ gaussianCellWindow p η L) : ∀ i, |x i| ≤ L + 1 := by
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
  have hrect := (mem_rectangleWindow _ _ _).mp ha
  intro i
  have h := gaussianCell_coordinate_error p η a hxa i
  have hi := hrect i
  have heq : x i = centered p η a i - (centered p η a i - x i) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add hi h)

theorem gaussianCellWindow_covers (p : Probability) (η : Fin d → ℕ) (L : ℝ)
    (hL : 2 ≤ L) (hcenter : ∀ i, L ≤ (p : ℝ) * η i)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ L / 2) : x ∈ gaussianCellWindow p η L := by
  let a : Fin d → ℕ := fun i => ⌊x i + (p : ℝ) * η i⌋₊
  have hpos (i : Fin d) : 0 ≤ x i + (p : ℝ) * η i := by
    have hi := (abs_le.mp (hx i)).1
    have hc := hcenter i
    linarith
  have hcell : x ∈ gaussianCell p η a := by
    intro i _
    have hlo := Nat.floor_le (hpos i)
    have hhi := Nat.lt_floor_add_one (x i + (p : ℝ) * η i)
    change (a i : ℝ) - (p : ℝ) * η i ≤ x i ∧ x i < (a i : ℝ) - (p : ℝ) * η i + 1
    dsimp [a]
    constructor <;> linarith
  have ha : a ∈ rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => L) := by
    rw [mem_rectangleWindow]
    intro i
    have hi := gaussianCell_coordinate_error p η a hcell i
    have heq : centered p η a i = (centered p η a i - x i) + x i := by ring
    change |centered p η a i| ≤ L
    rw [heq]
    have h := (abs_add_le _ _).trans (add_le_add hi (hx i))
    linarith
  exact Set.mem_iUnion₂.mpr ⟨a, ha, hcell⟩

theorem gaussianCellWindow_tail (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (hη : ∀ i, 0 < η i) (T s l : ℝ) (hT : 0 < T) (hs : 0 < s) (_hl : 0 ≤ l)
    (hL : 2 ≤ s * l) (hcenter : ∀ i, s * l ≤ (p : ℝ) * η i)
    (hmean : ∀ i, |gaussianMean p η α i| ≤ s * l / 4)
    (hvar : ∀ i, (p : ℝ) * η i ≤ T * s ^ 2) :
    (gaussianLaw p η α).real (gaussianCellWindow p η (s * l))ᶜ ≤
      2 * d * Real.exp (-(l ^ 2) / (32 * T)) := by
  classical
  have hsub : (gaussianCellWindow p η (s * l))ᶜ ⊆
      ⋃ i, {x : Fin d → ℝ | s * l / 4 ≤ |x i - gaussianMean p η α i|} := by
    intro x hx
    have hex : ∃ i, s * l / 2 < |x i| := by
      by_contra h
      push Not at h
      exact hx (gaussianCellWindow_covers p η (s * l) hL hcenter h)
    obtain ⟨i, hi⟩ := hex
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change s * l / 4 ≤ |x i - gaussianMean p η α i|
    have h := abs_sub_abs_le_abs_sub (x i) (gaussianMean p η α i)
    linarith [hmean i]
  have htail (i : Fin d) : (gaussianLaw p η α).real
      {x : Fin d → ℝ | s * l / 4 ≤ |x i - gaussianMean p η α i|} ≤
        2 * Real.exp (-(l ^ 2) / (32 * T)) := by
    apply (gaussian_coordinate_tail p η α i (hη i) (s * l / 4) (by positivity)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    have hv : 0 < (p : ℝ) * η i := mul_pos p.property.1 (by exact_mod_cast hη i)
    have h := div_le_div_of_nonneg_left (sq_nonneg (s * l / 4)) (show 0 < 2 * ((p : ℝ) * η i) by positivity)
      (mul_le_mul_of_nonneg_left (hvar i) (by norm_num : (0 : ℝ) ≤ 2))
    have heq : (s * l / 4) ^ 2 / (2 * (T * s ^ 2)) = l ^ 2 / (32 * T) := by field_simp; ring
    rwa [heq] at h
  apply (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans _)
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin d))) => htail i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (d : ℝ) * (2 * Real.exp (-(l ^ 2) / (32 * T))) = 2 * d * Real.exp (-(l ^ 2) / (32 * T)) by ring] using hsum

end MajorityDynamics.Binomial.Approximation
