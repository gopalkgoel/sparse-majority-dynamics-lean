import MajorityDynamics.Idealized.LinearResponse.Quotient

/-!
# The three response clauses as real-arithmetic lemmas

Each lemma takes the two A.2 expansions (mass and first moment) of the tilted
model around the reference model together with numeric bounds on the reference
quantities, and produces the paper's normalized response with an explicit
remainder. `X₁ = Σ β_i M1_i`, `X₂ = Σ β_i M2_i`, `Y = Σ β_i mbar_i`.
-/

namespace MajorityDynamics.Idealized.LinearResponse

variable {ι : Type*} [Fintype ι]

theorem abs_first_order_le (D P' X₁ Y u eP : ℝ)
    (hP : |P' - D - X₁ + Y * D| ≤ eP) (hu : |P' - D| ≤ u) : |X₁ - Y * D| ≤ u + eP := by
  have h : X₁ - Y * D = (P' - D) - (P' - D - X₁ + Y * D) := by ring
  rw [h]
  exact (abs_sub _ _).trans (add_le_add hu hP)

/-- Clause (i): the normalized conditional-mean response. -/
theorem mean_clause (D P' M' : ℝ) (M1 M2 σ β mbar Sig : ι → ℝ) (t : ι)
    (b₀ V R G ec u eP eM Em : ℝ) (hD : 0 < D) (hV : 0 < V) (hb₀ : 0 < b₀)
    (hβ : ∀ i, β i = b₀ * σ i) (hσ : ∀ i, |σ i| ≤ R)
    (hP : |P' - D - (∑ i, β i * M1 i) + (∑ i, β i * mbar i) * D| ≤ eP)
    (hM : |M' - M1 t - (∑ i, β i * M2 i) + (∑ i, β i * mbar i) * M1 t| ≤ eM)
    (hu : |P' - D| ≤ u) (hsmall : u + eP ≤ D / 4)
    (hcov : ∀ i, |(M2 i / D - M1 i / D * (M1 t / D)) / V - Sig i| ≤ ec)
    (hG : ∀ i, |Sig i| ≤ G) (hEm : |M1 t / D| ≤ Em) :
    D / 2 ≤ P' ∧
    |(M' / P' - M1 t / D) / (b₀ * V) - ∑ i, Sig i * σ i| ≤
      (Fintype.card ι : ℝ) * (R * ec) +
        2 / D * (eM + (u + eP) * ((Fintype.card ι : ℝ) * ((b₀ * R) * ((G + ec) * V))) +
          eP * (Em + (Fintype.card ι : ℝ) * ((b₀ * R) * ((G + ec) * V)))) / (b₀ * V) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans hu
  have heP0 : 0 ≤ eP := (abs_nonneg _).trans hP
  have hU := abs_first_order_le D P' (∑ i, β i * M1 i) (∑ i, β i * mbar i) u eP hP hu
  obtain ⟨hDen, hq⟩ := quotient_response M' P' (M1 t) D (∑ i, β i * M1 i) (∑ i, β i * M2 i)
    (∑ i, β i * mbar i) eP eM
    ((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D) hD rfl hP hM
    (hU.trans hsmall) (by linarith)
  refine ⟨hDen, ?_⟩
  have hSsum := first_order_sum_eq β M1 M2 (M1 t) D
  have hcovb : ∀ i, |M2 i / D - M1 i / D * (M1 t / D)| ≤ (G + ec) * V := by
    intro i
    have h1 : |(M2 i / D - M1 i / D * (M1 t / D)) / V| ≤ G + ec := by
      have := abs_sub_abs_le_abs_sub ((M2 i / D - M1 i / D * (M1 t / D)) / V) (Sig i)
      linarith [hcov i, hG i]
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV] at h1
    exact h1
  have hβb : ∀ i, |β i| ≤ b₀ * R := by
    intro i
    rw [hβ i, abs_mul, abs_of_pos hb₀]
    exact mul_le_mul_of_nonneg_left (hσ i) hb₀.le
  have hS : |(∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D| ≤
      (Fintype.card ι : ℝ) * ((b₀ * R) * ((G + ec) * V)) := by
    rw [hSsum]
    exact abs_sum_mul_le' β (fun i => M2 i / D - M1 i / D * (M1 t / D)) _ _ hβb hcovb
  have hbV : 0 < b₀ * V := mul_pos hb₀ hV
  have hD0 : D ≠ 0 := hD.ne'
  have hb0 : b₀ ≠ 0 := hb₀.ne'
  have hV0 : V ≠ 0 := hV.ne'
  have hSV : ((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D) / (b₀ * V) =
      ∑ i, σ i * ((M2 i / D - M1 i / D * (M1 t / D)) / V) := by
    rw [hSsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [hβ i]
    field_simp
  have hsecond : ((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D) / (b₀ * V) -
      ∑ i, Sig i * σ i =
      ∑ i, σ i * ((M2 i / D - M1 i / D * (M1 t / D)) / V - Sig i) := by
    rw [hSV, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdecomp : (M' / P' - M1 t / D) / (b₀ * V) - ∑ i, Sig i * σ i =
      (M' / P' - (M1 t / D + ((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D))) /
          (b₀ * V) +
        (((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D) / (b₀ * V) -
          ∑ i, Sig i * σ i) := by
    ring
  rw [hdecomp, hsecond]
  have hAS : |M1 t / D + ((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D)| ≤
      Em + (Fintype.card ι : ℝ) * ((b₀ * R) * ((G + ec) * V)) :=
    (abs_add_le _ _).trans (add_le_add hEm hS)
  have h1 : |(M' / P' - (M1 t / D + ((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D))) /
      (b₀ * V)| ≤
      2 / D * (eM + (u + eP) * ((Fintype.card ι : ℝ) * ((b₀ * R) * ((G + ec) * V))) +
        eP * (Em + (Fintype.card ι : ℝ) * ((b₀ * R) * ((G + ec) * V)))) / (b₀ * V) := by
    rw [abs_div, abs_of_pos hbV]
    apply div_le_div_of_nonneg_right _ hbV.le
    refine hq.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hprod := mul_le_mul hU hS (abs_nonneg _) (by linarith)
    have hprod' := mul_le_mul_of_nonneg_left hAS heP0
    linarith
  have h2 : |∑ i, σ i * ((M2 i / D - M1 i / D * (M1 t / D)) / V - Sig i)| ≤
      (Fintype.card ι : ℝ) * (R * ec) :=
    abs_sum_mul_le' σ (fun i => (M2 i / D - M1 i / D * (M1 t / D)) / V - Sig i) R ec hσ hcov
  calc
    _ ≤ |(M' / P' - (M1 t / D + ((∑ i, β i * M2 i) / D - M1 t / D * (∑ i, β i * M1 i) / D))) /
          (b₀ * V)| + |∑ i, σ i * ((M2 i / D - M1 i / D * (M1 t / D)) / V - Sig i)| :=
      abs_add_le _ _
    _ ≤ _ := by linarith [h1, h2]

/-- Clause (ii): the normalized split-probability response. -/
theorem split_clause (D DJ P' P'J : ℝ) (M1 M1J σ β mbar gJ gI : ι → ℝ)
    (r b₀ S₀ R G em er u eP ePJ : ℝ) (hD : 0 < D) (hDJ : 0 < DJ) (hDJD : DJ ≤ D)
    (hS₀ : 0 < S₀) (hb₀ : 0 < b₀)
    (hβ : ∀ i, β i = b₀ * σ i) (hσ : ∀ i, |σ i| ≤ R)
    (hP : |P' - D - (∑ i, β i * M1 i) + (∑ i, β i * mbar i) * D| ≤ eP)
    (hPJ : |P'J - DJ - (∑ i, β i * M1J i) + (∑ i, β i * mbar i) * DJ| ≤ ePJ)
    (hu : |P' - D| ≤ u) (hsmall : u + eP ≤ D / 4)
    (hr : |DJ / D - r| ≤ er)
    (hμJ : ∀ i, |M1J i / DJ / S₀ - gJ i| ≤ em) (hμI : ∀ i, |M1 i / D / S₀ - gI i| ≤ em)
    (hg : ∀ i, |gJ i| ≤ G ∧ |gI i| ≤ G) :
    |(P'J / P' - DJ / D) / (b₀ * S₀) - r * ∑ i, σ i * (gJ i - gI i)| ≤
      (Fintype.card ι : ℝ) * (R * (2 * em)) + (Fintype.card ι : ℝ) * (R * (2 * G)) * er +
        2 / D * (ePJ + (u + eP) * ((Fintype.card ι : ℝ) * ((b₀ * R) * (2 * (G + em) * S₀))) +
          eP * (1 + (Fintype.card ι : ℝ) * ((b₀ * R) * (2 * (G + em) * S₀)))) / (b₀ * S₀) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans hu
  have heP0 : 0 ≤ eP := (abs_nonneg _).trans hP
  have hU := abs_first_order_le D P' (∑ i, β i * M1 i) (∑ i, β i * mbar i) u eP hP hu
  obtain ⟨_, hq⟩ := quotient_response P'J P' DJ D (∑ i, β i * M1 i) (∑ i, β i * M1J i)
    (∑ i, β i * mbar i) eP ePJ
    ((∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D) hD rfl hP hPJ
    (hU.trans hsmall) (by linarith)
  have hSsum := first_order_sum_eq β M1 M1J DJ D
  have hratio0 : 0 ≤ DJ / D := div_nonneg hDJ.le hD.le
  have hratio1 : DJ / D ≤ 1 := (div_le_one hD).mpr hDJD
  have hD0 : D ≠ 0 := hD.ne'
  have hDJ0 : DJ ≠ 0 := hDJ.ne'
  have hb0 : b₀ ≠ 0 := hb₀.ne'
  have hS0 : S₀ ≠ 0 := hS₀.ne'
  have hμJb : ∀ i, |M1J i / DJ| ≤ (G + em) * S₀ := by
    intro i
    have h1 : |M1J i / DJ / S₀| ≤ G + em := by
      have := abs_sub_abs_le_abs_sub (M1J i / DJ / S₀) (gJ i)
      linarith [hμJ i, (hg i).1]
    rw [abs_div, abs_of_pos hS₀, div_le_iff₀ hS₀] at h1
    exact h1
  have hμIb : ∀ i, |M1 i / D| ≤ (G + em) * S₀ := by
    intro i
    have h1 : |M1 i / D / S₀| ≤ G + em := by
      have := abs_sub_abs_le_abs_sub (M1 i / D / S₀) (gI i)
      linarith [hμI i, (hg i).2]
    rw [abs_div, abs_of_pos hS₀, div_le_iff₀ hS₀] at h1
    exact h1
  have hcovb : ∀ i, |M1J i / D - M1 i / D * (DJ / D)| ≤ 2 * (G + em) * S₀ := by
    intro i
    have h : M1J i / D - M1 i / D * (DJ / D) = DJ / D * (M1J i / DJ - M1 i / D) := by
      field_simp
    rw [h, abs_mul, abs_of_nonneg hratio0]
    have h2 : |M1J i / DJ - M1 i / D| ≤ 2 * (G + em) * S₀ := by
      have := abs_sub (M1J i / DJ) (M1 i / D)
      linarith [hμJb i, hμIb i]
    calc
      _ ≤ 1 * |M1J i / DJ - M1 i / D| := mul_le_mul_of_nonneg_right hratio1 (abs_nonneg _)
      _ = |M1J i / DJ - M1 i / D| := one_mul _
      _ ≤ _ := h2
  have hβb : ∀ i, |β i| ≤ b₀ * R := by
    intro i
    rw [hβ i, abs_mul, abs_of_pos hb₀]
    exact mul_le_mul_of_nonneg_left (hσ i) hb₀.le
  have hS : |(∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D| ≤
      (Fintype.card ι : ℝ) * ((b₀ * R) * (2 * (G + em) * S₀)) := by
    rw [hSsum]
    exact abs_sum_mul_le' β (fun i => M1J i / D - M1 i / D * (DJ / D)) _ _ hβb hcovb
  have hbS : 0 < b₀ * S₀ := mul_pos hb₀ hS₀
  have hSV : ((∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D) / (b₀ * S₀) =
      DJ / D * ∑ i, σ i * (M1J i / DJ / S₀ - M1 i / D / S₀) := by
    rw [hSsum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [hβ i]
    field_simp
  -- the main term
  have hX : |∑ i, σ i * (M1J i / DJ / S₀ - M1 i / D / S₀) - ∑ i, σ i * (gJ i - gI i)| ≤
      (Fintype.card ι : ℝ) * (R * (2 * em)) := by
    rw [← Finset.sum_sub_distrib]
    have h : ∀ i, σ i * (M1J i / DJ / S₀ - M1 i / D / S₀) - σ i * (gJ i - gI i) =
        σ i * ((M1J i / DJ / S₀ - gJ i) - (M1 i / D / S₀ - gI i)) := fun i => by ring
    simp only [h]
    apply abs_sum_mul_le' σ _ R (2 * em) hσ
    intro i
    have := abs_sub (M1J i / DJ / S₀ - gJ i) (M1 i / D / S₀ - gI i)
    linarith [hμJ i, hμI i]
  have hY : |∑ i, σ i * (gJ i - gI i)| ≤ (Fintype.card ι : ℝ) * (R * (2 * G)) := by
    apply abs_sum_mul_le' σ _ R (2 * G) hσ
    intro i
    have := abs_sub (gJ i) (gI i)
    linarith [(hg i).1, (hg i).2]
  have hmain : |DJ / D * ∑ i, σ i * (M1J i / DJ / S₀ - M1 i / D / S₀) -
      r * ∑ i, σ i * (gJ i - gI i)| ≤
      (Fintype.card ι : ℝ) * (R * (2 * em)) + (Fintype.card ι : ℝ) * (R * (2 * G)) * er := by
    have h := abs_mul_sub_mul_le (DJ / D) r (∑ i, σ i * (M1J i / DJ / S₀ - M1 i / D / S₀))
      (∑ i, σ i * (gJ i - gI i)) 1 ((Fintype.card ι : ℝ) * (R * (2 * G)))
      (by rw [abs_of_nonneg hratio0]; exact hratio1) hY
    have hKb : 0 ≤ (Fintype.card ι : ℝ) * (R * (2 * G)) := by
      have := (abs_nonneg _).trans hY
      exact this
    have := mul_le_mul_of_nonneg_left hr hKb
    linarith
  have hdecomp : (P'J / P' - DJ / D) / (b₀ * S₀) - r * ∑ i, σ i * (gJ i - gI i) =
      (P'J / P' - (DJ / D + ((∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D))) /
          (b₀ * S₀) +
        (((∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D) / (b₀ * S₀) -
          r * ∑ i, σ i * (gJ i - gI i)) := by
    ring
  rw [hdecomp, hSV]
  have hAS : |DJ / D + ((∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D)| ≤
      1 + (Fintype.card ι : ℝ) * ((b₀ * R) * (2 * (G + em) * S₀)) :=
    (abs_add_le _ _).trans (add_le_add (by rw [abs_of_nonneg hratio0]; exact hratio1) hS)
  have h1 : |(P'J / P' - (DJ / D + ((∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D))) /
      (b₀ * S₀)| ≤
      2 / D * (ePJ + (u + eP) * ((Fintype.card ι : ℝ) * ((b₀ * R) * (2 * (G + em) * S₀))) +
        eP * (1 + (Fintype.card ι : ℝ) * ((b₀ * R) * (2 * (G + em) * S₀)))) / (b₀ * S₀) := by
    rw [abs_div, abs_of_pos hbS]
    apply div_le_div_of_nonneg_right _ hbS.le
    refine hq.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hprod := mul_le_mul hU hS (abs_nonneg _) (by linarith)
    have hprod' := mul_le_mul_of_nonneg_left hAS heP0
    linarith
  calc
    _ ≤ |(P'J / P' - (DJ / D + ((∑ i, β i * M1J i) / D - DJ / D * (∑ i, β i * M1 i) / D))) /
          (b₀ * S₀)| +
        |DJ / D * ∑ i, σ i * (M1J i / DJ / S₀ - M1 i / D / S₀) -
          r * ∑ i, σ i * (gJ i - gI i)| := abs_add_le _ _
    _ ≤ _ := by linarith [h1, hmain]

/-- Clause (iii): the child conditional mean moves by `O(τβ₀pN)`. -/
theorem child_clause (DJ P'J M'J : ℝ) (M1J M2J σ β mbar : ι → ℝ) (t : ι)
    (b₀ V R Q Q₂ uJ ePJ eMJ Em : ℝ) (hDJ : 0 < DJ) (hb₀ : 0 < b₀)
    (hβ : ∀ i, β i = b₀ * σ i) (hσ : ∀ i, |σ i| ≤ R)
    (hPJ : |P'J - DJ - (∑ i, β i * M1J i) + (∑ i, β i * mbar i) * DJ| ≤ ePJ)
    (hMJ : |M'J - M1J t - (∑ i, β i * M2J i) + (∑ i, β i * mbar i) * M1J t| ≤ eMJ)
    (huJ : |P'J - DJ| ≤ uJ) (hsmall : uJ + ePJ ≤ DJ / 4)
    (hM2 : ∀ i, |M2J i / DJ| ≤ Q * V) (hEm : ∀ i, |M1J i / DJ| ≤ Em) (hEm2 : Em * Em ≤ Q₂ * V) :
    DJ / 2 ≤ P'J ∧
    |M'J / P'J - M1J t / DJ| ≤
      (Fintype.card ι : ℝ) * ((b₀ * R) * ((Q + Q₂) * V)) +
        2 / DJ * (eMJ + (uJ + ePJ) * ((Fintype.card ι : ℝ) * ((b₀ * R) * ((Q + Q₂) * V))) +
          ePJ * (Em + (Fintype.card ι : ℝ) * ((b₀ * R) * ((Q + Q₂) * V)))) := by
  have hu0 : 0 ≤ uJ := (abs_nonneg _).trans huJ
  have heP0 : 0 ≤ ePJ := (abs_nonneg _).trans hPJ
  have hU := abs_first_order_le DJ P'J (∑ i, β i * M1J i) (∑ i, β i * mbar i) uJ ePJ hPJ huJ
  obtain ⟨hDen, hq⟩ := quotient_response M'J P'J (M1J t) DJ (∑ i, β i * M1J i)
    (∑ i, β i * M2J i) (∑ i, β i * mbar i) ePJ eMJ
    ((∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ) hDJ rfl hPJ hMJ
    (hU.trans hsmall) (by linarith)
  refine ⟨hDen, ?_⟩
  have hSsum := first_order_sum_eq β M1J M2J (M1J t) DJ
  have hcovb : ∀ i, |M2J i / DJ - M1J i / DJ * (M1J t / DJ)| ≤ (Q + Q₂) * V := by
    intro i
    have h := abs_sub (M2J i / DJ) (M1J i / DJ * (M1J t / DJ))
    rw [abs_mul] at h
    have h2 := mul_le_mul (hEm i) (hEm t) (abs_nonneg _) ((abs_nonneg _).trans (hEm i))
    linarith [hM2 i]
  have hβb : ∀ i, |β i| ≤ b₀ * R := by
    intro i
    rw [hβ i, abs_mul, abs_of_pos hb₀]
    exact mul_le_mul_of_nonneg_left (hσ i) hb₀.le
  have hS : |(∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ| ≤
      (Fintype.card ι : ℝ) * ((b₀ * R) * ((Q + Q₂) * V)) := by
    rw [hSsum]
    exact abs_sum_mul_le' β (fun i => M2J i / DJ - M1J i / DJ * (M1J t / DJ)) _ _ hβb hcovb
  have hAS : |M1J t / DJ + ((∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ)| ≤
      Em + (Fintype.card ι : ℝ) * ((b₀ * R) * ((Q + Q₂) * V)) :=
    (abs_add_le _ _).trans (add_le_add (hEm t) hS)
  have h1 : |M'J / P'J - (M1J t / DJ +
      ((∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ))| ≤
      2 / DJ * (eMJ + (uJ + ePJ) * ((Fintype.card ι : ℝ) * ((b₀ * R) * ((Q + Q₂) * V))) +
        ePJ * (Em + (Fintype.card ι : ℝ) * ((b₀ * R) * ((Q + Q₂) * V)))) := by
    refine hq.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hprod := mul_le_mul hU hS (abs_nonneg _) (by linarith)
    have hprod' := mul_le_mul_of_nonneg_left hAS heP0
    linarith
  have hdecomp : M'J / P'J - M1J t / DJ =
      (M'J / P'J - (M1J t / DJ +
        ((∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ))) +
        ((∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ) := by
    ring
  rw [hdecomp]
  calc
    _ ≤ |M'J / P'J - (M1J t / DJ +
          ((∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ))| +
        |(∑ i, β i * M2J i) / DJ - M1J t / DJ * (∑ i, β i * M1J i) / DJ| := abs_add_le _ _
    _ ≤ _ := by linarith [h1, hS]

end MajorityDynamics.Idealized.LinearResponse
