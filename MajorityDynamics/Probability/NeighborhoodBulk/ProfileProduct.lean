import MajorityDynamics.Probability.NeighborhoodBulk.BernoulliProfile

noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk

theorem profile_product {V : Type*} (A R : Finset V) (d : V → ℝ)
    (n : ℕ) (T p H D L : ℝ) (hT : 1 ≤ T) (hp : 0 < p) (hp16 : p ≤ 1 / 16)
    (hH : 2 ≤ H) (hDlo : H - 1 ≤ D) (hDhi : D ≤ H) (hL : 1 ≤ L)
    (hscale : 2 * L ≤ Real.sqrt (p * H)) (hsparse : (n : ℝ) * p ^ 2 ≤ 1)
    (hside : (n : ℝ) / T ≤ H) (hA : A.card ≤ n) (hA' : n ≤ A.card + 1)
    (hR : R ⊆ A) (hk : (R.card : ℝ) ≤ 2 * p * n)
    (hd : ∀ i ∈ A, |d i - p * H| ≤ Real.sqrt (p * H) * L) :
    0 < bernoulliProduct A R (fun i => d i / D) ∧
      |Real.log (bernoulliProduct A R (fun i => d i / D)) - R.card * Real.log p + p * n -
        linearWeight A R p H d| ≤ 32 * (T + 1) * L ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hH0 : 0 < H := by linarith
  have hx : 0 < p * H := mul_pos hp hH0
  have hL0 : 0 ≤ L := by linarith
  have hp1 : p ≤ 1 := by linarith
  let O := A \ R
  have hentry := fun i hi => profile_entry p H D L (d i) hp hp16 hH hDlo hDhi hL0 hscale (hd i hi)
  have hsel : 0 < ∏ i ∈ R, d i / D := Finset.prod_pos (fun i hi => (hentry i (hR hi)).1)
  have hout : 0 < ∏ i ∈ O, (1 - d i / D) := Finset.prod_pos
    (fun i hi => sub_pos.mpr (hentry i (Finset.mem_sdiff.mp hi).1).2.1)
  have hpositive : 0 < bernoulliProduct A R (fun i => d i / D) := mul_pos hsel hout
  have hcard : O.card + R.card = A.card := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset hR]
    have := Finset.card_le_card hR
    omega
  have hcardr : (O.card : ℝ) + R.card = A.card := by exact_mod_cast hcard
  have hAreal : (A.card : ℝ) ≤ n := by exact_mod_cast hA
  have hAreal' : (n : ℝ) ≤ (A.card : ℝ) + 1 := by exact_mod_cast hA'
  have hOreal : (O.card : ℝ) ≤ n := by exact_mod_cast (by omega : O.card ≤ n)
  have hlog : Real.log (bernoulliProduct A R (fun i => d i / D)) =
      (∑ i ∈ R, Real.log (d i / D)) + ∑ i ∈ O, Real.log (1 - d i / D) := by
    rw [bernoulliProduct, Real.log_mul hsel.ne' hout.ne',
      Real.log_prod (fun i hi => (hentry i (hR hi)).1.ne'),
      Real.log_prod (fun i hi => (sub_pos.mpr (hentry i (Finset.mem_sdiff.mp hi).1).2.1).ne')]
  have hdelta : (∑ i ∈ O, (d i - p * H) / H) = (∑ i ∈ O, d i / H) - O.card * p := by
    simp only [sub_div, mul_div_cancel_right₀ p hH0.ne', Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
  have hid : Real.log (bernoulliProduct A R (fun i => d i / D)) - R.card * Real.log p + p * n -
      linearWeight A R p H d =
      (∑ i ∈ R, (Real.log (d i / D) - Real.log p - (d i - p * H) / (p * H))) +
      (∑ i ∈ O, (Real.log (1 - d i / D) + d i / H)) + p * ((n : ℝ) - A.card + R.card) := by
    rw [hlog]
    simp only [linearWeight, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul]
    rw [hdelta, ← hcardr]
    ring
  have hselerr : |∑ i ∈ R, (Real.log (d i / D) - Real.log p - (d i - p * H) / (p * H))| ≤
      R.card * (2 * L ^ 2 / (p * H) + 2 / H) := by
    calc
      _ ≤ ∑ i ∈ R, |Real.log (d i / D) - Real.log p - (d i - p * H) / (p * H)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ R, (2 * L ^ 2 / (p * H) + 2 / H) :=
        Finset.sum_le_sum (fun i hi => (hentry i (hR hi)).2.2.1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have houterr : |∑ i ∈ O, (Real.log (1 - d i / D) + d i / H)| ≤
      O.card * (18 * p ^ 2 + 3 * p / H) := by
    calc
      _ ≤ ∑ i ∈ O, |Real.log (1 - d i / D) + d i / H| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ O, (18 * p ^ 2 + 3 * p / H) :=
        Finset.sum_le_sum (fun i hi => (hentry i (Finset.mem_sdiff.mp hi).1).2.2.2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hnH : (n : ℝ) ≤ T * H := by have hh := (div_le_iff₀ hT0).mp hside; nlinarith
  have hkx : (R.card : ℝ) / (p * H) ≤ 2 * T := by
    apply (div_le_iff₀ hx).mpr
    have hh := mul_le_mul_of_nonneg_left hnH (show 0 ≤ 2 * p by positivity)
    nlinarith only [hk, hh]
  have hkH : (R.card : ℝ) / H ≤ 2 * T * p := by
    apply (div_le_iff₀ hH0).mpr
    have hh := mul_le_mul_of_nonneg_left hnH (show 0 ≤ 2 * p by positivity)
    nlinarith only [hk, hh]
  have hsbound : R.card * (2 * L ^ 2 / (p * H) + 2 / H) ≤ 4 * T * L ^ 2 + 4 * T := by
    have h1 := mul_le_mul_of_nonneg_left hkx (show 0 ≤ 2 * L ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hkH (show (0 : ℝ) ≤ 2 by norm_num)
    have h3 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 4 * T by positivity)
    have he : R.card * (2 * L ^ 2 / (p * H) + 2 / H) =
        2 * L ^ 2 * ((R.card : ℝ) / (p * H)) + 2 * ((R.card : ℝ) / H) := by ring
    rw [he]
    nlinarith only [h1, h2, h3]
  have hnHdiv : (n : ℝ) / H ≤ T := (div_le_iff₀ hH0).mpr hnH
  have hobound : O.card * (18 * p ^ 2 + 3 * p / H) ≤ 18 + 3 * T := by
    have h0 := mul_le_mul_of_nonneg_right hOreal (show 0 ≤ 18 * p ^ 2 + 3 * p / H by positivity)
    have h1 := mul_le_mul_of_nonneg_left hnHdiv (show 0 ≤ 3 * p by positivity)
    have h2 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 3 * T by positivity)
    have he : (n : ℝ) * (18 * p ^ 2 + 3 * p / H) = 18 * ((n : ℝ) * p ^ 2) + 3 * p * ((n : ℝ) / H) := by ring
    rw [he] at h0
    nlinarith only [h0, h1, h2, hsparse]
  have hextra : |p * ((n : ℝ) - A.card + R.card)| ≤ 3 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ p * ((n : ℝ) - A.card + R.card))]
    have hh := mul_le_mul_of_nonneg_left hk hp.le
    have hA1 := mul_le_mul_of_nonneg_left hAreal' hp.le
    nlinarith only [hh, hA1, hp1, hsparse]
  refine ⟨hpositive, ?_⟩
  rw [hid]
  calc
    _ ≤ |(∑ i ∈ R, (Real.log (d i / D) - Real.log p - (d i - p * H) / (p * H))) +
        (∑ i ∈ O, (Real.log (1 - d i / D) + d i / H))| +
          |p * ((n : ℝ) - A.card + R.card)| := abs_add_le _ _
    _ ≤ (|∑ i ∈ R, (Real.log (d i / D) - Real.log p - (d i - p * H) / (p * H))| +
        |∑ i ∈ O, (Real.log (1 - d i / D) + d i / H)|) +
          |p * ((n : ℝ) - A.card + R.card)| := by gcongr; exact abs_add_le _ _
    _ ≤ (4 * T * L ^ 2 + 4 * T) + (18 + 3 * T) + 3 :=
      add_le_add (add_le_add (hselerr.trans hsbound) (houterr.trans hobound)) hextra
    _ ≤ _ := by
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
      nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hL2)]

end MajorityDynamics.Probability.NeighborhoodBulk
