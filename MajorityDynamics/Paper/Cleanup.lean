import MajorityDynamics.Paper.Contraction

/-!
# Iterating the deterministic contraction

This file connects the concrete majority process to the cleanup stage. The
finite theorem exposes just three numerical sufficient conditions; the next
file verifies that these conditions hold uniformly in the density range.
-/

noncomputable section
namespace MajorityDynamics.Paper

theorem majority_iterate_bound {N : ℕ} (G : Graph N) (c : Coloring N)
    (p : unitInterval) (β : ℝ) (hpN : 0 < (p : ℝ) * N)
    (hj : Jumbled G p β) (hd : minimumDegree G p)
    (hm : ((minusVertices c).card : ℝ) ≤ (N : ℝ) / 5)
    (hq : 16 * β ^ 2 / ((p : ℝ) * N) ^ 2 ≤ 1) (n : ℕ) :
    ((minusVertices ((nextColoring G)^[n] c)).card : ℝ) ≤
      (16 * β ^ 2 / ((p : ℝ) * N) ^ 2) ^ n * ((N : ℝ) / 5) := by
  let q := 16 * β ^ 2 / ((p : ℝ) * N) ^ 2
  have hq0 : 0 ≤ q := by positivity
  change _ ≤ q ^ n * _
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hsmall : ((minusVertices ((nextColoring G)^[n] c)).card : ℝ) ≤ (N : ℝ) / 5 := by
      have hpower : q ^ n ≤ 1 := pow_le_one₀ hq0 hq
      have hbound := mul_le_mul_of_nonneg_right hpower (by positivity : 0 ≤ (N : ℝ) / 5)
      exact ih.trans (by simpa using hbound)
    calc
      _ ≤ q * ((minusVertices ((nextColoring G)^[n] c)).card : ℝ) :=
        jumbled_majority_contract G _ p β hpN hj hd hsmall
      _ ≤ q * (q ^ n * ((N : ℝ) / 5)) := mul_le_mul_of_nonneg_left ih hq0
      _ = q ^ (n + 1) * ((N : ℝ) / 5) := by rw [pow_succ]; ring

/-- A finite sufficient condition for cleanup on the actual graph and coloring. -/
theorem cleanup_of_numerical_bounds {N : ℕ} (G : Graph N) (c : Coloring N)
    (θ : ℝ) (p : unitInterval) (CJ : ℝ) (hCJ : 0 < CJ)
    (hpN : 0 < (p : ℝ) * N)
    (hlog : 10 * CJ ≤ Real.log N)
    (hq : 16 * CJ ^ 2 / ((p : ℝ) * N) ≤ 1)
    (hfinal : (16 * CJ ^ 2 / ((p : ℝ) * N)) ^ expansionDay θ * ((N : ℝ) / 5) < 1)
    (hps : G ∈ pseudorandomEvent p CJ) (hexp : G ∈ expansionEvent θ p c) :
    G ∈ successEvent θ c := by
  let β := CJ * Real.sqrt ((p : ℝ) * N)
  let cK := coloringOnDay G c (expansionDay θ)
  have hspos := Real.sqrt_pos.mpr hpN
  have hsquare := Real.sq_sqrt hpN.le
  have hβ : 0 < β := mul_pos hCJ hspos
  have hthreshold : 10 * β ≤ (p : ℝ) * lead cK := by
    have hp : 0 ≤ (p : ℝ) := p.property.1
    have h1 := mul_le_mul_of_nonneg_left hexp hp
    have h2 := mul_le_mul_of_nonneg_left hlog (le_of_lt hspos)
    have heq : (p : ℝ) * ((N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N) =
        Real.sqrt ((p : ℝ) * N) * Real.log N := by
      field_simp
      nlinarith
    change (p : ℝ) * ((N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N) ≤
      (p : ℝ) * lead cK at h1
    rw [heq] at h1
    dsimp [β]
    nlinarith
  have hratio : 16 * β ^ 2 / ((p : ℝ) * N) ^ 2 = 16 * CJ ^ 2 / ((p : ℝ) * N) := by
    dsimp [β]
    rw [mul_pow, hsquare]
    field_simp
  have hj : Jumbled G p β := hps.2
  have hjump := jumbled_majority_jump G cK p β hβ hj hthreshold
  have hiter := majority_iterate_bound G (nextColoring G cK) p β hpN hj hps.1 hjump
    (by simpa only [hratio] using hq) (expansionDay θ)
  rw [hratio] at hiter
  have hzero := (minus_card_lt_one_iff _).mp (hiter.trans_lt hfinal)
  have hK : 1 ≤ expansionDay θ := by simp [expansionDay]
  have heq : (nextColoring G)^[expansionDay θ] (nextColoring G cK) =
      coloringOnDay G c (convergenceDay θ) := by
    dsimp [cK, coloringOnDay, convergenceDay]
    rw [← Function.iterate_succ_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  rw [heq] at hzero
  exact hzero

end MajorityDynamics.Paper
