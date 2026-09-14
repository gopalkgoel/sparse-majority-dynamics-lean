import MajorityDynamics.GraphProcess.History.Main
import MajorityDynamics.Universal.Section4

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open Universal

/-- Signed block counts agree exactly with the sum of vertex opinions. -/
theorem signed_partition_sum {V : Type*} [Fintype V] {n : ℕ}
    (π : V → Universal.History (n+1)) :
    ∑ s, character (Fin.last n) s * (Local.partSizes π s : ℝ) =
      ∑ v, sign (last (π v)) := by
  classical
  calc
    _ = ∑ s, ∑ v ∈ History.block π s, sign (last (π v)) := by
      apply Finset.sum_congr rfl
      intro s _
      have h : ∀ v ∈ History.block π s, sign (last (π v)) = character (Fin.last n) s := by
        intro v hv
        rw [History.mem_block] at hv
        rw [hv]
        rfl
      rw [Finset.sum_congr rfl h]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (History.block π s).card = Local.partSizes π s := by
        unfold History.block Local.partSizes
        congr 1
        ext v
        simp
      rw [hc]
      ring
    _ = _ := History.sum_block π _

/-- Literal day convention: universal level `n` is paper day `n+1`. -/
theorem signed_actual_partition {N n : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N) :
    ∑ s, character (Fin.last n) s *
      (Local.partSizes (History.actualHistory G c (n+1)) s : ℝ) =
      Paper.lead (Paper.coloringOnDay G c (n+1)) := by
  classical
  rw [signed_partition_sum]
  simp only [History.last_actualHistory,
    Probability.RandomOpinionsReduction.coloringOnDay_fin]
  let d := Paper.coloringOnDay G c (n+1)
  change (∑ v : Fin N, sign (d v)) = 2*(Paper.plusCount d : ℝ)-(N:ℝ)
  have hs (v : Fin N) : sign (d v) = 2*(if d v = false then (1:ℝ) else 0)-1 := by
    cases d v <;> norm_num [sign]
  simp_rw [hs]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.sum_boole, Paper.plusCount]

/-- The deterministic noncritical lead estimate, retaining the finite number
of history errors and the exact positive universal response sum. -/
theorem lead_of_size_errors {n : ℕ} (sizes reference : Universal.History (n+1) → ℝ)
    (a e : ℝ) (href : ∀ s, reference (flip s) = reference s)
    (herr : ∀ s, |sizes s-reference s-a*ε n s| ≤ e) :
    a*(∑ s, character (Fin.last n) s*ε n s) -
      (Fintype.card (Universal.History (n+1)) : ℝ)*e ≤
        ∑ s, character (Fin.last n) s*sizes s := by
  have hs (s : Universal.History (n+1)) :
      character (Fin.last n) s*(reference s+a*ε n s)-e ≤
      character (Fin.last n) s*sizes s := by
    have h := abs_le.mp (herr s)
    unfold character sign
    split <;> nlinarith [h.1,h.2]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hs s)
  have hc := sum_character_of_flip_invariant reference href (Fin.last n)
  calc
    _ = ∑ s, (character (Fin.last n) s*(reference s+a*ε n s)-e) := by
      simp_rw [mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hc]
      simp only [zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ _ := hsum

/-- Critical-day child gains add without losing their coefficient. -/
theorem lead_of_critical_gains {n : ℕ} (sizes : Universal.History (n+1) → ℝ)
    (N ζ : ℝ)
    (hgain : ∀ s, ζ*N ≤ character (Fin.last n) s*(sizes s-N*ν n s)) :
    (Fintype.card (Universal.History (n+1)) : ℝ)*ζ*N ≤
      ∑ s, character (Fin.last n) s*sizes s := by
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hgain s)
  have hc := ν_signed_sum n (Fin.last n)
  simp_rw [mul_sub] at h
  rw [Finset.sum_sub_distrib] at h
  have hz : ∑ s, character (Fin.last n) s*(N*ν n s) = 0 := by
    calc
      _ = N*∑ s, character (Fin.last n) s*ν n s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 0 := by rw [hc,mul_zero]
  rw [hz,sub_zero] at h
  simpa [mul_assoc] using h

end MajorityDynamics.GraphProcess.FaithfulTrajectory
