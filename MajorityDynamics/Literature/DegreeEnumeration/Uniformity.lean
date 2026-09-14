import MajorityDynamics.Literature.DegreeEnumeration.Consequences

/-! Finite maximization converts estimates along every selected sequence into
an estimate uniform over all finite data. This is a proved logical step,
separate from the numerical source applicability hypotheses. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Literature.DegreeEnumeration

theorem relativeApproximation_iff_div {δ P Q : ℝ} (hQ : Q ≠ 0) :
    RelativeApproximation δ P Q ↔ |P / Q - 1| ≤ δ := by
  constructor
  · rintro ⟨ε, hε, rfl⟩
    simpa only [mul_div_cancel_left₀ _ hQ, add_sub_cancel_left] using hε
  · intro h
    refine ⟨P / Q - 1, h, ?_⟩
    field_simp
    ring

theorem relativeApproximation_iff_cost {C E P Q : ℝ} (hE : 0 < E) (hQ : Q ≠ 0) :
    RelativeApproximation (C * E) P Q ↔ |P / Q - 1| / E ≤ C := by
  rw [relativeApproximation_iff_div hQ, div_le_iff₀ hE]

/-- No compactness assumption on the set of sequences is used: at each index
choose data with maximal normalized relative error. Invalid data have cost zero. -/
theorem uniform_relativeApproximation_of_sequences
    {A : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Nonempty (A n)]
    (valid : ∀ n, A n → Prop) (E P Q : ∀ n, A n → ℝ)
    (hE : ∀ n a, valid n a → 0 < E n a)
    (hQ : ∀ n a, valid n a → Q n a ≠ 0)
    (hseq : ∀ f : ∀ n, A n, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      valid n (f n) → RelativeApproximation (C * E n (f n)) (P n (f n)) (Q n (f n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ a, valid n a →
      RelativeApproximation (C * E n a) (P n a) (Q n a) := by
  let cost : ∀ n, A n → ℝ := fun n a =>
    if valid n a then |P n a / Q n a - 1| / E n a else 0
  have hmax : ∀ n, ∃ a : A n, ∀ b, cost n b ≤ cost n a := by
    intro n
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (cost n) Finset.univ_nonempty
    exact ⟨a, fun b => ha b (Finset.mem_univ _)⟩
  choose f hf using hmax
  obtain ⟨C, hC, hc⟩ := hseq f
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc] with n hn
  have hcost : cost n (f n) ≤ C := by
    by_cases hv : valid n (f n)
    · simpa only [cost, if_pos hv] using
        (relativeApproximation_iff_cost (hE n (f n) hv) (hQ n (f n) hv)).mp (hn hv)
    · simpa only [cost, if_neg hv] using hC.le
  intro a ha
  apply (relativeApproximation_iff_cost (hE n a ha) (hQ n a ha)).mpr
  have hh := (hf n a).trans hcost
  simpa only [cost, if_pos ha] using hh

end MajorityDynamics.Literature.DegreeEnumeration
