import MajorityDynamics.Universal.Main

/-!
# Universal nondegeneracy constants

This proves `lem:universal-nondegeneracy` in §4 of `latest/main.tex` for the
actual recursively constructed arrays. The hypotheses needed here were proved
with the Gaussian recursion: no response or coherence result is needed.

As throughout this directory, `n` denotes paper day `k = n + 1`. In particular,
the family of earlier signed forms is empty at `n = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

/-- A finite positive family has a common positive lower bound, including when
the index type is empty. This is the finite-minimum argument used below. -/
private theorem positive_family_lower_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  have aux : ∀ s : Finset ι, ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hbound⟩ := ih
      refine ⟨min (f a) c, lt_min (hf a) hc, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound i hi)
  obtain ⟨c, hc, hbound⟩ := aux Finset.univ
  exact ⟨c, hc, fun i => hbound i (Finset.mem_univ i)⟩

/-- The paper's uniform inequalities, stated using the original tie events. -/
structure UniversalNondegeneracy (n : ℕ) (φ ζ : ℝ) : Prop where
  probability_pos : 0 < φ
  probability_le_quarter : φ ≤ 1 / 4
  probability_lt_half : φ < 1 / 2
  separation_pos : 0 < ζ
  history : ∀ s, φ ≤ (dayLaw n s).real (historyEvent s)
  split : ∀ s b, φ ≤ (historyLaw n s).real (childEvent s b) ∧
    (historyLaw n s).real (childEvent s b) ≤ 1 - φ
  separation : ∀ s (r : Fin n), ζ ≤ sign (bits (n + 1) s r.succ) *
    imbalance r.castSucc (WithLp.toLp 2 (fun t => ν n t * μ n s t))

theorem universal_history_probability_pos (n : ℕ) (s : History (n + 1)) :
    0 < (dayLaw n s).real (historyEvent s) := by
  rw [dayLaw, measureReal_congr (historyEvent_ae_eq_cone s (ν n) (ν_positive n) (γ n s))]
  exact history_mass_real_pos s (ν n) (ν_positive n) (γ n s)

theorem universal_split_probability_pos (n : ℕ) (s : History (n + 1)) (b : Bool) :
    0 < (historyLaw n s).real (childEvent s b) := by
  change 0 < (ConditionalGaussian.condition (rowLaw (ν n) (γ n s))
    (historyEvent s)).real (childEvent s b)
  rw [← branchProbability_eq_event_condition s (ν n) (ν_positive n)]
  exact branchProbability_pos s (ν n) (ν_positive n) (γ n s) b

theorem universal_split_probability_add (n : ℕ) (s : History (n + 1)) :
    (historyLaw n s).real (childEvent s false) +
      (historyLaw n s).real (childEvent s true) = 1 := by
  change (ConditionalGaussian.condition (rowLaw (ν n) (γ n s))
    (historyEvent s)).real (childEvent s false) +
    (ConditionalGaussian.condition (rowLaw (ν n) (γ n s))
      (historyEvent s)).real (childEvent s true) = 1
  rw [← branchProbability_eq_event_condition s (ν n) (ν_positive n),
    ← branchProbability_eq_event_condition s (ν n) (ν_positive n)]
  exact branchProbability_add s (ν n) (ν_positive n) (γ n s)

theorem universal_split_probability_lt_one (n : ℕ) (s : History (n + 1)) (b : Bool) :
    (historyLaw n s).real (childEvent s b) < 1 := by
  have hsum := universal_split_probability_add n s
  have hfalse := universal_split_probability_pos n s false
  have htrue := universal_split_probability_pos n s true
  cases b <;> linarith

/-- `lem:universal-nondegeneracy`, with no outstanding positivity or coherence
hypotheses. Constants depend only on the day. -/
theorem universal_nondegeneracy_exists (n : ℕ) :
    ∃ φ ζ : ℝ, UniversalNondegeneracy n φ ζ := by
  obtain ⟨a, ha, hhistory⟩ := positive_family_lower_bound
    (fun s => (dayLaw n s).real (historyEvent s)) (universal_history_probability_pos n)
  obtain ⟨q, hq, hsplit⟩ := positive_family_lower_bound
    (fun sb : History (n + 1) × Bool => (historyLaw n sb.1).real (childEvent sb.1 sb.2))
    (fun sb => universal_split_probability_pos n sb.1 sb.2)
  obtain ⟨c, hc, hcomplement⟩ := positive_family_lower_bound
    (fun sb : History (n + 1) × Bool => 1 - (historyLaw n sb.1).real (childEvent sb.1 sb.2))
    (fun sb => sub_pos.mpr (universal_split_probability_lt_one n sb.1 sb.2))
  obtain ⟨ζ, hζ, hseparation⟩ := positive_family_lower_bound
    (fun sr : History (n + 1) × Fin n => sign (bits (n + 1) sr.1 sr.2.succ) *
      imbalance sr.2.castSucc (WithLp.toLp 2 (fun t => ν n t * μ n sr.1 t)))
    (fun sr => (mem_historyCone sr.1 _).mp (weightedRow_mem n sr.1) sr.2)
  let φ : ℝ := min (1 / 4) (min a (min q c))
  have hφ : 0 < φ := lt_min (by norm_num) (lt_min ha (lt_min hq hc))
  have hquarter : φ ≤ 1 / 4 := min_le_left _ _
  have hrest : φ ≤ min a (min q c) := min_le_right _ _
  have hφa : φ ≤ a := hrest.trans (min_le_left _ _)
  have hφq : φ ≤ q := (hrest.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hφc : φ ≤ c := (hrest.trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨φ, ζ, hφ, hquarter, by linarith, hζ,
    fun s => hφa.trans (hhistory s), ?_, fun s r => hseparation (s, r)⟩
  intro s b
  exact ⟨hφq.trans (hsplit (s, b)), by linarith [hcomplement (s, b)]⟩

/-- A fixed universal probability margin for paper day `n + 1`. -/
def φStar (n : ℕ) : ℝ := (universal_nondegeneracy_exists n).choose

/-- A fixed universal separation margin; the empty day-one family uses `1`. -/
def ζStar (n : ℕ) : ℝ :=
  if n = 0 then 1 else ((universal_nondegeneracy_exists n).choose_spec).choose

@[simp] theorem ζStar_zero : ζStar 0 = 1 := by simp [ζStar]

/-- The chosen constants satisfy every bound in the paper's lemma. -/
theorem universal_nondegeneracy (n : ℕ) : UniversalNondegeneracy n (φStar n) (ζStar n) := by
  have h := ((universal_nondegeneracy_exists n).choose_spec).choose_spec
  change UniversalNondegeneracy n (φStar n) _ at h
  by_cases hn : n = 0
  · subst n
    exact ⟨h.probability_pos, h.probability_le_quarter, h.probability_lt_half,
      by simp, h.history, h.split, fun _ r => Fin.elim0 r⟩
  · simpa only [ζStar, if_neg hn] using h

end MajorityDynamics.Universal
