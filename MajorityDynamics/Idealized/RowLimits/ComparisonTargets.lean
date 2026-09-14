import MajorityDynamics.Idealized.RowLimits.Comparison
import MajorityDynamics.Idealized.RowLimits.EventsGaussian

/-! The fixed compact Gaussian boxes, uniform over every history and child. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
open MajorityDynamics.Universal MajorityDynamics.Analysis
namespace MajorityDynamics.Idealized.RowLimits

variable {n : ℕ}

/-- A finite family of positive constants has one common positive lower bound. -/
theorem finite_common_positive {I : Type*} [Fintype I] [Nonempty I]
    (a : I → ℝ) (ha : ∀ i, 0 < a i) : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ a i := by
  classical
  refine ⟨Finset.univ.inf' Finset.univ_nonempty a, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun i _ => ha i
  · intro i
    exact Finset.inf'_le a (Finset.mem_univ i)

def gaussianBox (n r : ℕ) (R T : ℝ) :
    Set (GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) r) :=
  parameterBox (2 * R) (2 * T + 1) (fun t => ν n t / 2) (fun t => 2 * ν n t)

theorem gaussianBox_regular (r : ℕ) (M : Matrix (Fin r) (History (n + 1)) ℝ)
    (hM : M.rank = r) (R T : ℝ) : GaussianRegularity.RegularOn M (gaussianBox n r R T) :=
  parameterBox_regular M hM _ _ _ _ (fun t => half_pos (ν_positive n t))

theorem historyParameters_mem_box {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    {σ : Row (n + 1)} (hσ : ∀ t, |σ t| ≤ R) :
    historyParameters σ ∈ gaussianBox n n R T := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro t
    have := abs_le.mp (hσ t)
    change - (2 * R) ≤ σ t ∧ σ t ≤ 2 * R
    constructor <;> linarith
  · intro t
    change ν n t / 2 ≤ ν n t ∧ ν n t ≤ 2 * ν n t
    have := ν_positive n t
    constructor <;> linarith
  · intro i
    change -(2 * T + 1) ≤ 0 ∧ 0 ≤ 2 * T + 1
    constructor <;> linarith

theorem childParameters_mem_box {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    {σ : Row (n + 1)} (hσ : ∀ t, |σ t| ≤ R) (b : Bool) {u : ℝ}
    (hu : |u| ≤ T) : childParameters σ b u ∈ gaussianBox n (n + 1) R T := by
  refine ⟨(historyParameters_mem_box hR hT hσ).1, ?_⟩
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · change -(2 * T + 1) ≤ childThreshold b u j.castSucc ∧ childThreshold b u j.castSucc ≤ 2 * T + 1
    rw [childThreshold_castSucc]
    constructor <;> linarith
  · change -(2 * T + 1) ≤ childThreshold b u (Fin.last n) ∧ childThreshold b u (Fin.last n) ≤ 2 * T + 1
    rw [childThreshold_last]
    have hbu : |sign b * u| ≤ T := by cases b <;> simpa [sign] using hu
    have := abs_le.mp hbu
    constructor <;> linarith

/-- One lower bound works for every actual and target Gaussian parameter in
all boxes. It is selected before θ, ell, N, p, sizes, or ξ. -/
theorem gaussian_boxes_uniform_lower (n : ℕ) (R T : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      (∀ s : History (n + 1), ∀ z ∈ gaussianBox n n R T,
        c ≤ GaussianRegularity.mass (historyMatrix s) z) ∧
      (∀ (s : History (n + 1)) (b : Bool), ∀ z ∈ gaussianBox n (n + 1) R T,
        c ≤ GaussianRegularity.mass (childMatrix s b) z) := by
  classical
  have hh := fun s : History (n + 1) =>
    (gaussianBox_regular n (historyMatrix s) (historyMatrix_rank s) R T).positive_lower_bound
  have hc := fun (s : History (n + 1)) (b : Bool) =>
    (gaussianBox_regular (n + 1) (childMatrix s b) (childMatrix_rank s b) R T).positive_lower_bound
  choose a ha hmass using hh
  choose b hb bmass using hc
  let f : History (n + 1) × Option Bool → ℝ := fun i =>
    match i.2 with | none => a i.1 | some u => b i.1 u
  have hf : ∀ i, 0 < f i := by
    rintro ⟨s, _ | u⟩
    · exact ha s
    · exact hb s u
  obtain ⟨c, hc, hf⟩ := finite_common_positive f hf
  refine ⟨c, hc, ?_, ?_⟩
  · intro s z hz
    exact (hf (s, none)).trans (hmass s z hz)
  · intro s u z hz
    exact (hf (s, some u)).trans (bmass s u z hz)

/-- Bounds and regularity used for the E.3 comparisons, with common constants. -/
structure GaussianControl {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ)
    (P : Set (GaussianRegularity.Parameters d r)) (B : ℝ) (L : ℝ≥0) : Prop where
  first_bound : ∀ p ∈ P, ∀ t, |GaussianRegularity.firstMoment M t p| ≤ B
  second_bound : ∀ p ∈ P, ∀ t t', |GaussianRegularity.secondMoment M t t' p| ≤ B
  mass_lipschitz : LipschitzOnWith L (GaussianRegularity.mass M) P
  first_lipschitz : ∀ t, LipschitzOnWith L (GaussianRegularity.firstMoment M t) P
  second_lipschitz : ∀ t t', LipschitzOnWith L (GaussianRegularity.secondMoment M t t') P
  mean_lipschitz : ∀ t, LipschitzOnWith L (GaussianRegularity.conditionalFirst M t) P
  conditional_second_lipschitz : ∀ t t',
    LipschitzOnWith L (GaussianRegularity.conditionalSecond M t t') P
  covariance_lipschitz : ∀ t t',
    LipschitzOnWith L (GaussianRegularity.conditionalCovariance M t t') P

theorem GaussianControl.mono {d r : ℕ} {M : Matrix (Fin r) (Fin d) ℝ}
    {P : Set (GaussianRegularity.Parameters d r)} {B B' : ℝ} {L L' : ℝ≥0}
    (h : GaussianControl M P B L) (hB : B ≤ B') (hL : L ≤ L') :
    GaussianControl M P B' L' := by
  exact ⟨fun p hp t => (h.first_bound p hp t).trans hB,
    fun p hp t t' => (h.second_bound p hp t t').trans hB,
    h.mass_lipschitz.weaken hL, fun t => (h.first_lipschitz t).weaken hL,
    fun t t' => (h.second_lipschitz t t').weaken hL,
    fun t => (h.mean_lipschitz t).weaken hL,
    fun t t' => (h.conditional_second_lipschitz t t').weaken hL,
    fun t t' => (h.covariance_lipschitz t t').weaken hL⟩

theorem gaussianBox_control (r : ℕ) (M : Matrix (Fin r) (History (n + 1)) ℝ)
    (hM : M.rank = r) (R T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ L : ℝ≥0, GaussianControl M (gaussianBox n r R T) B L := by
  obtain ⟨B, hB, hb₁, hb₂⟩ := compact_raw_bounds M hM
    (parameterBox_compact _ _ _ _) (parameterBox_positive (fun t => half_pos (ν_positive n t)))
  obtain ⟨L, hl₀, hl₁, hl₂, hl₃, hl₄, hl₅⟩ := (gaussianBox_regular r M hM R T).lipschitz
  exact ⟨B, hB, L, hb₁, hb₂, hl₀, hl₁, hl₂, hl₃, hl₄, hl₅⟩

/-- Raw bounds and every E.2 Lipschitz constant can be made uniform over the
finite history and child choices. These constants depend only on n,R,T. -/
theorem gaussian_boxes_uniform_control (n : ℕ) (R T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ L : ℝ≥0,
      (∀ s : History (n + 1), GaussianControl (historyMatrix s) (gaussianBox n n R T) B L) ∧
      (∀ (s : History (n + 1)) (b : Bool),
        GaussianControl (childMatrix s b) (gaussianBox n (n + 1) R T) B L) := by
  classical
  choose A hA L hH using fun s : History (n + 1) =>
    gaussianBox_control n (historyMatrix s) (historyMatrix_rank s) R T
  choose C hC K hCk using fun (s : History (n + 1)) (b : Bool) =>
    gaussianBox_control (n + 1) (childMatrix s b) (childMatrix_rank s b) R T
  let B := (∑ s, A s) + ∑ s, ∑ b, C s b
  let Q := (∑ s, L s) + ∑ s, ∑ b, K s b
  have hAnon : 0 ≤ ∑ s, A s := Finset.sum_nonneg fun s _ => hA s
  have hCnon : 0 ≤ ∑ s, ∑ b, C s b :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun b _ => hC s b
  refine ⟨B, add_nonneg hAnon hCnon, Q, ?_, ?_⟩
  · intro s
    apply (hH s).mono
    · exact (Finset.single_le_sum (f := A) (fun i _ => hA i) (Finset.mem_univ s)).trans
        (le_add_of_nonneg_right hCnon)
    · exact (Finset.single_le_sum (f := L) (fun _ _ => zero_le) (Finset.mem_univ s)).trans
        (le_add_of_nonneg_right (zero_le))
  · intro s b
    apply (hCk s b).mono
    · exact ((Finset.single_le_sum (f := C s) (fun i _ => hC s i) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun s => ∑ b, C s b)
          (fun s _ => Finset.sum_nonneg fun b _ => hC s b) (Finset.mem_univ s))).trans
        (le_add_of_nonneg_left hAnon)
    · exact ((Finset.single_le_sum (f := K s) (fun _ _ => zero_le) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun s => ∑ b, K s b)
          (fun _ _ => zero_le) (Finset.mem_univ s))).trans
        (le_add_of_nonneg_left (zero_le))

/-- The probability lower bounds in E.3, including arbitrary bounded edge-day
shifts. No closeness or small-shift premise enters this conclusion. -/
theorem gaussian_probabilities_uniform_lower (n : ℕ) {R T : ℝ}
    (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : History (n + 1)) (σ : Row (n + 1)),
      (∀ t, |σ t| ≤ R) → c ≤ gaussianMass σ (historyEvent s) ∧
      ∀ (b : Bool) (u : ℝ), |u| ≤ T → c ≤ gaussianMass σ (shiftedChildEvent s b u) := by
  obtain ⟨c, hc, hh, hb⟩ := gaussian_boxes_uniform_lower n R T
  refine ⟨c, hc, ?_⟩
  intro s σ hσ
  constructor
  · rw [gaussianMass_history_eq]
    exact hh s _ (historyParameters_mem_box hR hT hσ)
  · intro b u hu
    rw [gaussianMass_child_eq]
    exact hb s b _ (childParameters_mem_box hR hT hσ b hu)

theorem childParameters_dist_le (σ : Row (n + 1)) (b : Bool) (u v : ℝ) :
    dist (childParameters σ b u) (childParameters σ b v) ≤
      (Fintype.card (Fin (n + 1) → Bool) + (n + 1) + 1 : ℝ) * |u - v| := by
  have h : dist (childParameters σ b u) (childParameters σ b v) ≤
      ((Fintype.card (Fin (n + 1) → Bool) : ℝ) + ((n + 1 : ℕ) : ℝ) + 1) * |u - v| := by
    apply parameters_dist_le_of_coordinates (abs_nonneg _)
    · intro i
      simp only [childParameters, sub_self, abs_zero]
      exact abs_nonneg _
    · intro i
      simp only [childParameters, sub_self, abs_zero]
      exact abs_nonneg _
    · intro i
      change |childThreshold b u i - childThreshold b v i| ≤ |u - v|
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp only [childThreshold_castSucc, sub_self, abs_zero]
        exact abs_nonneg _
      · simp only [childThreshold_last, ← mul_sub, abs_mul]
        cases b <;> simp [sign]
  simpa using h

/-- The final small-shift clause of E.3 uses these direct conditional-mean
bounds; it does not require the shifted event to be unchanged. -/
theorem child_shift_comparison {R T B : ℝ} {L : ℝ≥0}
    (hR : 0 ≤ R) (hT : 0 ≤ T) (s : History (n + 1)) (b : Bool)
    (hcontrol : GaussianControl (childMatrix s b) (gaussianBox n (n + 1) R T) B L)
    (σ : Row (n + 1)) (hσ : ∀ t, |σ t| ≤ R) {u v : ℝ}
    (hu : |u| ≤ T) (hv : |v| ≤ T) :
    let e := (L : ℝ) *
      ((Fintype.card (Fin (n + 1) → Bool) + (n + 1) + 1 : ℝ) * |u - v|)
    |gaussianMass σ (shiftedChildEvent s b u) -
      gaussianMass σ (shiftedChildEvent s b v)| ≤ e ∧
    ∀ t, |gaussianMean σ (shiftedChildEvent s b u) t -
      gaussianMean σ (shiftedChildEvent s b v) t| ≤ e := by
  have hpu := childParameters_mem_box hR hT hσ b hu
  have hpv := childParameters_mem_box hR hT hσ b hv
  have hd := childParameters_dist_le σ b u v
  dsimp only
  constructor
  · rw [gaussianMass_child_eq, gaussianMass_child_eq]
    exact abs_sub_le_of_lipschitz hcontrol.mass_lipschitz hpu hpv hd
  · intro t
    rw [gaussianMean_child_eq, gaussianMean_child_eq]
    exact abs_sub_le_of_lipschitz (hcontrol.mean_lipschitz t) hpu hpv hd

end MajorityDynamics.Idealized.RowLimits
