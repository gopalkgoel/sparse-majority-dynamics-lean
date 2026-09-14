import MajorityDynamics.Analysis.GaussianRegularity.Main

/-!
# Compact Gaussian comparison and normalization

These are the quantitative normalization steps in Appendix E.3. The compact
Gaussian estimates are obtained from the proved E.2 theorem. The ratio estimate
keeps a separate lower bound for the *actual* binomial denominator: the paper's
parameter ξ is bounded, but need not tend to zero.
-/

noncomputable section
open Set MeasureTheory
open scoped NNReal
open MajorityDynamics.Analysis

namespace MajorityDynamics.Idealized.RowLimits

/-- Lipschitz comparison in the real-valued form used for moment errors. -/
theorem abs_sub_le_of_lipschitz {X : Type*} [PseudoMetricSpace X]
    {P : Set X} {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f P)
    {x y : X} (hx : x ∈ P) (hy : y ∈ P) {e : ℝ} (hxy : dist x y ≤ e) :
    |f x - f y| ≤ (L : ℝ) * e := by
  simpa only [Real.dist_eq] using (hf.dist_le_mul x hx y hy).trans
    (mul_le_mul_of_nonneg_left hxy L.coe_nonneg)

/-- Convert coordinate errors to the Euclidean metric of E.2. The deliberately
loose dimension constant also covers the zero-row event. -/
theorem space_dist_le_of_coordinates {d : ℕ} {x y : ConditionalGaussian.Space d}
    {e : ℝ} (he : 0 ≤ e) (hxy : ∀ i, |x i - y i| ≤ e) :
    dist x y ≤ (d + 1 : ℝ) * e := by
  have hs : ‖x - y‖ ^ 2 ≤ (d : ℝ) * e ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d, e ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := hxy i
        have h0 := abs_nonneg (x i - y i)
        have hh : (x i - y i) ^ 2 ≤ e ^ 2 := by nlinarith [sq_abs (x i - y i)]
        simpa using hh
      _ = _ := by simp
  have hd : (d : ℝ) ≤ (d + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg (d : ℝ)]
  have hsq := hs.trans (mul_le_mul_of_nonneg_right hd (sq_nonneg e))
  rw [dist_eq_norm]
  have hpos : 0 ≤ (d + 1 : ℝ) * e := by positivity
  nlinarith [norm_nonneg (x - y)]

/-- A common coordinate error controls the full mean/variance/threshold triple. -/
theorem parameters_dist_le_of_coordinates {d r : ℕ}
    {x y : GaussianRegularity.Parameters d r} {e : ℝ} (he : 0 ≤ e)
    (hm : ∀ i, |x.1.1 i - y.1.1 i| ≤ e)
    (hv : ∀ i, |x.1.2 i - y.1.2 i| ≤ e)
    (hu : ∀ i, |x.2 i - y.2 i| ≤ e) :
    dist x y ≤ (d + r + 1 : ℝ) * e := by
  rw [Prod.dist_eq, Prod.dist_eq, max_le_iff, max_le_iff]
  have hd : (d + 1 : ℝ) * e ≤ (d + r + 1 : ℝ) * e := by nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) r]
  have hr : (r + 1 : ℝ) * e ≤ (d + r + 1 : ℝ) * e := by nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) r]
  exact ⟨⟨(space_dist_le_of_coordinates he hm).trans hd,
    (space_dist_le_of_coordinates he hv).trans hd⟩,
    (space_dist_le_of_coordinates he hu).trans hr⟩

/-- One common compact bound for every raw first and second moment. -/
theorem compact_raw_bounds {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) {P : Set (GaussianRegularity.Parameters d r)}
    (hP : IsCompact P) (hv : ∀ p ∈ P, GaussianRegularity.positiveVariance p) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ p ∈ P, ∀ t, |GaussianRegularity.firstMoment M t p| ≤ B) ∧
      (∀ p ∈ P, ∀ t t', |GaussianRegularity.secondMoment M t t' p| ≤ B) := by
  classical
  obtain ⟨L, _, hfirst, hsecond, _⟩ :=
    (GaussianRegularity.gaussian_regularity d r M hM P hP hv).lipschitz
  have hb₁ : ∀ t, ∃ B : ℝ, ∀ p ∈ P, |GaussianRegularity.firstMoment M t p| ≤ B :=
    fun t => by simpa only [Real.norm_eq_abs] using
      hP.exists_bound_of_continuousOn (hfirst t).continuousOn
  have hb₂ : ∀ t t', ∃ B : ℝ, ∀ p ∈ P,
      |GaussianRegularity.secondMoment M t t' p| ≤ B :=
    fun t t' => by simpa only [Real.norm_eq_abs] using
      hP.exists_bound_of_continuousOn (hsecond t t').continuousOn
  choose b₁ hb₁ using hb₁
  choose b₂ hb₂ using hb₂
  refine ⟨(∑ t, |b₁ t|) + ∑ t, ∑ t', |b₂ t t'|, by positivity, ?_, ?_⟩
  · intro p hp t
    calc
      _ ≤ b₁ t := hb₁ t p hp
      _ ≤ |b₁ t| := le_abs_self _
      _ ≤ ∑ t, |b₁ t| := Finset.single_le_sum (f := fun t => |b₁ t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ t)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · intro p hp t t'
    calc
      _ ≤ b₂ t t' := hb₂ t t' p hp
      _ ≤ |b₂ t t'| := le_abs_self _
      _ ≤ ∑ t', |b₂ t t'| := Finset.single_le_sum (f := fun t' => |b₂ t t'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ t')
      _ ≤ ∑ t, ∑ t', |b₂ t t'| := Finset.single_le_sum (f := fun t => ∑ t', |b₂ t t'|) (fun _ _ => by positivity) (Finset.mem_univ t)
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- A closed coordinate box in the Euclidean coordinates used by E.2. -/
def coordinateBox {d : ℕ} (lo hi : Fin d → ℝ) :
    Set (ConditionalGaussian.Space d) := {x | ∀ i, lo i ≤ x i ∧ x i ≤ hi i}

theorem coordinateBox_compact {d : ℕ} (lo hi : Fin d → ℝ) :
    IsCompact (coordinateBox lo hi) := by
  have h := (isCompact_univ_pi (fun i : Fin d => isCompact_Icc (a := lo i) (b := hi i))).image
    (PiLp.continuous_toLp (p := (2 : ENNReal)) (fun _ : Fin d => ℝ))
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨WithLp.ofLp x, ?_, WithLp.toLp_ofLp 2 x⟩
    intro i _
    exact hx i
  · rintro ⟨y, hy, rfl⟩
    intro i
    exact hy i (Set.mem_univ i)

/-- The parameter box used in the proof of E.3. Bounds are coordinatewise,
so membership does not introduce dimension-dependent norm estimates. -/
def parameterBox {d r : ℕ} (R T : ℝ) (lo hi : Fin d → ℝ) :
    Set (GaussianRegularity.Parameters d r) :=
  (coordinateBox (fun _ => -R) (fun _ => R) ×ˢ coordinateBox lo hi) ×ˢ
    coordinateBox (fun _ => -T) (fun _ => T)

theorem parameterBox_compact {d r : ℕ} (R T : ℝ) (lo hi : Fin d → ℝ) :
    IsCompact (parameterBox (r := r) R T lo hi) :=
  ((coordinateBox_compact _ _).prod (coordinateBox_compact _ _)).prod
    (coordinateBox_compact _ _)

theorem parameterBox_positive {d r : ℕ} {R T : ℝ} {lo hi : Fin d → ℝ}
    (hl : ∀ i, 0 < lo i) :
    ∀ p ∈ parameterBox (r := r) R T lo hi, GaussianRegularity.positiveVariance p := by
  intro p hp i
  exact (hl i).trans_le (hp.1.2 i).1

/-- E.2 supplies uniform positive probability and all moment regularity on
these concrete boxes, without any extra analytic assumption. -/
theorem parameterBox_regular {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) (R T : ℝ) (lo hi : Fin d → ℝ) (hl : ∀ i, 0 < lo i) :
    GaussianRegularity.RegularOn M (parameterBox R T lo hi) :=
  GaussianRegularity.gaussian_regularity d r M hM _ (parameterBox_compact R T lo hi)
    (parameterBox_positive hl)

/-- Combine A.2 at the actual Gaussian parameters with E.2 comparison to the
limiting parameters. -/
theorem raw_error_of_comparison {X : Type*} [PseudoMetricSpace X]
    {P : Set X} {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f P)
    {x y : X} (hx : x ∈ P) (hy : y ∈ P) {a δ ε : ℝ}
    (ha : |a - f x| ≤ δ) (hxy : dist x y ≤ ε) :
    |a - f y| ≤ δ + (L : ℝ) * ε := by
  calc
    _ ≤ |a - f x| + |f x - f y| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add ha (abs_sub_le_of_lipschitz hf hx hy hxy)

/-- Uniformly positive actual Gaussian masses survive a small A.2 error.
The error here does not include the potentially nonvanishing ξ parameter. -/
theorem denominator_lower_bound {a g c e : ℝ}
    (hg : c ≤ g) (he : |a - g| ≤ e) (hsmall : e ≤ c / 2) : c / 2 ≤ a := by
  have := (abs_le.mp he).1
  linarith

/-- Quantitative division, using independent lower bounds on both denominators. -/
theorem ratio_error {a b p q c B e : ℝ} (hc : 0 < c)
    (hp : c ≤ p) (hq : c ≤ q) (hb : |b| ≤ B)
    (hab : |a - b| ≤ e) (hpq : |p - q| ≤ e) :
    |a / p - b / q| ≤ (1 / c + B / c ^ 2) * e := by
  have hp0 : 0 < p := hc.trans_le hp
  have hq0 : 0 < q := hc.trans_le hq
  have he : 0 ≤ e := (abs_nonneg _).trans hab
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have hpc : c ^ 2 ≤ p * q := by nlinarith [mul_le_mul hp hq hc.le hp0.le]
  have hsplit : a / p - b / q = (a - b) / p + b * (q - p) / (p * q) := by
    field_simp
    ring
  rw [hsplit]
  calc
    _ ≤ |(a - b) / p| + |b * (q - p) / (p * q)| := abs_add_le _ _
    _ = |a - b| / p + |b| * |p - q| / (p * q) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hp0, abs_of_pos (mul_pos hp0 hq0), abs_sub_comm q p]
    _ ≤ e / c + B * e / c ^ 2 := add_le_add
      (div_le_div₀ he hab hc hp)
      (div_le_div₀ (mul_nonneg hB he)
        (mul_le_mul hb hpq (abs_nonneg _) hB) (sq_pos_of_pos hc) hpc)
    _ = _ := by ring

/-- Passing from first and second conditional moments to centered covariance.
A fixed upper bound E for the error absorbs the product of the first-moment
errors; no assumption that ξ tends to zero is needed. -/
theorem covariance_error {a a' b b' A B c d e E : ℝ}
    (hb : |b| ≤ B) (hb' : |b'| ≤ B)
    (ha : |a - b| ≤ e) (ha' : |a' - b'| ≤ e)
    (hc : |c - d| ≤ e) (he : e ≤ E) (hA : 1 + 2 * B + E ≤ A) :
    |(c - a * a') - (d - b * b')| ≤ A * e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans ha
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have ha'B : |a'| ≤ B + E := by
    calc
      _ ≤ |a' - b'| + |b'| := by simpa using abs_add_le (a' - b') b'
      _ ≤ e + B := add_le_add ha' hb'
      _ ≤ B + E := by linarith
  have hprod : |a * a' - b * b'| ≤ (2 * B + E) * e := by
    calc
      _ = |(a - b) * a' + b * (a' - b')| := by congr 1; ring
      _ ≤ |(a - b) * a'| + |b * (a' - b')| := abs_add_le _ _
      _ = |a - b| * |a'| + |b| * |a' - b'| := by rw [abs_mul, abs_mul]
      _ ≤ e * (B + E) + B * e := add_le_add
        (mul_le_mul ha ha'B (abs_nonneg _) he0)
        (mul_le_mul hb ha' (abs_nonneg _) hB)
      _ = _ := by ring
  calc
    _ = |(c - d) - (a * a' - b * b')| := by congr 1; ring
    _ ≤ |c - d| + |a * a' - b * b'| := abs_sub _ _
    _ ≤ e + (2 * B + E) * e := add_le_add hc hprod
    _ ≤ A * e := by nlinarith

end MajorityDynamics.Idealized.RowLimits
