import MajorityDynamics.Literature.LWFormal.Lemma71

set_option autoImplicit true

/-!
# The exact `(P, Y)` is a fixed point of `𝒞`, and lies in `Π`

Proposition 3.1 rewritten in the operator language of §5, on a set of sequences where every
sequence is graphical, has all degrees `≥ 2` and satisfies `P_{av} ≤ 2μ`.
-/

namespace LW

open Finset Real

variable {n : ℕ}

theorem Close.trans' {x y z a b : ℝ} (hxy : Close x y a) (hyz : Close y z b) (ha : 0 ≤ a) :
    Close x z (a * (1 + b) + b) := by
  have h := hyz.abs_le
  unfold Close at *
  calc |x - z| = |(x - y) + (y - z)| := by ring_nf
    _ ≤ |x - y| + |y - z| := abs_add_le _ _
    _ ≤ a * ((1 + b) * |z|) + b * |z| := add_le_add (hxy.trans (by gcongr)) hyz
    _ = (a * (1 + b) + b) * |z| := by ring

theorem P_nonneg (a v : Fin n) (d : Seq n) : 0 ≤ P a v d := by unfold P; positivity

theorem Y_nonneg (a v b : Fin n) (d : Seq n) : 0 ≤ Y a v b d := by unfold Y; positivity

theorem Nav_comm (a v : Fin n) (d : Seq n) : Nav a v d = Nav v a d := by
  simp only [Nav, Sym2.eq_swap]

theorem Y_comm (a v b : Fin n) (d : Seq n) : Y a v b d = Y b v a d := by
  simp only [Y, Navb, pair_comm]

/-- `∑_{v ≠ a} P_{av}(d) = d_a`. -/
theorem sum_P (d : Seq n) (hN : 0 < N d) (a : Fin n) :
    ∑ v ∈ univ.erase a, P a v d = d a := by
  have h := sum_Nav d a
  have hN' : (N d : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [P]
  rw [← sum_div, div_eq_iff hN']
  simp_rw [Nav_comm a]
  exact_mod_cast h

/-- `N_{av}(d) > 0` when `d - e_a - e_v` is graphical and `P_{av}(d - e_a - e_v) < 1`. -/
theorem Nav_pos {d : Seq n} {a v : Fin n} (hav : a ≠ v) (hN : 0 < N (d - e a - e v))
    (hP : P a v (d - e a - e v) < 1) : 0 < Nav a v d := by
  have h := lemma_2_2 hav d
  have hN' : (0 : ℝ) < N (d - e a - e v) := by exact_mod_cast hN
  unfold P at hP
  rw [div_lt_one hN'] at hP
  have : Nav a v (d - e a - e v) < N (d - e a - e v) := by exact_mod_cast hP
  omega

theorem mu_sub_e_le (hn : 2 ≤ n) (d : Seq n) (a : Fin n) : mu (d - e a) ≤ mu d := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  unfold mu dbar
  rw [M1_sub_e]; push_cast
  gcongr
  linarith

/-- Hypotheses on a set of sequences making the exact `(P,Y)` a fixed point of `𝒞`. -/
structure ExactOK (μ : ℝ) (D₀ : Set (Seq n)) : Prop where
  n2 : 2 ≤ n
  two_le : ∀ d ∈ D₀, ∀ a, 2 ≤ d a
  mu_le : ∀ d ∈ D₀, mu d ≤ μ
  N_pos : ∀ d ∈ D₀, IsEven d → 0 < N d
  P_le : ∀ d ∈ D₀, IsEven d → ∀ a v, P a v d ≤ 2 * mu d

namespace ExactOK

variable {μ : ℝ} {D₀ : Set (Seq n)} (h : ExactOK μ D₀) (hμ : μ ≤ 1 / 8)
include h hμ

omit hμ in
theorem mu_nonneg {d : Seq n} (hd : d ∈ D₀) : 0 ≤ mu d := by
  have h2 := h.two_le d hd
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := h.n2; omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast h.n2
  have : (0 : ℝ) ≤ M1 d := by
    unfold M1; push_cast
    exact sum_nonneg fun i _ => by exact_mod_cast (by linarith [h2 i] : (0 : ℤ) ≤ d i)
  unfold mu dbar
  positivity

theorem P_lt_one {d : Seq n} (hd : d ∈ D₀) (hev : IsEven d) (a v : Fin n) : P a v d < 1 := by
  have := h.P_le d hd hev a v
  have := h.mu_le d hd
  linarith

/-- `Y_{avb}(d) ≤ 3μ(d) P_{av}(d)` for `d ∈ Ω⁽²⁾`. -/
theorem Y_le {d : Seq n} (hd : d ∈ Omega D₀ 2) (hev : IsEven d) {a v b : Fin n} (hav : a ≠ v)
    (hab : a ≠ b) (_hvb : v ≠ b) : Y a v b d ≤ 3 * mu d * P a v d := by
  have hd' : d - e a - e v ∈ D₀ := Omega_subset _ _ (Q0_subset_Omega (s := 0) hd
    (sub_e_sub_e_mem_Q0 hev a v))
  have hev' : IsEven (d - e a - e v) := (isEven_sub_e_sub_e a v).2 hev
  rw [prop_3_1c d a v b hav hab (h.N_pos _ hd' hev')]
  have hμd := h.mu_le d hd.1
  have hμd0 := h.mu_nonneg hd.1
  have hμ' : mu (d - e a - e v) ≤ mu d :=
    (mu_sub_e_le h.n2 _ _).trans (mu_sub_e_le h.n2 _ _)
  have hPa := h.P_le _ hd' hev' a v
  have hPb := h.P_le _ hd' hev' b v
  have hPa0 := P_nonneg a v (d - e a - e v)
  have hY0 := Y_nonneg a v b (d - e a - e v)
  have hP0 := P_nonneg a v d
  have hden : 0 < 1 - P a v (d - e a - e v) := by linarith
  rw [div_le_iff₀ hden]
  have : P b v (d - e a - e v) - Y a v b (d - e a - e v) ≤ 2 * mu d := by linarith
  calc P a v d * (P b v (d - e a - e v) - Y a v b (d - e a - e v)) ≤ P a v d * (2 * mu d) :=
        mul_le_mul_of_nonneg_left this hP0
    _ ≤ 3 * mu d * P a v d * (1 - P a v (d - e a - e v)) := by
        nlinarith [mul_nonneg (mul_nonneg hμd0 hP0)
          (by linarith : 0 ≤ 1 - 3 * P a v (d - e a - e v))]

theorem inPi : InPi (3 * μ) (Omega D₀ 2) P Y where
  pa d hd hev a v _ := ⟨P_nonneg a v d, by
    have := h.P_le d hd.1 hev a v; have := h.mu_le d hd.1; have := h.mu_nonneg hd.1; linarith⟩
  pb d hd hev a b hab := by
    have hN := h.N_pos d hd.1 hev
    have hμd := h.mu_le d hd.1
    have hμd0 := h.mu_nonneg hd.1
    calc ∑ v ∈ (univ.erase a).erase b, Y a v b d
        ≤ ∑ v ∈ (univ.erase a).erase b, 3 * mu d * P a v d := by
          refine sum_le_sum fun v hv => ?_
          simp only [mem_erase, mem_univ, and_true] at hv
          exact h.Y_le hμ hd hev (Ne.symm hv.2) hab hv.1
      _ ≤ ∑ v ∈ univ.erase a, 3 * mu d * P a v d :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun v _ _ => by
            have := P_nonneg a v d; positivity
      _ = 3 * mu d * d a := by rw [← mul_sum, sum_P d hN]
      _ ≤ 3 * μ * d a := by
          have : (0 : ℝ) ≤ d a := by exact_mod_cast (h.two_le d hd.1 a).trans' (by norm_num)
          gcongr
  pc d hd hev a v b hav hab hvb := by
    refine ⟨Y_nonneg _ _ _ _, ?_⟩
    rw [Y_comm]
    have := h.Y_le hμ hd hev hvb.symm hab.symm hav.symm
    have hμd := h.mu_le d hd.1
    have := P_nonneg b v d
    nlinarith

theorem bad_lt_one {d : Seq n} (hd : d ∈ Omega D₀ 2) (hev : IsEven d) {a b : Fin n} (hab : a ≠ b) :
    bad P Y a b d < 1 := by
  have hμ0 : 0 ≤ μ := (h.mu_nonneg hd.1).trans (h.mu_le d hd.1)
  have := (bad_bounds (h.inPi hμ) (by positivity) hd hev hab (h.two_le d hd.1 a)).2
  linarith

omit h hμ in
theorem B_eq_bad {a b : Fin n} (hab : a ≠ b) (d : Seq n) : B a b d = bad P Y a b d := by
  simp [B, bad, hab]

/-- `ℛ(P,Y) = R` on odd sequences of `Ω⁽³⁾` (Proposition 3.1(b)). -/
theorem opR_eq {d : Seq n} (hd : d ∈ Omega D₀ 3) (hodd : ¬ IsEven d) (a b : Fin n) :
    opR P Y a b d = R a b d := by
  have hQ : ∀ c, d - e c ∈ Omega D₀ 2 := fun c =>
    mem_Omega_of_dist1 (s := 2) (t := 1) hd (by rw [dist1_sub_e]; norm_num)
  have hNc : ∀ c, 0 < N (d - e c) := fun c =>
    h.N_pos _ (hQ c).1 (isEven_sub_e_of_odd hodd c)
  by_cases hab : a = b
  · subst hab
    have hN : (N (d - e a) : ℝ) ≠ 0 := by exact_mod_cast (hNc a).ne'
    have hda : (d a : ℝ) ≠ 0 := by
      exact_mod_cast (show d a ≠ 0 by have := h.two_le d hd.1 a; omega)
    simp [opR, bad, R, hN, hda]
  rw [prop_3_1b d a b hab (hNc a) (hNc b), opR, B_eq_bad hab, B_eq_bad (Ne.symm hab)]
  rw [B_eq_bad (Ne.symm hab)]
  exact (h.bad_lt_one hμ (hQ a) (isEven_sub_e_of_odd hodd a) (Ne.symm hab)).ne

/-- `𝒫(P, ℛ(P,Y)) = P` on even sequences of `Ω⁽⁴⁾` (Proposition 3.1(a)). -/
theorem opP_eq {d : Seq n} (hd : d ∈ Omega D₀ 4) (hev : IsEven d) {a v : Fin n} (hav : a ≠ v) :
    opP P (opR P Y) a v d = P a v d := by
  have hd2 : d - e a - e v ∈ Omega D₀ 2 := Q0_subset_Omega hd (sub_e_sub_e_mem_Q0 hev a v)
  have hev2 : IsEven (d - e a - e v) := (isEven_sub_e_sub_e a v).2 hev
  have hdv : d - e v ∈ Omega D₀ 3 :=
    mem_Omega_of_dist1 (s := 3) (t := 1) hd (by rw [dist1_sub_e]; norm_num)
  have hNav : 0 < Nav a v d :=
    Nav_pos hav (h.N_pos _ hd2.1 hev2) (h.P_lt_one hμ hd2.1 hev2 a v)
  rw [prop_3_1a d a v hav hNav, opP]
  congr 2
  refine sum_congr rfl fun b _ => ?_
  rw [h.opR_eq hμ hdv (not_isEven_sub_e_of_even hev v)]

/-- `𝒞(P,Y) = (P,Y)` on even sequences of `Ω⁽⁶⁾`. -/
theorem opC_fixed {d : Seq n} (hd : d ∈ Omega D₀ 6) (hev : IsEven d) :
    (∀ a v, a ≠ v → (opC P Y).1 a v d = P a v d) ∧
    (∀ a v b, a ≠ v → a ≠ b → v ≠ b → (opC P Y).2 a v b d = Y a v b d) := by
  have hd4 : d ∈ Omega D₀ 4 := Omega_mono (by norm_num) hd
  refine ⟨fun a v hav => h.opP_eq hμ hd4 hev hav, fun a v b hav hab hvb => ?_⟩
  have hd2 : d - e a - e v ∈ Omega D₀ 4 := Q0_subset_Omega hd (sub_e_sub_e_mem_Q0 hev a v)
  have hev2 : IsEven (d - e a - e v) := (isEven_sub_e_sub_e a v).2 hev
  show opY (opP P (opR P Y)) Y a v b d = Y a v b d
  rw [opY, h.opP_eq hμ hd4 hev hav, h.opP_eq hμ hd2 hev2 hvb.symm, h.opP_eq hμ hd2 hev2 hav,
    ← prop_3_1c d a v b hav hab (h.N_pos _ hd2.1 hev2)]

end ExactOK

/-! ### `(P^gr, Y^gr) ∈ Π` -/

/-- The correction `E` in `π = μ(1+x)(1+z)(1+E)`. -/
noncomputable def piCorr (x z μ σ2 d : ℝ) (n : ℕ) : ℝ :=
  (-μ * x * z + (x + z) * σ2 / (d * n)) / (1 - μ) + (x + z) / ((n : ℝ) - 1)

theorem piF_eq_corr (x z μ σ2 d : ℝ) (n : ℕ) :
    piF x z μ σ2 d n = μ * (1 + x) * (1 + z) * (1 + piCorr x z μ σ2 d n) := by
  unfold piF piCorr; ring

/-- `|E| ≤ 1/100` under the smallness hypotheses. -/
theorem abs_piCorr_le {x z μ σ2 d η : ℝ} {n : ℕ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 8) (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 32) (hx : |x| ≤ 2 * η) (hz : |z| ≤ 2 * η) (hσ : 0 ≤ σ2 / (d * n))
    (hs : σ2 / (d * n) ≤ η ^ 2 * μ) (hn : 1 / ((n : ℝ) - 1) ≤ μ * η ^ 2) (hn2 : (2 : ℝ) ≤ n) :
    |piCorr x z μ σ2 d n| ≤ 1 / 100 := by
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hη2 : η ^ 2 ≤ 1 / 1024 := by nlinarith
  have hxz : |x + z| ≤ 4 * η := (abs_add_le _ _).trans (by linarith)
  have h1 : |μ * x * z| ≤ 4 * μ * η ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hμ0]
    calc μ * |x| * |z| ≤ μ * (2 * η) * (2 * η) := by gcongr
      _ = 4 * μ * η ^ 2 := by ring
  have h2 : |(x + z) * σ2 / (d * n)| ≤ 4 * η * (η ^ 2 * μ) := by
    rw [mul_div_assoc, abs_mul, abs_of_nonneg hσ]
    gcongr
  have hA : |-μ * x * z + (x + z) * σ2 / (d * n)| ≤ 4 * μ * η ^ 2 + 4 * η * (η ^ 2 * μ) := by
    rw [show -μ * x * z = -(μ * x * z) by ring]
    exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
  have h3 : |(x + z) / ((n : ℝ) - 1)| ≤ 4 * η * (μ * η ^ 2) := by
    rw [div_eq_mul_one_div, abs_mul, abs_of_pos (one_div_pos.2 hn1)]
    gcongr
  unfold piCorr
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_pos (by linarith : 0 < 1 - μ)]
  have : 4 * η * (η ^ 2 * μ) ≤ μ * η ^ 2 / 8 := by nlinarith
  have : 4 * η * (μ * η ^ 2) ≤ μ * η ^ 2 / 8 := by nlinarith
  have hμη : μ * η ^ 2 ≤ 1 / 8192 := by nlinarith
  have : |-μ * x * z + (x + z) * σ2 / (d * ↑n)| / (1 - μ) ≤ 8 / 7 * (5 * μ * η ^ 2) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  nlinarith

/-- `μ/4 ≤ π ≤ 2μ` under the smallness hypotheses. -/
theorem piF_bounds {x z μ σ2 d η : ℝ} {n : ℕ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 8) (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 32) (hx : |x| ≤ 2 * η) (hz : |z| ≤ 2 * η) (hσ : 0 ≤ σ2 / (d * n))
    (hs : σ2 / (d * n) ≤ η ^ 2 * μ) (hn : 1 / ((n : ℝ) - 1) ≤ μ * η ^ 2) (hn2 : (2 : ℝ) ≤ n) :
    μ / 4 ≤ piF x z μ σ2 d n ∧ piF x z μ σ2 d n ≤ 2 * μ := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  obtain ⟨hz1, hz2⟩ := abs_le.1 hz
  obtain ⟨hE1, hE2⟩ := abs_le.1 (abs_piCorr_le hμ0 hμ hη hη' hx hz hσ hs hn hn2)
  set E := piCorr x z μ σ2 d n
  have hxz1 : 87 / 100 ≤ (1 + x) * (1 + z) := by nlinarith
  have hxz2 : (1 + x) * (1 + z) ≤ 114 / 100 := by nlinarith
  have hP : piF x z μ σ2 d n = μ * ((1 + x) * (1 + z) * (1 + E)) := by
    rw [piF_eq_corr]; ring
  rw [hP]
  constructor
  · have : 87 / 100 * (99 / 100) ≤ (1 + x) * (1 + z) * (1 + E) :=
      mul_le_mul hxz1 (by linarith) (by norm_num) (by linarith)
    nlinarith
  · have : (1 + x) * (1 + z) * (1 + E) ≤ 114 / 100 * (101 / 100) :=
      mul_le_mul hxz2 (by linarith) (by linarith) (by norm_num)
    nlinarith

/-- Hypotheses on a set of sequences under which `(P^gr, Y^gr)` is controlled. -/
structure GrOK (α μ : ℝ) (D₀ : Set (Seq n)) : Prop where
  α₁ : 1 / 2 ≤ α
  α₂ : α < 3 / 5
  n2 : 2 ≤ n
  spread : ∀ d ∈ D₀, Spread α d
  dbar_ge : ∀ d ∈ D₀, (32768 : ℝ) ≤ dbar d
  mu_le : ∀ d ∈ D₀, mu d ≤ μ

namespace GrOK

variable {α μ : ℝ} {D₀ : Set (Seq n)} (h : GrOK α μ D₀) (hμ : μ ≤ 1 / 8)
include h

/-- The scale `η = 2 d̄^{α-1}` on `D₀`, with `η ≤ 1/32`. -/
theorem eta {d : Seq n} (hd : d ∈ D₀) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 32 ∧ (∀ i, |eps d i| ≤ η) ∧ 1 / dbar d ≤ η ^ 2 ∧
      sigma2 d / dbar d ^ 2 ≤ η ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := h.n2; omega)
  have hD := h.dbar_ge d hd
  obtain ⟨h0, h25, -, hε, hδ, ht, -⟩ :=
    spread_bounds h.α₁ h.α₂ (by linarith) (h.spread d hd) hn0
  refine ⟨_, h0, eta_le (by norm_num) h25 ?_, hε, hδ, ht⟩
  calc ((1 / 32 : ℝ) / 2) ^ (-(5 / 2 : ℝ)) = ((2 : ℝ) ^ (6 : ℕ)) ^ ((5 / 2 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]; norm_num
    _ = 32768 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ dbar d := hD

theorem basic {d : Seq n} (hd : d ∈ D₀) :
    0 < dbar d ∧ 0 < mu d ∧ mu d ≤ μ ∧ (2 : ℝ) ≤ n ∧ dbar d / n ≤ mu d ∧
      1 / ((n : ℝ) - 1) = mu d / dbar d := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.n2
  have hD := h.dbar_ge d hd
  have hdpos : 0 < dbar d := by linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  refine ⟨hdpos, by unfold mu; positivity, h.mu_le d hd, hn2, ?_, ?_⟩
  · unfold mu; gcongr; linarith
  · unfold mu; field_simp

include hμ

theorem Pgr_bounds {d : Seq n} (hd : d ∈ D₀) (a v : Fin n) :
    mu d / 4 ≤ Pgr a v d ∧ Pgr a v d ≤ 2 * mu d := by
  obtain ⟨η, hη0, hη1, hε, hδ, ht⟩ := h.eta hd
  obtain ⟨hdpos, hμ0, hμd, hn2, hdn, hn1⟩ := h.basic hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : sigma2 d / (dbar d * n) = sigma2 d / dbar d ^ 2 * (dbar d / n) := by
    field_simp
  have hσ0 : 0 ≤ sigma2 d := by unfold sigma2; positivity
  refine piF_bounds hμ0 (hμd.trans hμ) hη0.le hη1 ((hε a).trans (by linarith))
    ((hε v).trans (by linarith)) (by positivity) ?_ ?_ hn2
  · rw [hs]; exact mul_le_mul ht hdn (by positivity) (by positivity)
  · rw [hn1, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hδ hμ0.le

theorem abs_piCorr_le {d : Seq n} (hd : d ∈ D₀) (a v : Fin n) :
    |piCorr (eps d a) (eps d v) (mu d) (sigma2 d) (dbar d) n| ≤ 1 / 100 := by
  obtain ⟨η, hη0, hη1, hε, hδ, ht⟩ := h.eta hd
  obtain ⟨hdpos, hμ0, hμd, hn2, hdn, hn1⟩ := h.basic hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : sigma2 d / (dbar d * n) = sigma2 d / dbar d ^ 2 * (dbar d / n) := by
    field_simp
  have hσ0 : 0 ≤ sigma2 d := by unfold sigma2; positivity
  refine LW.abs_piCorr_le hμ0 (hμd.trans hμ) hη0.le hη1 ((hε a).trans (by linarith))
    ((hε v).trans (by linarith)) (by positivity) ?_ ?_ hn2
  · rw [hs]; exact mul_le_mul ht hdn (by positivity) (by positivity)
  · rw [hn1, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hδ hμ0.le

theorem Ygr_bounds {d : Seq n} (hd : d ∈ D₀) (a v b : Fin n) :
    mu d ^ 2 / 16 ≤ Ygr a v b d ∧ Ygr a v b d ≤ 8 * mu d ^ 2 := by
  obtain ⟨η, hη0, hη1, hε, hδ, ht⟩ := h.eta hd
  obtain ⟨hdpos, hμ0, hμd, hn2, hdn, hn1⟩ := h.basic hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1' : (0 : ℝ) < n - 1 := by linarith
  have hs : sigma2 d / (dbar d * n) = sigma2 d / dbar d ^ 2 * (dbar d / n) := by
    field_simp
  have hσ0 : 0 ≤ sigma2 d := by unfold sigma2; positivity
  have hs' : sigma2 d / (dbar d * n) ≤ η ^ 2 * mu d := by
    rw [hs]; exact mul_le_mul ht hdn (by positivity) (by positivity)
  have hn' : 1 / ((n : ℝ) - 1) ≤ mu d * η ^ 2 := by
    rw [hn1, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hδ hμ0.le
  have hμ8 : mu d ≤ 1 / 8 := hμd.trans hμ
  have h1 := piF_bounds hμ0 hμ8 hη0.le hη1 ((hε a).trans (by linarith))
    ((hε v).trans (by linarith)) (by positivity) hs' hn' hn2
  have hz : |eps d v - 1 / dbar d| ≤ 2 * η := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (one_div_pos.2 hdpos)]
    nlinarith [hε v]
  have h2 := piF_bounds hμ0 hμ8 hη0.le hη1 ((hε b).trans (by linarith)) hz (by positivity) hs'
    hn' hn2
  obtain ⟨ha1, ha2⟩ := abs_le.1 (hε a)
  obtain ⟨hb1, hb2⟩ := abs_le.1 (hε b)
  have hnum0 : 0 ≤ 1 + eps d a - mu d * (1 + eps d a + eps d b) := by nlinarith
  have hnum2 : 1 + eps d a - mu d * (1 + eps d a + eps d b) ≤ 2 := by nlinarith
  have hden : 0 < ((n : ℝ) - 1) * (1 - mu d) := by
    apply mul_pos hn1'; linarith
  have hT0 : 0 ≤ (1 + eps d a - mu d * (1 + eps d a + eps d b)) / (((n : ℝ) - 1) * (1 - mu d)) :=
    div_nonneg hnum0 hden.le
  have hT1 : (1 + eps d a - mu d * (1 + eps d a + eps d b)) / (((n : ℝ) - 1) * (1 - mu d)) ≤ 1 := by
    rw [div_le_one hden]
    have : 1 / ((n : ℝ) - 1) ≤ 1 / 8192 := by nlinarith
    have : (8192 : ℝ) ≤ n - 1 := by
      rw [div_le_div_iff₀ hn1' (by norm_num)] at this; linarith
    nlinarith
  unfold Ygr
  constructor
  · calc mu d ^ 2 / 16 = mu d / 4 * (mu d / 4) * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul h1.1 h2.1 (by positivity) (by linarith)) (by linarith)
          (by norm_num) (by nlinarith)
  · calc piF (eps d a) (eps d v) (mu d) (sigma2 d) (dbar d) n *
          piF (eps d b) (eps d v - 1 / dbar d) (mu d) (sigma2 d) (dbar d) n *
          (1 + (1 + eps d a - mu d * (1 + eps d a + eps d b)) / (((n : ℝ) - 1) * (1 - mu d)))
        ≤ 2 * mu d * (2 * mu d) * 2 := by gcongr <;> linarith
      _ = 8 * mu d ^ 2 := by ring

theorem Rgr_nonneg {d : Seq n} (hd : d ∈ D₀) (a b : Fin n) : 0 ≤ Rgr a b d := by
  obtain ⟨η, hη0, hη1, hε, hδ, ht⟩ := h.eta hd
  obtain ⟨hdpos, hμ0, hμd, hn2, hdn, hn1⟩ := h.basic hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hσ0 : 0 ≤ sigma2 d := by unfold sigma2; positivity
  have hs : sigma2 d / (dbar d * n) ≤ η ^ 2 * mu d := by
    rw [show sigma2 d / (dbar d * n) = sigma2 d / dbar d ^ 2 * (dbar d / n) by field_simp]
    exact mul_le_mul ht hdn (by positivity) (by positivity)
  have hμ8 : mu d ≤ 1 / 8 := hμd.trans hμ
  obtain ⟨ha1, ha2⟩ := abs_le.1 (hε a)
  obtain ⟨hb1, hb2⟩ := abs_le.1 (hε b)
  have hη2 : η ^ 2 ≤ 1 / 1024 := by nlinarith
  unfold Rgr rhoF
  have hn0' : (0 : ℝ) < 1 / n := by positivity
  have hma : mu d * (1 + eps d a) ≤ 1 / 4 :=
    (mul_le_mul hμ8 (by linarith : 1 + eps d a ≤ 2) (by linarith) (by norm_num)).trans (by norm_num)
  have hmb : mu d * (1 + eps d b) ≤ 1 / 4 :=
    (mul_le_mul hμ8 (by linarith : 1 + eps d b ≤ 2) (by linarith) (by norm_num)).trans (by norm_num)
  refine mul_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith))
    (div_nonneg (by linarith) (by linarith))) ?_
  have hT : |(eps d a - eps d b) * sigma2 d / ((1 - mu d) ^ 2 * dbar d * n)| ≤ 1 / 2 := by
    rw [show (eps d a - eps d b) * sigma2 d / ((1 - mu d) ^ 2 * dbar d * n) =
      (eps d a - eps d b) * (sigma2 d / (dbar d * n)) / (1 - mu d) ^ 2 by field_simp]
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ sigma2 d / (dbar d * n)),
      abs_of_pos (by nlinarith : 0 < (1 - mu d) ^ 2), div_le_iff₀ (by nlinarith)]
    have : |eps d a - eps d b| ≤ 2 * η := (abs_sub _ _).trans (by linarith [hε a, hε b])
    have : |eps d a - eps d b| * (sigma2 d / (dbar d * n)) ≤ 2 * η * (η ^ 2 * mu d) := by
      gcongr
    have : η * (η ^ 2 * mu d) ≤ 1 / 32 * (1 / 1024 * (1 / 8)) :=
      mul_le_mul hη1 (mul_le_mul hη2 hμ8 hμ0.le (by norm_num)) (by positivity) (by norm_num)
    have : (7 / 8 : ℝ) ^ 2 ≤ (1 - mu d) ^ 2 := by gcongr; linarith
    nlinarith
  linarith [(abs_le.1 hT).1]

theorem inPi {μp : ℝ} (hμp : 64 * μ ≤ μp) : InPi μp D₀ Pgr Ygr where
  pa d hd _ a v _ := by
    obtain ⟨h1, h2⟩ := h.Pgr_bounds hμ hd a v
    have := (h.basic hd).2.1
    have := h.mu_le d hd
    exact ⟨by linarith, by linarith⟩
  pb d hd _ a b _ := by
    obtain ⟨η, hη0, hη1, hε, -, -⟩ := h.eta hd
    obtain ⟨hdpos, hμ0, hμd, hn2, hdn, hn1⟩ := h.basic hd
    have hda : (d a : ℝ) = dbar d * (1 + eps d a) := by unfold eps; field_simp; ring
    have hda' : dbar d * (31 / 32) ≤ d a := by
      rw [hda]; have := (abs_le.1 (hε a)).1; nlinarith
    have hcard : (((univ.erase a).erase b).card : ℝ) ≤ n := by
      exact_mod_cast (card_le_univ _).trans (by simp)
    have hμn : mu d * n ≤ 2 * dbar d := by
      unfold mu
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ∑ v ∈ (univ.erase a).erase b, Ygr a v b d
        ≤ ∑ _v ∈ (univ.erase a).erase b, 8 * mu d ^ 2 :=
          sum_le_sum fun v _ => (h.Ygr_bounds hμ hd a v b).2
      _ = ((univ.erase a).erase b).card * (8 * mu d ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ n * (8 * mu d ^ 2) := by gcongr
      _ = 8 * mu d * (mu d * n) := by ring
      _ ≤ 8 * mu d * (2 * dbar d) := by gcongr
      _ ≤ μp * d a := by nlinarith
  pc d hd _ a v b _ _ _ := by
    obtain ⟨h1, h2⟩ := h.Ygr_bounds hμ hd a v b
    obtain ⟨h3, -⟩ := h.Pgr_bounds hμ hd b v
    have := (h.basic hd).2.1
    have := h.mu_le d hd
    exact ⟨le_trans (by positivity) h1, by nlinarith⟩

/-- `(p̂, Y^gr) ∈ Π` for any `p̂ = P^gr(1 ± 1/2)`. -/
theorem inPi_of_close {μp : ℝ} (hμp : 64 * μ ≤ μp) {D₁ : Set (Seq n)} (hD₁ : D₁ ⊆ D₀)
    (p : PFun n) (hp : ∀ d ∈ D₁, IsEven d → ∀ a v, a ≠ v → Close (p a v d) (Pgr a v d) (1 / 2)) :
    InPi μp D₁ p Ygr where
  pa d hd hev a v hav := by
    obtain ⟨h1, h2⟩ := h.Pgr_bounds hμ (hD₁ hd) a v
    have := (h.basic (hD₁ hd)).2.1
    have := h.mu_le d (hD₁ hd)
    have h3 := (hp d hd hev a v hav).le_of_nonneg (by linarith)
    have h4 := (hp d hd hev a v hav).ge_of_nonneg (by linarith)
    exact ⟨by linarith, by linarith⟩
  pb d hd hev a b hab := (h.inPi hμ hμp).pb d (hD₁ hd) hev a b hab
  pc d hd hev a v b _ _ hvb := by
    obtain ⟨h1, h2⟩ := h.Ygr_bounds hμ (hD₁ hd) a v b
    obtain ⟨h3, -⟩ := h.Pgr_bounds hμ (hD₁ hd) b v
    have := (h.basic (hD₁ hd)).2.1
    have := h.mu_le d (hD₁ hd)
    have h4 := (hp d hd hev b v hvb.symm).ge_of_nonneg (by linarith)
    exact ⟨le_trans (by positivity) h1, by nlinarith⟩

end GrOK

end LW
