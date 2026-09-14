import MajorityDynamics.Literature.LWFormal.Assembly
import MajorityDynamics.Literature.LWFormal.Eq74
import MajorityDynamics.Literature.LWFormal.Statements

set_option autoImplicit true

/-!
# Theorem 1.4: final assembly via Lemma 2.1
-/

namespace LW

open Finset Real Filter

variable {n : ℕ}

theorem Range.mono {ω : ℕ → ℝ} {μ₀ μ₁ : ℝ} {n m : ℕ} (h : Range ω μ₀ n m) (hμ : μ₀ ≤ μ₁) :
    Range ω μ₁ n m :=
  ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg n))⟩

theorem expFactor_le (d : Fin n → ℕ) : expFactor d ≤ exp (1 / 4) := by
  unfold expFactor
  have : 0 ≤ gamma2 d ^ 2 / (4 * density d ^ 2 * (1 - density d) ^ 2) := by positivity
  exact exp_le_exp.2 (by linarith)

theorem toN_toZ (d : Fin n → ℕ) : toN (toZ d) = d := by
  funext i; simp [toN, toZ]

theorem toZ_injective : Function.Injective (toZ (n := n)) := fun d d' h =>
  funext fun i => by have := congrFun h i; simpa [toZ] using this

theorem probBinom_pos {m : ℕ} {d : Fin n → ℕ} (hd : d ∈ OmegaNM n m) (hm : 2 * m ≤ n * (n - 1)) :
    0 < probBinom n m d := by
  obtain ⟨hlt, -⟩ := mem_OmegaNM.1 hd
  unfold probBinom
  refine mul_pos (inv_pos.2 (by exact_mod_cast Nat.choose_pos hm)) (prod_pos fun i _ => ?_)
  exact_mod_cast Nat.choose_pos (by have := hlt i; omega)

theorem Close.pos_of_pos {x z ε : ℝ} (h : Close x z ε) (hx : 0 < x) (hε : ε < 1) : 0 < z := by
  by_contra hz
  push Not at hz
  rw [Close, abs_of_nonpos hz] at h
  have := (_root_.abs_le.1 h).2
  nlinarith

/-- Two quantities relatively close to a common positive `z` have close logarithms. -/
theorem abs_log_sub_log_le {x y z ε₁ ε₂ : ℝ} (hx : Close x z ε₁) (hy : Close y z ε₂) (hz : 0 < z)
    (h1 : 0 ≤ ε₁) (h1' : ε₁ ≤ 1 / 2) (h2 : 0 ≤ ε₂) (h2' : ε₂ ≤ 1 / 2) :
    |log x - log y| ≤ 2 * ε₁ + 2 * ε₂ := by
  obtain ⟨hx0, -, hlx⟩ := hx.logClose hz h1 h1'
  obtain ⟨hy0, -, hly⟩ := hy.logClose hz h2 h2'
  rw [log_div hx0.ne' hz.ne'] at hlx
  rw [log_div hy0.ne' hz.ne'] at hly
  calc |log x - log y| = |(log x - log z) - (log y - log z)| := by ring_nf
    _ ≤ |log x - log z| + |log y - log z| := abs_sub _ _
    _ ≤ _ := by linarith

/-- On `Q₁¹`, `err71 = μ d̄^{4α-4} ≤ 2 D^{4α-3}/n` with `D = 2m/n`. -/
theorem err71_Q1D {α : ℝ} (hα : α ≤ 3 / 4) {m : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ (2 * m / n : ℝ))
    {d : Seq n} (hd : d ∈ Q1D α n m) :
    err71 α d ≤ 2 * (2 * m / n : ℝ) ^ (4 * α - 3) / n := by
  obtain ⟨a, -, hM, -⟩ := hd
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set D : ℝ := 2 * m / n with hDdef
  have hM' : M1 d = 2 * m + 1 := by have := M1_sub_e d a; omega
  have hdbar : dbar d = D + 1 / n := by rw [dbar, hM', hDdef]; push_cast; ring
  have hD0 : 0 < D := by linarith
  have hdb : 0 < dbar d := by rw [hdbar]; positivity
  have e : err71 α d = dbar d ^ (4 * α - 3) / (n - 1) := by
    unfold err71 mu
    rw [show 4 * α - 3 = (4 * α - 4) + 1 by ring, rpow_add_one hdb.ne']; ring
  have h1 : dbar d ^ (4 * α - 3) ≤ D ^ (4 * α - 3) :=
    rpow_le_rpow_of_nonpos hD0 (by rw [hdbar]; linarith [show (0 : ℝ) < 1 / n by positivity])
      (by linarith)
  have h2 : 0 ≤ D ^ (4 * α - 3) := rpow_nonneg hD0.le _
  rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ n)]

theorem tendsto_xi : Tendsto xi atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := 1 / 2) (2 : ℝ) (by norm_num))
    |>.tendsto_div_nhds_zero |>.comp tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp only [Function.comp, xi, rpow_two, sqrt_eq_rpow]

theorem toZ_toN {u : Seq n} (h : ∀ i, 0 ≤ u i) : toZ (toN u) = u := by
  funext i; simp only [toZ, toN]; exact Int.toNat_of_nonneg (h i)

theorem probGnm_toN {α : ℝ} {m : ℕ} {u : Seq n} (hu : u ∈ Dset α n m) :
    probGnm n m (toN u) = N u / edgeGraphCount n m := by
  have hsum : ∑ i, toN u i = 2 * m := by
    have h := hu.2.1
    simp only [M1] at h
    have h' : ∑ i, ((toN u i : ℕ) : ℤ) = 2 * m := by
      rw [← h]; exact sum_congr rfl fun i _ => Int.toNat_of_nonneg (hu.1 i)
    exact_mod_cast h'
  rw [probGnm_eq n m _ hsum, show (fun i => ((toN u i : ℕ) : ℤ)) = u from toZ_toN hu.1]

theorem edgeGraphCount_pos {m : ℕ} (hm : 2 * m ≤ n * (n - 1)) : 0 < edgeGraphCount n m := by
  rw [← card_Gnm, Gnm, card_powersetCard]
  exact Nat.choose_pos (by have := two_mul_card_allEdges n; omega)

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.4** (Liebenau–Wormald). -/
theorem theorem_1_4 : Theorem14 := by
  unfold Theorem14
  obtain ⟨μ₁, hμ₁, h75⟩ := eq_7_5
  obtain ⟨μ₂, hμ₂, hHR⟩ := H_ratio
  obtain ⟨μ₃, hμ₃, hEH⟩ := expect_Htilde
  obtain ⟨μ₄, hμ₄, hPG⟩ := prob_Dset_G
  obtain ⟨μ₅, hμ₅, hPB⟩ := prob_Dset_B
  obtain ⟨μ₆, hμ₆, hDG⟩ := Dset_graphical
  refine ⟨min (min μ₁ μ₂) (min (min μ₃ μ₄) (min μ₅ (min μ₆ (1 / 8)))), by positivity,
    fun α hα₁ hα₂ ω hω => ?_⟩
  obtain ⟨C₁, N₁, h₁⟩ := h75 α hα₁ hα₂ ω hω
  obtain ⟨C₂, N₂, h₂⟩ := hHR α hα₁ hα₂ ω hω
  obtain ⟨C₃, N₃, h₃⟩ := hEH ω hω
  obtain ⟨N₄, h₄⟩ := hPG α hα₁ hα₂ ω hω
  obtain ⟨N₅, h₅⟩ := hPB α hα₁ hα₂ ω hω
  obtain ⟨N₆, h₆⟩ := hDG α hα₁ hα₂ ω hω
  set K := 4 * |C₁| + 2 * |C₂| with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * (K + 12 + 2 * |C₃|), ?_⟩
  set β : ℝ := 1 / (3 - 5 * α) with hβ
  have hL : ∀ᶠ n : ℕ in atTop, max 2 (4 * K) ≤ log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hNr : ∀ᶠ n : ℕ in atTop, 4 * |C₁| + 2 * |C₂| + 6 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hωβ : ∀ᶠ n : ℕ in atTop, β ≤ ω n := hω.eventually (eventually_ge_atTop _)
  have hξ : ∀ᶠ n : ℕ in atTop, xi n < 1 / (4 * (|C₃| + 1)) :=
    tendsto_xi.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_ge_atTop 8).and (hL.and (hNr.and (hωβ.and
    (hξ.and ((eventually_ge_atTop N₁).and ((eventually_ge_atTop N₂).and
    ((eventually_ge_atTop N₃).and ((eventually_ge_atTop N₄).and
    ((eventually_ge_atTop N₅).and (eventually_ge_atTop N₆)))))))))))
  refine ⟨N, fun n hn m hR1 hR2 d hd => ?_⟩
  obtain ⟨hn8, hlog, hnC, hωn, hxi, hN₁, hN₂, hN₃, hN₄, hN₅, hN₆⟩ := hN n hn
  have hR : Range ω _ n m := ⟨hR1, hR2⟩
  have hR₁ := hR.mono ((min_le_left _ _).trans (min_le_left _ _))
  have hR₂ := hR.mono ((min_le_left _ _).trans (min_le_right _ _))
  have hR₃ := hR.mono ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hR₄ := hR.mono ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hR₅ := hR.mono ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hR₆ := hR.mono ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hR₈ : Range ω (1 / 8) n m := hR.mono ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  -- basic bounds on `n` and `D = 2m/n`
  set D : ℝ := 2 * m / n with hD
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hn2 : (64 : ℝ) ≤ n ^ 2 := by
    rw [sq]; exact le_trans (by norm_num) (mul_le_mul hn' hn' (by norm_num) (by linarith))
  have hnn2 : (n : ℝ) ≤ n ^ 2 := le_self_pow₀ (by linarith) two_ne_zero
  have hl2 : 2 ≤ log n := (le_max_left _ _).trans hlog
  have hlK : 4 * K ≤ log n := (le_max_right _ _).trans hlog
  have h35 : 0 < 3 - 5 * α := by linarith
  have hβ0 : 0 < β := by rw [hβ]; exact div_pos one_pos h35
  have hD1 : 1 ≤ D := (one_le_rpow (by linarith) (by linarith)).trans hR1
  have hDβ : log n ^ β ≤ D := (rpow_le_rpow_of_exponent_le (by linarith) hωn).trans hR1
  have hDn : 8 * D ≤ n := by have := hR₈.2; linarith
  have hD0 : 0 < D := by linarith
  have hmn : 2 * m ≤ n * (n - 1) := by
    refine two_mul_le_of_eight_mul_le (by omega) ?_
    have : (8 * m : ℝ) ≤ n * n := by
      have : (2 * m : ℝ) = D * n := by rw [hD]; field_simp
      nlinarith
    exact_mod_cast this
  have hD53 : D ^ (5 * α - 3) ≤ (log n)⁻¹ := by
    calc D ^ (5 * α - 3) ≤ (log n ^ β) ^ (5 * α - 3) :=
          rpow_le_rpow_of_nonpos (rpow_pos_of_pos (by linarith) _) hDβ (by linarith)
      _ = log n ^ (β * (5 * α - 3)) := (rpow_mul (by linarith) _ _).symm
      _ = (log n)⁻¹ := by
          rw [show β * (5 * α - 3) = -1 by rw [hβ]; field_simp; ring, rpow_neg_one]
  have hKD : K * D ^ (5 * α - 3) ≤ 1 / 4 := by
    calc K * D ^ (5 * α - 3) ≤ K * (log n)⁻¹ := mul_le_mul_of_nonneg_left hD53 hK0
      _ ≤ 1 / 4 := by rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith
  have hDα : D ^ α * D ^ (4 * α - 3) = D ^ (5 * α - 3) := by
    rw [← rpow_add hD0]; congr 1; ring
  have hDαD : D ^ α ≤ D := by
    calc D ^ α ≤ D ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hD1 (by linarith)
      _ = D := rpow_one D
  have hDα' : D ^ α ≤ n * D ^ (5 * α - 3) := by
    calc D ^ α = D ^ (5 * α - 3) * D ^ (3 - 4 * α) := by rw [← rpow_add hD0]; congr 1; ring
      _ ≤ D ^ (5 * α - 3) * n := by
          refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg hD0.le _)
          calc D ^ (3 - 4 * α) ≤ D ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hD1 (by linarith)
            _ = D := rpow_one D
            _ ≤ n := by linarith
      _ = _ := mul_comm _ _
  have hD43 : D ^ (4 * α - 3) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hD1 (by linarith)
  have hxi0 : 0 ≤ xi n := by unfold xi; positivity
  have hxi1 : 1 / (n : ℝ) ^ 2 ≤ xi n := by
    unfold xi
    have hs : √(n : ℝ) ≤ n := sqrt_le_self_iff.2 (Or.inr (by linarith))
    have hs' : √(n : ℝ) ≤ (n : ℝ) ^ 2 := hs.trans (by nlinarith)
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc √(n : ℝ) ≤ 1 * (n : ℝ) ^ 2 := by linarith
      _ ≤ log n ^ 2 * n ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  -- membership of `d`
  obtain ⟨hsum, hdev⟩ := hd
  have hdlt : ∀ i, d i < n := fun i => by
    have h := (abs_le.1 (hdev i)).2
    have : (d i : ℝ) < n := by linarith
    exact_mod_cast this
  have hdΩ : d ∈ OmegaNM n m := mem_OmegaNM.2 ⟨hdlt, hsum⟩
  have hdD : toZ d ∈ Dset α n m :=
    ⟨fun i => Int.natCast_nonneg _, by simp only [M1, toZ]; exact_mod_cast hsum,
      fun i => by simpa [toZ] using hdev i⟩
  have hdW : toZ d ∈ Wset α n m :=
    mem_Wset.2 ⟨hdD, fun i => by simp only [toZ]; exact_mod_cast hdlt i⟩
  -- the normalising constant `Z = ∑_Ω H`
  set Z := ∑ d ∈ OmegaNM n m, probBinom n m d * expFactor d with hZ
  have hZ1 : |Z - 1| ≤ |C₃| * xi n :=
    (h₃ n hN₃ m hR₃).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hxi0)
  have hxi' : |C₃| * xi n ≤ 1 / 4 := by
    calc |C₃| * xi n ≤ (|C₃| + 1) * xi n := by gcongr; linarith
      _ ≤ (|C₃| + 1) * (1 / (4 * (|C₃| + 1))) := by gcongr
      _ = 1 / 4 := by field_simp
  have hZpos : 0 < Z := by linarith [(abs_le.1 hZ1).1]
  have hlogZ : |log Z| ≤ 2 * (|C₃| * xi n) := by
    have hc : Close Z 1 (|C₃| * xi n) := by rw [Close, abs_one, mul_one]; exact hZ1
    have := (hc.logClose one_pos (by positivity) (by linarith)).2.2
    rwa [div_one] at this
  -- Lemma 2.1 on `Ω' = toZ '' Ω`, `W`, `P = P_{𝒟(𝒢)}`, `P' = H / Z`
  have hHZ : ∀ d : Fin n → ℕ, H n m (toZ d) = probBinom n m d * expFactor d := fun d => by
    simp only [H, toN_toZ]
  have hHnn : ∀ u : Seq n, 0 ≤ H n m u := fun u => by unfold H probBinom expFactor; positivity
  have hinj : ∀ x ∈ OmegaNM n m, ∀ y ∈ OmegaNM n m, toZ x = toZ y → x = y :=
    fun x _ y _ h => toZ_injective h
  have hinjD : ∀ x ∈ DsetN α n m, ∀ y ∈ DsetN α n m, toZ x = toZ y → x = y :=
    fun x _ y _ h => toZ_injective h
  have hsub : DsetN α n m ⊆ OmegaNM n m := fun d hd => (mem_DsetN.1 hd).1
  have hE : (0 : ℝ) < edgeGraphCount n m := by exact_mod_cast edgeGraphCount_pos hmn
  have hpB : ∀ x ∈ OmegaNM n m, 0 ≤ probBinom n m x := fun x _ => by unfold probBinom; positivity
  have hP1 : ∑ x ∈ (OmegaNM n m).image toZ, probGnm n m (toN x) = 1 := by
    rw [sum_image hinj]; simp only [toN_toZ]; exact sum_probGnm n m hmn
  have hP'1 : ∑ x ∈ (OmegaNM n m).image toZ, H n m x / Z = 1 := by
    rw [← sum_div, sum_image hinj]; simp only [hHZ]; exact div_self hZpos.ne'
  have hpos : ∀ v ∈ Wset α n m, 0 < probGnm n m (toN v) ∧ 0 < H n m v / Z := by
    intro v hv
    obtain ⟨hvD, -⟩ := mem_Wset.1 hv
    obtain ⟨d', hd', rfl⟩ := mem_image.1 hv
    obtain ⟨hd'Ω, -⟩ := mem_DsetN.1 hd'
    refine ⟨?_, by rw [hHZ]; exact div_pos (mul_pos (probBinom_pos hd'Ω hmn) (exp_pos _)) hZpos⟩
    rw [probGnm_toN hvD]
    exact div_pos (by exact_mod_cast h₆ n hN₆ m hR₆ _ hvD) hE
  have hε₀ : 6 / (n : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hW : 1 - 6 / (n : ℝ) ^ 2 ≤ ∑ v ∈ Wset α n m, probGnm n m (toN v) := by
    rw [Wset, sum_image hinjD]; simp only [toN_toZ]
    have := h₄ n hN₄ m hR₄
    have : 1 / (n : ℝ) ^ 2 ≤ 6 / n ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hW' : 1 - 6 / (n : ℝ) ^ 2 ≤ ∑ v ∈ Wset α n m, H n m v / Z := by
    rw [← sum_div, Wset, sum_image hinjD, le_div_iff₀ hZpos]; simp only [hHZ]
    have hsd := sum_sdiff (f := fun d => probBinom n m d * expFactor d) hsub
    have hsd' := sum_sdiff (f := probBinom n m) hsub
    rw [sum_probBinom n m hmn] at hsd'
    have hgood := h₅ n hN₅ m hR₅
    have hbad : ∑ x ∈ OmegaNM n m \ DsetN α n m, probBinom n m x * expFactor x ≤ 3 / n ^ 2 := by
      calc ∑ x ∈ OmegaNM n m \ DsetN α n m, probBinom n m x * expFactor x
          ≤ ∑ x ∈ OmegaNM n m \ DsetN α n m, probBinom n m x * exp (1 / 4) :=
            sum_le_sum fun x hx =>
              mul_le_mul_of_nonneg_left (expFactor_le x) (hpB x (sdiff_subset hx))
        _ = (∑ x ∈ OmegaNM n m \ DsetN α n m, probBinom n m x) * exp (1 / 4) :=
            (sum_mul _ _ _).symm
        _ ≤ 1 / n ^ 2 * 3 := by
            refine mul_le_mul (by linarith) ?_ (exp_pos _).le (by positivity)
            have := exp_le_exp.2 (show (1 / 4 : ℝ) ≤ 1 by norm_num)
            linarith [exp_one_lt_d9]
        _ = 3 / n ^ 2 := by ring
    have : 3 / (n : ℝ) ^ 2 ≤ 6 * Z / n ^ 2 :=
      div_le_div_of_nonneg_right (by linarith [(abs_le.1 hZ1).1]) (by positivity)
    have : (1 - 6 / (n : ℝ) ^ 2) * Z = Z - 6 * Z / n ^ 2 := by ring
    linarith
  -- edge estimate: (7.5) vs (6.10)
  set δ : ℝ := 2 * (|C₁| * (2 * D ^ (4 * α - 3) / n)) + 2 * (|C₂| / n ^ 2) with hδ
  have hedge : ∀ u ∈ Wset α n m, ∀ v ∈ Wset α n m, Adj u v →
      |log (H n m u / Z / (H n m v / Z)) - log (probGnm n m (toN u) / probGnm n m (toN v))| ≤ δ := by
    rintro u hu v hv ⟨d₀, a, b, -, rfl, rfl⟩
    obtain ⟨huD, -⟩ := mem_Wset.1 hu
    obtain ⟨hvD, -⟩ := mem_Wset.1 hv
    have hQ : d₀ ∈ Q1D α n m := ⟨a, huD⟩
    have hNa : (0 : ℝ) < LW.N (d₀ - e a) := by exact_mod_cast h₆ n hN₆ m hR₆ _ huD
    have hNb : (0 : ℝ) < LW.N (d₀ - e b) := by exact_mod_cast h₆ n hN₆ m hR₆ _ hvD
    have hRpos : 0 < R a b d₀ := div_pos hNa hNb
    have herr0 : 0 ≤ err71 α d₀ := by
      have hdbar0 : 0 < dbar d₀ := by
        have : M1 d₀ = 2 * m + 1 := by have := M1_sub_e d₀ a; have := huD.2.1; omega
        rw [dbar, this]; positivity
      exact mul_nonneg (div_nonneg hdbar0.le (by linarith)) (rpow_nonneg hdbar0.le _)
    have herr : err71 α d₀ ≤ 2 * D ^ (4 * α - 3) / n := err71_Q1D (by linarith) (by omega) hD1 hQ
    have hε₁ : |C₁| * err71 α d₀ ≤ 1 / 2 := by
      calc |C₁| * err71 α d₀ ≤ |C₁| * (2 * 1 / n) := by
            refine mul_le_mul_of_nonneg_left (herr.trans ?_) (abs_nonneg _)
            gcongr
        _ ≤ 1 / 2 := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]; linarith [abs_nonneg C₂]
    have hε₂ : |C₂| / (n : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith [abs_nonneg C₁]
    have hx : Close (R a b d₀) (Rgr a b d₀) (|C₁| * err71 α d₀) :=
      (h₁ n hN₁ m hR₁ d₀ hQ a b).mono (mul_le_mul_of_nonneg_right (le_abs_self _) herr0)
    have hy : Close (H n m (d₀ - e a) / H n m (d₀ - e b)) (Rgr a b d₀) (|C₂| / n ^ 2) :=
      (h₂ n hN₂ m hR₂ d₀ hQ a b).mono (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))
    have hz : 0 < Rgr a b d₀ := hx.pos_of_pos hRpos (by linarith)
    rw [div_div_div_cancel_right₀ hZpos.ne', probGnm_toN huD, probGnm_toN hvD,
      div_div_div_cancel_right₀ hE.ne']
    have := abs_log_sub_log_le hy hx hz (by positivity) hε₂ (by positivity) hε₁
    refine this.trans ?_
    rw [hδ]
    have := mul_le_mul_of_nonneg_left herr (abs_nonneg C₁)
    linarith
  -- diameter
  have hdiam : ∀ u ∈ Wset α n m, ∀ v ∈ Wset α n m,
      HasWalk Adj (Wset α n m) ⌊(n : ℝ) * D ^ α⌋₊ u v := fun u hu v hv => by
    obtain ⟨r, hr, hw⟩ := diam_Dset α (by linarith) n m u v hu hv
    exact hw.mono (Nat.le_floor hr)
  have key := lemma_2_1 ((OmegaNM n m).image toZ) (Wset α n m)
    (image_subset_image hsub) (fun u => probGnm n m (toN u)) (fun u => H n m u / Z)
    (fun x _ => by unfold probGnm; exact prob_nonneg _ _)
    (fun x _ => div_nonneg (hHnn x) hZpos.le) hP1 hP'1 hpos
    (6 / n ^ 2) δ (by positivity) hε₀ (by positivity) hW hW' Adj hedge _ hdiam (toZ d) hdW
  simp only [hHZ, toN_toZ] at key
  -- conclusion
  have hPd : 0 < probGnm n m d := by
    have := (hpos (toZ d) hdW).1; rwa [toN_toZ] at this
  have hHd : 0 < probBinom n m d * expFactor d := mul_pos (probBinom_pos hdΩ hmn) (exp_pos _)
  set η := (⌊(n : ℝ) * D ^ α⌋₊ : ℝ) * δ + 2 * (6 / (n : ℝ) ^ 2) + 2 * (|C₃| * xi n) with hη
  have hlogPH : |log (probGnm n m d / (probBinom n m d * expFactor d))| ≤ η := by
    have hk : log (probBinom n m d * expFactor d / Z / probGnm n m d) =
        -log (probGnm n m d / (probBinom n m d * expFactor d)) - log Z := by
      rw [log_div (div_pos hHd hZpos).ne' hPd.ne', log_div hHd.ne' hZpos.ne',
        log_div hPd.ne' hHd.ne']
      ring
    rw [hk] at key
    have := abs_sub_abs_le_abs_sub (-log (probGnm n m d / (probBinom n m d * expFactor d))) (log Z)
    rw [abs_neg] at this
    rw [hη]; linarith
  have hrδ : (⌊(n : ℝ) * D ^ α⌋₊ : ℝ) * δ ≤ K * D ^ (5 * α - 3) := by
    have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
    calc (⌊(n : ℝ) * D ^ α⌋₊ : ℝ) * δ ≤ n * D ^ α * δ :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hδ0
      _ = 4 * |C₁| * (D ^ α * D ^ (4 * α - 3)) + 2 * |C₂| * (D ^ α / n) := by
          rw [hδ]; field_simp; ring
      _ ≤ 4 * |C₁| * D ^ (5 * α - 3) + 2 * |C₂| * D ^ (5 * α - 3) := by
          rw [hDα]
          gcongr
          rw [div_le_iff₀ (by linarith)]; linarith
      _ = K * D ^ (5 * α - 3) := by rw [hK]; ring
  have hη1 : η ≤ 1 := by
    have : 6 / (n : ℝ) ^ 2 ≤ 6 / 64 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by nlinarith)
    rw [hη]; linarith
  have hηe : η ≤ (K + 12 + 2 * |C₃|) * err14 α n D := by
    have hD53' : 0 ≤ D ^ (5 * α - 3) := rpow_nonneg hD0.le _
    have : err14 α n D = xi n + D ^ (5 * α - 3) := rfl
    have e : (K + 12 + 2 * |C₃|) * (xi n + D ^ (5 * α - 3)) =
        K * D ^ (5 * α - 3) + 12 * xi n + 2 * |C₃| * xi n +
          (K * xi n + 12 * D ^ (5 * α - 3) + 2 * |C₃| * D ^ (5 * α - 3)) := by ring
    have h6 : 6 / (n : ℝ) ^ 2 = 6 * (1 / n ^ 2) := by ring
    rw [this, hη, e, h6]
    linarith [mul_nonneg hK0 hxi0, mul_nonneg (abs_nonneg C₃) hD53']
  refine ⟨probGnm n m d / (probBinom n m d * expFactor d) - 1, ?_,
    by rw [add_sub_cancel, mul_div_cancel₀ _ hHd.ne']⟩
  have hθ := abs_exp_sub_one_le (hlogPH.trans hη1)
  rw [exp_log (div_pos hPd hHd)] at hθ
  calc _ ≤ 2 * |log (probGnm n m d / (probBinom n m d * expFactor d))| := hθ
    _ ≤ 2 * ((K + 12 + 2 * |C₃|) * err14 α n D) := by gcongr; exact hlogPH.trans hηe
    _ = _ := by ring

#print axioms theorem_1_4

end LW
