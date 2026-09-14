import MajorityDynamics.Literature.LWFormal.Bip.Walk

set_option autoImplicit true

/-!
# Theorem 1.1 (bipartite case): final assembly

Lemma 2.1 with `P' = P_{𝒟(𝒢(ℓ,n,m))}`, ideal weight `h = P_ℬ H̃` on `𝔇`, edge estimates (30) + (35)
on both sides, the two-phase walk, `E_{ℬ_m}(1_W H̃) = 1 + O(1/√ℓ + 1/√n)`, and the conversion of
the logarithmic error into `1 + θ`.
-/

namespace LW.Bip

open Finset Real Filter

variable {ℓ n : ℕ}

theorem N_swap (d : BSeq ℓ n) : N d.swap = N d := by
  unfold N
  exact (card_equiv tr fun E => by
    simp only [mem_graphs, HasDeg, ldeg_tr, rdeg_tr, Prod.fst_swap, Prod.snd_swap]
    exact and_comm).symm

theorem probG_eq_N {m : ℕ} {s : Fin ℓ → ℕ} {t : Fin n → ℕ} (hs : ∑ a, s a = m) :
    probG ℓ n m s t = N (toSeq s t) / (Gm ℓ n m).card := by
  have key : (Gm ℓ n m).filter (fun E => ldeg E = s ∧ rdeg E = t) = graphs (toSeq s t) := by
    ext E
    simp only [mem_filter, mem_Gm, graphs, mem_univ, true_and, HasDeg, toSeq, Nat.cast_inj]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨fun a => congrFun h1 a, fun v => congrFun h2 v⟩
    · rintro ⟨h1, h2⟩
      have h1' : ldeg E = s := funext h1
      exact ⟨by rw [← sum_ldeg, h1', hs], h1', funext h2⟩
  unfold probG prob N
  rw [key]

/-- Edge estimate for `S`-steps: `|log(𝒩(x)/𝒩(y)) - log(H(x)/H(y))| ≤ 2 C' errS`. -/
theorem edgeS {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {C₁ B₀ C' : ℝ}
    (h30 : ∀ {ℓ n m : ℕ} {K B : ℝ}, Sizes ℓ n m K B → B₀ ≤ B →
      ∀ d ∈ Q1D φ ℓ n m, ∀ a b, Close (R a b d) (Rst a b d) (C₁ * err41 φ d))
    (hB : B₀ ≤ B) (hC : |C₁| ≤ C') (hC1 : 1 ≤ C') (hE : 5000 * C' * E3 φ ℓ n m ≤ 1 / 2)
    {x y : BSeq ℓ n} (hx : x ∈ Dset φ ℓ n m) (hy : y ∈ Dset φ ℓ n m) (hxy : AdjS x y) :
    |log ((N x : ℝ) / N y) - log (HB ℓ n m x / HB ℓ n m y)| ≤ 2 * C' * errS φ ℓ n m := by
  obtain ⟨d, a, b, rfl, rfl⟩ := hxy
  have hQ : d ∈ Q1D φ ℓ n m := ⟨a, hx⟩
  have hNa := Dset_realizable φ hφ₁ hφ₂ hS _ hx
  have hNb := Dset_realizable φ hφ₁ hφ₂ hS _ hy
  have hR : 0 < R a b d := div_pos (by exact_mod_cast hNa) (by exact_mod_cast hNb)
  have h41 : 0 ≤ err41 φ d := by
    obtain ⟨hM1, hM2, -⟩ := Q1D_facts (by linarith) hS hQ
    unfold err41 mu dmin dbar
    rw [hM1, hM2]; push_cast
    exact mul_nonneg (by positivity) (rpow_nonneg (le_min (by positivity) (by positivity)) _)
  have hSE := errS_le hφ₁ hφ₂ hS
  have hA0 := errA_nonneg φ ℓ n m
  have hH0 := errH_nonneg φ ℓ n m
  have hE3 := E3_nonneg φ ℓ n m
  have hS' : C' * errS φ ℓ n m ≤ 1 / 2 :=
    calc C' * errS φ ℓ n m ≤ C' * (5000 * E3 φ ℓ n m) :=
          mul_le_mul_of_nonneg_left hSE (by linarith)
      _ ≤ 1 / 2 := by linarith
  have hA : C' * errA φ ℓ n m ≤ 1 / 2 := by
    have : C' * errA φ ℓ n m ≤ C' * errS φ ℓ n m :=
      mul_le_mul_of_nonneg_left (by unfold errS; linarith) (by linarith)
    linarith
  have hH : errH φ ℓ n m ≤ 1 / 2 := by
    have : errH φ ℓ n m ≤ C' * errS φ ℓ n m := by
      unfold errS; nlinarith
    linarith
  have hxC : Close (R a b d) (Rst a b d) (C' * errA φ ℓ n m) :=
    (h30 hS hB d hQ a b).mono
      (calc C₁ * err41 φ d ≤ |C₁| * err41 φ d := mul_le_mul_of_nonneg_right (le_abs_self _) h41
        _ ≤ C' * errA φ ℓ n m :=
          mul_le_mul hC (err41_le_errA (by linarith) hS hQ) h41 (by linarith))
  have hyC := hratio_S hφ₁ hφ₂ hS hQ a b
  have hz : 0 < Rst a b d := hxC.pos_of_pos hR (by linarith)
  have := abs_log_sub_log_le hxC hyC hz (by nlinarith) hA hH0 hH
  show |log (R a b d) - log (HB ℓ n m (d - eS a) / HB ℓ n m (d - eS b))| ≤ _
  refine this.trans ?_
  unfold errS; nlinarith

/-- Edge estimate for `T`-steps, by transposition. -/
theorem edgeT {φ : ℝ} (hφ₁ : 1 / 2 < φ) (hφ₂ : φ < 3 / 5) {m : ℕ} {K B : ℝ} (hS : Sizes ℓ n m K B)
    {C₁ B₀ C' : ℝ}
    (h30 : ∀ {ℓ n m : ℕ} {K B : ℝ}, Sizes ℓ n m K B → B₀ ≤ B →
      ∀ d ∈ Q1D φ ℓ n m, ∀ a b, Close (R a b d) (Rst a b d) (C₁ * err41 φ d))
    (hB : B₀ ≤ B) (hC : |C₁| ≤ C') (hC1 : 1 ≤ C') (hE : 5000 * C' * E3 φ ℓ n m ≤ 1 / 2)
    {x y : BSeq ℓ n} (hx : x ∈ Dset φ ℓ n m) (hy : y ∈ Dset φ ℓ n m) (hxy : AdjT x y) :
    |log ((N x : ℝ) / N y) - log (HB ℓ n m x / HB ℓ n m y)| ≤ 2 * C' * errS φ n ℓ m := by
  obtain ⟨d, a, b, rfl, rfl⟩ := hxy
  have hadj : AdjS (d - eT a).swap (d - eT b).swap :=
    ⟨d.swap, a, b, swap_sub_eT d a, swap_sub_eT d b⟩
  have := edgeS hφ₁ hφ₂ hS.swap h30 hB hC hC1 (by rwa [E3_swap]) (Dset_swap.2 hx) (Dset_swap.2 hy)
    hadj
  rwa [N_swap, N_swap, HB_swap, HB_swap] at this

set_option maxHeartbeats 1000000 in
theorem theorem_1_1 : Theorem11 := by
  unfold Theorem11
  refine ⟨1 / (2 * 10 ^ 9), by norm_num, fun φ hφ₁ hφ₂ ω hω => ?_⟩
  obtain ⟨C₁, B₀, h30⟩ := eq_30 φ hφ₁ hφ₂
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = |C₁| + 1 := ⟨_, rfl⟩
  have hC : |C₁| ≤ C' := by rw [hC']; linarith
  have hC1 : 1 ≤ C' := by rw [hC']; linarith [abs_nonneg C₁]
  obtain ⟨N₁, hN₁⟩ := sizes_of_range φ hφ₁ hφ₂ hω (K := max 4 (2 / (2 * φ - 1)))
    (B := max 35000 B₀) (le_max_left _ _) (le_max_left _ _)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((eventually_ge_atTop N₁).and (hω.eventually (eventually_ge_atTop (40000 * C'))))
  refine ⟨2 * (20000 * C' + 110), N₀, fun n hn ℓ m hR1 hR2 hR3 s t hd => ?_⟩
  obtain ⟨hnN₁, hωn⟩ := hN₀ n hn
  have hR : Range φ ω (1 / (2 * 10 ^ 9)) ℓ n m := ⟨hR1, hR2, hR3⟩
  have hS := hN₁ n hnN₁ ℓ m hR
  have hB : B₀ ≤ max 35000 B₀ := le_max_right _ _
  have hK : 2 / (2 * φ - 1) ≤ max 4 (2 / (2 * φ - 1)) := le_max_right _ _
  have hφ0 : 0 ≤ φ := by linarith
  have hφ1 : φ ≤ 1 := by linarith
  obtain ⟨hℓ, hn', hm, -, -, -, -, -, -, hlogn⟩ := hS.bounds
  have hB35 := hS.B_ge
  have hB2 : (35000 : ℝ) ^ 2 ≤ (max 35000 B₀) ^ 2 := pow_le_pow_left₀ (by norm_num) hB35 2
  have hℓ8 : (4 * 10 ^ 8 : ℝ) ≤ ℓ := by
    have := natCast_ge_of_log (by linarith) hS.logℓ; norm_num at hB2; linarith
  have hn8 : (4 * 10 ^ 8 : ℝ) ≤ n := by
    have := natCast_ge_of_log (by linarith) hS.logn; norm_num at hB2; linarith
  have hsℓ : (20000 : ℝ) ≤ √ℓ := (le_sqrt' (by norm_num)).2 (by linarith)
  have hsn : (20000 : ℝ) ≤ √n := (le_sqrt' (by norm_num)).2 (by linarith)
  have hiℓ : 1 / √ℓ ≤ 1 / 20000 := one_div_le_one_div_of_le (by norm_num) hsℓ
  have hin : 1 / √n ≤ 1 / 20000 := one_div_le_one_div_of_le (by norm_num) hsn
  have hiℓ0 : 0 ≤ 1 / √ℓ := by positivity
  have hin0 : 0 ≤ 1 / √n := by positivity
  have hlogℓ : 1 ≤ log ℓ := by linarith [hS.logℓ]
  have hlogn1 : 1 ≤ log n := by linarith
  -- the error term `E3`
  have hω0 : 0 < ω n := by linarith
  have hE3 : E3 φ ℓ n m ≤ 1 / ω n := E3_le_inv_omega hφ₂ hR hω0 (by linarith) (by linarith) hm
  have hE30 := E3_nonneg φ ℓ n m
  have hE3' : 40000 * C' * E3 φ ℓ n m ≤ 1 :=
    calc 40000 * C' * E3 φ ℓ n m ≤ ω n * (1 / ω n) := mul_le_mul hωn hE3 hE30 hω0.le
      _ = 1 := by field_simp
  have hE3half : 5000 * C' * E3 φ ℓ n m ≤ 1 / 2 := by linarith
  -- the spaces
  have hmℓn : m ≤ ℓ * n := by have := hS.two_mul_le; omega
  have hGm : (0 : ℝ) < (Gm ℓ n m).card := by exact_mod_cast card_pos.2 (Gm_nonempty hmℓn)
  have hP'N : ∀ u ∈ DsetZ φ ℓ n m,
      probG ℓ n m (toN u.1) (toN u.2) = N u / (Gm ℓ n m).card := fun u hu => by
    have hu' := (mem_DsetZ hφ1 hS).1 hu
    have e := toSeq'_toN hu'.1 hu'.2.1
    simp only [toSeq'] at e
    rw [probG_eq_N (InD_toN hu').1, e]
  have hDsub : DsetZ φ ℓ n m ⊆ OmegaZ ℓ n m := DsetZ_subset_OmegaZ
  have hWD : WsetZ φ ℓ n m ⊆ DsetZ φ ℓ n m := WsetZ_subset_DsetZ
  have hP'0 : ∀ x ∈ OmegaZ ℓ n m, 0 ≤ probG ℓ n m (toN x.1) (toN x.2) := fun x _ => by
    unfold probG; exact prob_nonneg _ _
  have hP'1 : ∑ x ∈ OmegaZ ℓ n m, probG ℓ n m (toN x.1) (toN x.2) = 1 := by
    unfold OmegaZ
    rw [sum_image fun x _ y _ hxy => toSeq'_injective hxy]
    simp only [toSeq', toN_toSeq_fst, toN_toSeq_snd]
    exact sum_probG hmℓn
  have hpos : ∀ v ∈ DsetZ φ ℓ n m, 0 < HB ℓ n m v ∧ 0 < probG ℓ n m (toN v.1) (toN v.2) :=
    fun v hv => by
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hv
      refine ⟨?_, ?_⟩
      · rw [HB_toSeq']
        exact mul_pos (probB_pos hmℓn (DsetB_subset_OmegaB hx)) (exp_pos _)
      · rw [hP'N _ hv]
        have := Dset_realizable φ hφ₁ hφ₂ hS _ ((mem_DsetZ hφ1 hS).1 hv)
        exact div_pos (by exact_mod_cast this) hGm
  -- `P_𝒢(W) ≥ 1 - ε₀`
  have hε₀0 : 0 ≤ 5 / √ℓ + 5 / √n := by positivity
  have hε₀half : 5 / √ℓ + 5 / √n ≤ 1 / 2 := by
    have : 5 / √ℓ = 5 * (1 / √ℓ) := by ring
    have : 5 / √n = 5 * (1 / √n) := by ring
    linarith
  have hW' : 1 - (5 / √ℓ + 5 / √n) ≤ ∑ v ∈ WsetZ φ ℓ n m, probG ℓ n m (toN v.1) (toN v.2) := by
    unfold WsetZ
    rw [sum_image fun x _ y _ hxy => toSeq'_injective hxy]
    simp only [toSeq', toN_toSeq_fst, toN_toSeq_snd]
    exact probG_W_ge hφ₁ hφ1 hS hK
  -- edge estimates and the walk bound
  have hδ₁0 : 0 ≤ 2 * C' * errS φ ℓ n m := mul_nonneg (by linarith) (errS_nonneg _ _ _ _)
  have hδ₂0 : 0 ≤ 2 * C' * errS φ n ℓ m := mul_nonneg (by linarith) (errS_nonneg _ _ _ _)
  have hwalk : ∀ g : BSeq ℓ n → ℝ,
      (∀ x ∈ DsetZ φ ℓ n m, ∀ y ∈ DsetZ φ ℓ n m, g x - g y =
        log (probG ℓ n m (toN x.1) (toN x.2) / probG ℓ n m (toN y.1) (toN y.2)) -
          log (HB ℓ n m x / HB ℓ n m y)) →
      ∀ u ∈ DsetZ φ ℓ n m, ∀ v ∈ WsetZ φ ℓ n m,
        |g u - g v| ≤ (⌊(ℓ * (m / ℓ : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ ℓ n m) +
          (⌊(n * (m / n : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ n ℓ m) := fun g hg u hu v hv => by
    refine two_type_walk_bound (two_phase hφ0 hφ1 hS hu (hWD hv)) g hδ₁0 hδ₂0 ?_ ?_
    · intro x hx y hy hxy
      rw [hg x hx y hy, hP'N x hx, hP'N y hy, div_div_div_cancel_right₀ hGm.ne']
      exact edgeS hφ₁ hφ₂ hS h30 hB hC hC1 hE3half ((mem_DsetZ hφ1 hS).1 hx)
        ((mem_DsetZ hφ1 hS).1 hy) hxy
    · intro x hx y hy hxy
      rw [hg x hx y hy, hP'N x hx, hP'N y hy, div_div_div_cancel_right₀ hGm.ne']
      exact edgeT hφ₁ hφ₂ hS h30 hB hC hC1 hE3half ((mem_DsetZ hφ1 hS).1 hx)
        ((mem_DsetZ hφ1 hS).1 hy) hxy
  -- Lemma 2.1
  have hv₀ : toSeq' (s, t) ∈ DsetZ φ ℓ n m :=
    mem_image_of_mem _ ((mem_DsetB_iff hφ1 hS).2 hd)
  have key := lemma_2_1_h (OmegaZ ℓ n m) (WsetZ φ ℓ n m) (DsetZ φ ℓ n m) hWD hDsub (HB ℓ n m)
    (fun u => probG ℓ n m (toN u.1) (toN u.2)) hP'0 hP'1 hpos _ _ hε₀0 hε₀half hW' hwalk _ hv₀
  have hPv : probG ℓ n m (toN (toSeq' (s, t)).1) (toN (toSeq' (s, t)).2) = probG ℓ n m s t := by
    simp only [toSeq', toN_toSeq_fst, toN_toSeq_snd]
  have hhv : HB ℓ n m (toSeq' (s, t)) = probB ℓ n m s t * Htilde s t := HB_toSeq' m (s, t)
  have hZ : ∑ x ∈ WsetZ φ ℓ n m, HB ℓ n m x =
      ∑ x ∈ WsetB φ ℓ n m, probB ℓ n m x.1 x.2 * Htilde x.1 x.2 := by
    unfold WsetZ
    rw [sum_image fun x _ y _ hxy => toSeq'_injective hxy]
    exact sum_congr rfl fun x _ => HB_toSeq' m x
  simp only [hPv, hhv] at key
  -- `log Z = O(1/√ℓ + 1/√n)`
  have hζ0 : 0 ≤ 50 * (1 / √ℓ + 1 / √n) := by positivity
  have hζhalf : 50 * (1 / √ℓ + 1 / √n) ≤ 1 / 2 := by linarith
  have hlogZ : |log (∑ x ∈ WsetZ φ ℓ n m, HB ℓ n m x)| ≤ 2 * (50 * (1 / √ℓ + 1 / √n)) := by
    have hc : Close (∑ x ∈ WsetZ φ ℓ n m, HB ℓ n m x) 1 (50 * (1 / √ℓ + 1 / √n)) := by
      unfold Close; rw [abs_one, mul_one, hZ]; exact expect_W hφ₁ hφ1 hS hK
    have := (hc.logClose one_pos hζ0 hζhalf).2.2
    rwa [div_one] at this
  -- collect the error
  have hPd : 0 < probG ℓ n m s t := by have := (hpos _ hv₀).2; rwa [hPv] at this
  have hHd : 0 < probB ℓ n m s t * Htilde s t := by have := (hpos _ hv₀).1; rwa [hhv] at this
  have hlogPH : |log (probG ℓ n m s t / (probB ℓ n m s t * Htilde s t))| ≤
      (⌊(ℓ * (m / ℓ : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ ℓ n m) +
        (⌊(n * (m / n : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ n ℓ m) +
        2 * (5 / √ℓ + 5 / √n) + 2 * (50 * (1 / √ℓ + 1 / √n)) := by
    have := abs_add_le (log (probG ℓ n m s t / (probB ℓ n m s t * Htilde s t)) +
      log (∑ x ∈ WsetZ φ ℓ n m, HB ℓ n m x)) (-log (∑ x ∈ WsetZ φ ℓ n m, HB ℓ n m x))
    rw [abs_neg, add_neg_cancel_right] at this
    linarith
  have hρ₁ : (⌊(ℓ * (m / ℓ : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ ℓ n m) ≤
      10000 * C' * E3 φ ℓ n m := by
    have hr : (⌊(ℓ * (m / ℓ : ℝ) ^ φ)⌋₊ : ℝ) ≤ ℓ * (m / ℓ : ℝ) ^ φ := Nat.floor_le (by positivity)
    have hw := walk_errS hφ₁ hφ₂ hS
    calc (⌊(ℓ * (m / ℓ : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ ℓ n m)
        = 2 * C' * ((⌊(ℓ * (m / ℓ : ℝ) ^ φ)⌋₊ : ℝ) * errS φ ℓ n m) := by ring
      _ ≤ 2 * C' * (ℓ * (m / ℓ : ℝ) ^ φ * errS φ ℓ n m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr (errS_nonneg _ _ _ _))
            (by linarith)
      _ ≤ 2 * C' * (5000 * E3 φ ℓ n m) := mul_le_mul_of_nonneg_left hw (by linarith)
      _ = 10000 * C' * E3 φ ℓ n m := by ring
  have hρ₂ : (⌊(n * (m / n : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ n ℓ m) ≤
      10000 * C' * E3 φ ℓ n m := by
    have hr : (⌊(n * (m / n : ℝ) ^ φ)⌋₊ : ℝ) ≤ n * (m / n : ℝ) ^ φ := Nat.floor_le (by positivity)
    have hw := walk_errS hφ₁ hφ₂ hS.swap
    rw [E3_swap] at hw
    calc (⌊(n * (m / n : ℝ) ^ φ)⌋₊ : ℝ) * (2 * C' * errS φ n ℓ m)
        = 2 * C' * ((⌊(n * (m / n : ℝ) ^ φ)⌋₊ : ℝ) * errS φ n ℓ m) := by ring
      _ ≤ 2 * C' * (n * (m / n : ℝ) ^ φ * errS φ n ℓ m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr (errS_nonneg _ _ _ _))
            (by linarith)
      _ ≤ 2 * C' * (5000 * E3 φ ℓ n m) := mul_le_mul_of_nonneg_left hw (by linarith)
      _ = 10000 * C' * E3 φ ℓ n m := by ring
  have hη : |log (probG ℓ n m s t / (probB ℓ n m s t * Htilde s t))| ≤
      20000 * C' * E3 φ ℓ n m + 110 * (1 / √ℓ + 1 / √n) := by
    have : 5 / √ℓ = 5 * (1 / √ℓ) := by ring
    have : 5 / √n = 5 * (1 / √n) := by ring
    linarith
  have hη1 : 20000 * C' * E3 φ ℓ n m + 110 * (1 / √ℓ + 1 / √n) ≤ 1 := by linarith
  have herr : 20000 * C' * E3 φ ℓ n m + 110 * (1 / √ℓ + 1 / √n) ≤
      (20000 * C' + 110) * err11 φ ℓ n m := by
    show _ ≤ (20000 * C' + 110) * (log ℓ ^ 2 / √ℓ + log n ^ 2 / √n + E3 φ ℓ n m)
    have h1 : 1 / √ℓ ≤ log ℓ ^ 2 / √ℓ :=
      div_le_div_of_nonneg_right (by nlinarith) (sqrt_nonneg _)
    have h2 : 1 / √n ≤ log n ^ 2 / √n :=
      div_le_div_of_nonneg_right (by nlinarith) (sqrt_nonneg _)
    have hA0 : 0 ≤ log ℓ ^ 2 / √ℓ := by positivity
    have hB0 : 0 ≤ log n ^ 2 / √n := by positivity
    have hC0 : 0 ≤ C' := by linarith
    nlinarith [mul_nonneg hC0 hA0, mul_nonneg hC0 hB0, mul_nonneg hC0 hE30]
  -- conclusion
  refine ⟨probG ℓ n m s t / (probB ℓ n m s t * Htilde s t) - 1, ?_,
    by rw [add_sub_cancel, mul_div_cancel₀ _ hHd.ne']⟩
  have hθ := abs_exp_sub_one_le (hη.trans hη1)
  rw [exp_log (div_pos hPd hHd)] at hθ
  calc _ ≤ 2 * |log (probG ℓ n m s t / (probB ℓ n m s t * Htilde s t))| := hθ
    _ ≤ 2 * ((20000 * C' + 110) * err11 φ ℓ n m) :=
        mul_le_mul_of_nonneg_left (hη.trans herr) (by norm_num)
    _ = _ := by ring

#print axioms theorem_1_1

end LW.Bip
